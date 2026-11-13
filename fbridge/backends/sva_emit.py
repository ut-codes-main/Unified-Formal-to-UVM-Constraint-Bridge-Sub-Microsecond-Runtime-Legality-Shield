from __future__ import annotations

from dataclasses import dataclass, field

import z3

from ..frontends.svparse import Prop, PropertySpec, Seq
from ..ir.ast import TRUE, Expr, Field, Schema, conj, free_vars, substitute
from ..ir.printer import to_sv
from ..ir.simplify import simplify
from ..ir.smt import Encoder
from ..mapping import Mapping, View, pinned_fields
from .uvm_emit import sv_ident


def _delay(d: tuple[int, int]) -> str:
    return f"##{d[0]}" if d[0] == d[1] else f"##[{d[0]}:{d[1]}]"


def _paren(s: str) -> str:
    return s if s.replace("_", "").isalnum() else f"({s})"


def seq_to_sv(s: Seq) -> str:
    parts = []
    for i, el in enumerate(s.elems):
        txt = to_sv(el.expr)
        if len(s.elems) > 1 or el.rep != (1, 1):
            txt = _paren(txt)
        if el.rep != (1, 1):
            txt += f"[*{el.rep[0]}]" if el.rep[0] == el.rep[1] else f"[*{el.rep[0]}:{el.rep[1]}]"
        if i == 0 and s.first_delay is not None:
            parts.append(f"{_delay(s.first_delay)} {txt}")
        elif i > 0:
            parts.append(f"{_delay(s.delays[i - 1])} {txt}")
        else:
            parts.append(txt)
    return " ".join(parts)


def prop_to_sv(p: Prop) -> str:
    if p.kind == "seq":
        return seq_to_sv(p.seq)
    if p.kind == "not":
        return f"not ({prop_to_sv(p.rhs)})"
    return f"{seq_to_sv(p.seq)} {p.op} {prop_to_sv(p.rhs)}"


def spec_to_sv(spec: PropertySpec, clock: str | None = None, disable: str | None = None) -> str:
    out = []
    if spec.clock is not None:
        out.append(f"@({spec.edge + ' ' if spec.edge else ''}{to_sv(spec.clock)})")
    elif clock:
        out.append(f"@(posedge {clock})")
    if spec.disable is not None:
        out.append(f"disable iff ({to_sv(spec.disable)})")
    elif disable:
        out.append(f"disable iff ({disable})")
    out.append(prop_to_sv(spec.prop))
    return " ".join(out)


@dataclass
class SvaEmission:
    text: str
    emitted: dict[str, list[str]] = field(default_factory=dict)
    skipped: list[str] = field(default_factory=list)
    warnings: list[str] = field(default_factory=list)


def vacuous_in_view(rule_expr: Expr, view: View, item_schema: Schema) -> bool:
    enc = Encoder(item_schema)
    s = z3.Solver()
    s.add(enc.bool(view.when), z3.Not(enc.bool(rule_expr)))
    return s.check() == z3.unsat


def specialize(rule_expr: Expr, view: View, item_schema: Schema) -> Expr:
    if vacuous_in_view(rule_expr, view, item_schema):
        return TRUE
    env = dict(view.fields)
    env.update(pinned_fields(view, item_schema))
    return simplify(substitute(rule_expr, env), Schema(dict(item_schema.fields), dict(item_schema.consts)))


def emit_assumes(item_cset, mapping: Mapping, protocols=(), directive: str = "assume", module: str | None = None) -> SvaEmission:
    item_schema = item_cset.schema
    sig = mapping.signal_schema(item_schema)
    mod = module or mapping.module or f"{sv_ident(item_cset.name)}_env_{directive}s"
    em = SvaEmission("")
    body = []
    prefix = {"assume": "as", "assert": "ap", "cover": "cv"}.get(directive, directive[:2])
    for r in item_cset.rules:
        if r.soft:
            em.skipped.append(f"{r.name}: soft constraint (simulation preference only)")
            continue
        names, unmapped = [], False
        for v in mapping.views:
            e = specialize(r.body(), v, item_schema)
            if e == TRUE:
                continue
            left = free_vars(e) - set(sig.fields) - set(item_schema.consts)
            if left:
                unmapped = True
                em.warnings.append(f"{r.name}: not expressible in view '{v.name}' (unmapped: {', '.join(sorted(left))})")
                continue
            label = f"{prefix}_{sv_ident(r.name)}__{v.name}"
            body.append(f"  // {r.origin.file}:{r.origin.line} {r.origin.text}".rstrip())
            body.append(f"  {label}: {directive} property ({_paren(to_sv(v.sample))} |-> {_paren(to_sv(e))});")
            names.append(label)
        if names:
            em.emitted[r.name] = names
        elif not unmapped:
            em.skipped.append(f"{r.name}: vacuous in every view")
    for p in protocols:
        label = f"{prefix}_{sv_ident(p.name)}"
        body.append(f"  // {p.rule.origin.file}:{p.rule.origin.line}")
        body.append(f"  {label}: {directive} property ({prop_to_sv(p.spec.prop)});")
        em.emitted[p.name] = [label]
        refs = conj([p.rule.expr] + ([p.rule.disable] if p.rule.disable is not None else []))
        for n in sorted(free_vars(refs)):
            if n not in sig.fields and n not in item_schema.consts:
                sig.add(Field(n, 1, False, "signal"))
    ports = []
    order = [mapping.clock] + sorted(free_vars(mapping.disable)) if mapping.disable is not None else [mapping.clock]
    fields_sorted = [sig.fields[n] for n in order if n in sig.fields] + [f for f in sig.fields.values() if f.name not in order]
    for f in fields_sorted:
        dim = f" [{f.width - 1}:0]" if f.width > 1 else ""
        ports.append(f"  input logic{dim} {f.name}")
    members = {n for f in item_schema.fields.values() for n, _ in f.enum}
    consts = [f"  localparam int unsigned {n} = 32'h{c.value:X};" for n, c in item_schema.consts.items() if n not in members]
    pre = [f"  default clocking cb @(posedge {mapping.clock}); endclocking"]
    if mapping.disable_text:
        pre.append(f"  default disable iff ({mapping.disable_text});")
    em.text = "\n".join([f"module {mod} (", ",\n".join(ports), ");"] + consts + pre + [""] + body + ["endmodule", ""])
    return em
