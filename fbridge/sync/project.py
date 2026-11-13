from __future__ import annotations

from dataclasses import dataclass

import z3

from ..ir.ast import Binary, Const, Expr, Rule, Schema, Var, free_vars, is_temporal, substitute, temporal_span
from ..ir.simplify import simplify
from ..ir.smt import Encoder
from ..mapping import Mapping, View


def _span(r: Rule) -> tuple[int, int]:
    lo, hi = temporal_span(r.body())
    if r.disable is not None:
        dlo, dhi = temporal_span(r.disable)
        lo, hi = min(lo, dlo), max(hi, dhi)
    return lo, hi


@dataclass
class Projection:
    phi: z3.BoolRef
    free_signals: list[z3.ExprRef]
    item_vars: dict[str, z3.BitVecRef]


class ViewProjector:
    def __init__(self, item_schema: Schema, sig_schema: Schema, view: View, mapping: Mapping):
        self.item_schema = item_schema
        self.sig_schema = sig_schema
        self.view = view
        self.mapping = mapping
        self.item = Encoder(item_schema)
        self.direct = {e.name: f for f, e in view.fields.items() if isinstance(e, Var)}
        self.complex = {f: e for f, e in view.fields.items() if not isinstance(e, Var)}

    def mapped_fields(self) -> set[str]:
        return set(self.view.fields)

    def project(self, assumes: list[Rule], tag: str = "") -> Projection:
        k = max([hi - lo for lo, hi in (_span(r) for r in assumes)] + [0])
        t0 = k
        horizon = 2 * k
        item = self.item

        def resolver(name: str, t: int):
            if t == t0 and name in self.direct:
                f = self.direct[name]
                fw = self.item_schema.fields[f]
                return item.var(f), fw.width, fw.signed
            return None

        sig = Encoder(self.sig_schema, prefix=f"sig{tag}.", resolver=resolver)
        parts = [sig.bool(self.view.sample, t0)]
        for f, e in self.complex.items():
            fw = self.item_schema.fields[f].width
            se = sig.bv(e, t0)
            w = max(fw, se.size())
            parts.append(z3.ZeroExt(w - se.size(), se) == z3.ZeroExt(w - fw, item.var(f)))
        if self.mapping.disable is not None:
            for t in range(horizon + 1):
                parts.append(z3.Not(sig.bool(self.mapping.disable, t)))
        for r in assumes:
            lo, hi = _span(r)
            for t in range(-lo, horizon - hi + 1):
                parts.append(sig.rule(r, t))
        free = list(sig.backend.vars.values())
        return Projection(z3.And(*parts) if len(parts) > 1 else parts[0], free, {f: item.var(f) for f in self.view.fields})

    def syntactic(self, r: Rule) -> Expr | None:
        if is_temporal(r.body()):
            return None
        sample_true = {}
        stack = [self.view.sample]
        while stack:
            n = stack.pop()
            if isinstance(n, Binary) and n.op == "&&":
                stack += [n.a, n.b]
            elif isinstance(n, Var):
                sample_true[n.name] = Const(1, 1, False)
            else:
                return None
        env = {sname: Var(f) for sname, f in self.direct.items()}
        env.update(sample_true)
        merged = Schema({**self.sig_schema.fields, **self.item_schema.fields}, {**self.sig_schema.consts, **self.item_schema.consts})
        e = simplify(substitute(r.body(), env), merged)
        consts = set(self.item_schema.consts) | set(self.sig_schema.consts)
        if any(v not in self.item_schema.fields and v not in consts for v in free_vars(e)):
            return None
        return e
