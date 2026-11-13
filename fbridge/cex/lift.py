from __future__ import annotations

import re
from dataclasses import dataclass, field
from pathlib import Path

import z3

from ..eco.cones import Design, load_design
from ..frontends.slang_util import collect_params
from ..frontends.svparse import ParseError, lower_spec, parse_expr, parse_property
from ..ir.ast import Binary, Const, Expr, Field, Func, Next, Past, Schema, Slice, Var, walk
from ..ir.evaluate import holds
from ..ir.semantics import SemanticsError
from ..ir.smt import Encoder, unsat_core
from .monitor import MonitorDef, Transaction, assemble
from .vcd import Waveform

IDENT = re.compile(r"\b[A-Za-z_][A-Za-z0-9_]*\b")


@dataclass
class FieldLift:
    name: str
    value: object
    mask: int
    width: int

    @property
    def essential(self) -> bool:
        return self.mask != 0


@dataclass
class LiftedTxn:
    txn: Transaction
    essential: bool
    fields: dict[str, FieldLift]
    timing_relevant: bool
    idle_before: int = 0
    disabled_constraints: list[str] = field(default_factory=list)
    legal: bool | None = None


@dataclass
class LiftResult:
    property_text: str
    fail_cycle: int
    fail_end: int
    cycles: int
    transactions: list[LiftedTxn]
    relevant_inputs: dict[str, dict[int, int]]
    warnings: list[str] = field(default_factory=list)
    item_class: str = ""

    def kept(self) -> list[LiftedTxn]:
        return [t for t in self.transactions if t.essential]


class TraceView:
    def __init__(self, wf: Waveform, top: str, clock: str):
        self.wf = wf
        self.top = top
        names = [n for n in wf.vars if n.startswith(top + ".") and n.count(".") == top.count(".") + 1]
        self.short = {n.split(".")[-1]: n for n in names}
        self.cycles = wf.sample(list(self.short.values()), clock=self.short.get(clock, clock))
        self.cycles = [{k.split(".")[-1]: v for k, v in c.items()} for c in self.cycles]
        self.widths = {k: wf.vars[n].width for k, n in self.short.items()}


def _schema(widths: dict[str, int], consts: dict[str, int]) -> Schema:
    s = Schema()
    for n, w in widths.items():
        s.add(Field(n, w))
    for k, v in consts.items():
        if k not in s.fields:
            s.consts[k] = Const(v, 32, True)
    return s


def _offset_refs(e: Expr, off: int = 0, out: set | None = None) -> set[tuple[str, int]]:
    out = set() if out is None else out
    if isinstance(e, Var):
        out.add((e.name, off))
        return out
    if isinstance(e, Past):
        return _offset_refs(e.a, off - e.n, out)
    if isinstance(e, Next):
        return _offset_refs(e.a, off + e.n, out)
    if isinstance(e, Func) and e.name in ("$stable", "$rose", "$fell", "$changed"):
        for a in e.args:
            _offset_refs(a, off - 1, out)
    for c in e.children():
        _offset_refs(c, off, out)
    return out


def ref_masks(e: Expr, widths: dict[str, int], consts: dict[str, int]) -> dict[str, int]:
    out: dict[str, int] = {}

    def full(n: str) -> int:
        return (1 << widths.get(n, 64)) - 1

    def go(n: Expr):
        if isinstance(n, Slice) and isinstance(n.a, Var):
            m = ((1 << (n.hi - n.lo + 1)) - 1) << n.lo
            out[n.a.name] = out.get(n.a.name, 0) | (m & full(n.a.name))
            return
        if isinstance(n, Binary) and n.op == ">>" and isinstance(n.a, Var):
            out[n.a.name] = out.get(n.a.name, 0) | full(n.a.name)
        if isinstance(n, Var):
            if n.name not in consts:
                out[n.name] = out.get(n.name, 0) | full(n.name)
            return
        for c in n.children():
            go(c)
    go(e)
    return out


class Slicer:
    def __init__(self, design: Design, trace: TraceView, consts: dict[str, int], top: str, mode: str = "data",
                 barrier: set[str] | None = None):
        self.d = design
        self.tr = trace
        self.consts = consts
        self.top = top
        self.mode = mode
        self.barrier = barrier or set()
        self.schema = _schema(trace.widths, consts)
        self.ports = design.modules.get(top, {}).get("ports", {})
        self._parsed: dict[str, Expr | None] = {}
        self.relevant: dict[str, dict[int, int]] = {}

    def parsed(self, text: str) -> Expr | None:
        if text not in self._parsed:
            try:
                self._parsed[text] = parse_expr(text, self.consts)
            except (ParseError, Exception):
                self._parsed[text] = None
        return self._parsed[text]

    def masks_of(self, text: str) -> dict[str, int]:
        e = self.parsed(text)
        if e is None:
            return {n: (1 << self.tr.widths.get(n, 64)) - 1 for n in IDENT.findall(text) if n in self.tr.widths}
        return {n: m for n, m in ref_masks(e, self.tr.widths, self.consts).items() if n in self.tr.widths or f"{self.top}.{n}" in self.d.drivers}

    def cond_value(self, text: str, t: int) -> bool | None:
        if text.startswith("?"):
            return None
        e = self.parsed(text)
        if e is None or not (0 <= t < len(self.tr.cycles)):
            return None
        try:
            return holds(e, self.schema, self.tr.cycles, t)
        except (SemanticsError, KeyError, Exception):
            return None

    def mark(self, name: str, t: int, mask: int, work: list) -> None:
        if t < 0 or t >= len(self.tr.cycles) or mask == 0:
            return
        per = self.relevant.setdefault(name, {})
        old = per.get(t, 0)
        if old | mask != old:
            per[t] = old | mask
            work.append((name, t))

    def run(self, seeds: list[tuple[str, int, int]]) -> dict[str, dict[int, int]]:
        work: list[tuple[str, int]] = []
        for n, t, m in seeds:
            self.mark(n, t, m, work)
        while work:
            name, t = work.pop()
            if name in self.barrier:
                continue
            drivers = self.d.drivers.get(f"{self.top}.{name}", [])
            if not drivers:
                continue
            ff = [d for d in drivers if d.kind == "ff"]
            comb = [d for d in drivers if d.kind != "ff"]
            for d in comb:
                self._apply(d, t, work)
            if ff:
                active = [d for d in ff if self._apply(d, t - 1, work)]
                if not any(not d.partial for d in active):
                    self.mark(name, t - 1, self.relevant[name][t], work)
        return self.relevant

    def _apply(self, d, t: int, work: list) -> bool:
        if t < 0:
            return False
        if self.mode == "data":
            if any(self.cond_value(c, t) is False for c in d.conds):
                return False
            for c in d.conds:
                for n, m in self.masks_of(c.lstrip("!")).items():
                    self.mark(n, t, m, work)
        else:
            for c in d.conds:
                for n, m in self.masks_of(c.lstrip("!")).items():
                    self.mark(n, t, m, work)
                if self.cond_value(c, t) is False:
                    return False
        if d.kind == "port":
            for dep in d.deps:
                mod, n = dep.split(".", 1)
                if mod == self.top:
                    self.mark(n, t, (1 << self.tr.widths.get(n, 64)) - 1, work)
            return True
        if d.rhs:
            masks = self.masks_of(d.rhs)
            for n, m in masks.items():
                self.mark(n, t, m, work)
            for dep in d.deps:
                mod, n = dep.split(".", 1)
                if mod == self.top and n not in masks and n not in self.consts and n in self.tr.widths and not self._is_cond_dep(d, n):
                    self.mark(n, t, (1 << self.tr.widths.get(n, 64)) - 1, work)
        else:
            for dep in d.deps:
                mod, n = dep.split(".", 1)
                if mod == self.top and n not in self.consts:
                    self.mark(n, t, (1 << self.tr.widths.get(n, 64)) - 1, work)
        return True

    @staticmethod
    def _is_cond_dep(d, n: str) -> bool:
        return any(c.endswith("." + n) for c in d.cond_deps)


def find_failure(prop_text: str, trace: TraceView, consts: dict[str, int]) -> tuple[int, int, Expr, Expr | None]:
    spec = parse_property(prop_text, consts)
    expr, disable = lower_spec(spec)
    sch = _schema(trace.widths, consts)
    refs = _offset_refs(expr)
    hi = max([o for _, o in refs] + [0])
    for t in range(len(trace.cycles) - hi):
        if disable is not None and holds(disable, sch, trace.cycles, t):
            continue
        if not holds(expr, sch, trace.cycles, t):
            return t, t + hi, expr, disable
    raise ValueError("property holds on every cycle of the trace; nothing to lift")


def lift(wf: Waveform, mon: MonitorDef, rtl: list[Path], top: str, prop_text: str, item_cset=None,
         kind_map: dict[str, str] | None = None, keep_timing: bool = False) -> LiftResult:
    design = load_design(rtl)
    consts: dict[str, int] = {}
    from ..frontends.slang_util import load_tree
    for p in rtl:
        collect_params(load_tree(p).root, consts)
    trace = TraceView(wf, top, mon.clock)
    t0, t1, expr, disable = find_failure(prop_text, trace, consts)
    seeds = []
    for name, off in _offset_refs(expr):
        if name in trace.widths:
            seeds.append((name, t0 + off, (1 << trace.widths[name]) - 1))
    if disable is not None:
        for name, off in _offset_refs(disable):
            if name in trace.widths:
                seeds.append((name, t0 + off, (1 << trace.widths[name]) - 1))
    responses = {t.response for t in mon.transactions.values() if t.response}
    barrier = set()
    for name, ch in mon.channels.items():
        if name in responses:
            barrier |= {ch.valid, *ch.fields.values()}
        elif ch.ready:
            barrier.add(ch.ready)
    core = Slicer(design, trace, consts, top, "data", barrier).run(seeds) if not keep_timing else None
    rel = Slicer(design, trace, consts, top, "data").run(seeds)
    pin = Slicer(design, trace, consts, top, "relevant").run(seeds)
    decide = rel if core is None else core
    txns = [t for t in assemble(mon, trace.cycles[: t1 + 1]) if t.issue_cycle <= t1]
    res = LiftResult(prop_text, t0, t1, len(trace.cycles), [], rel)
    reset_release = 0
    if mon.reset:
        for i, c in enumerate(trace.cycles):
            if c.get(mon.reset, 1 - mon.reset_active) != mon.reset_active:
                reset_release = i
                break
    prev_end = reset_release - 1
    for tx in txns:
        tt = mon.transactions[tx.kind]
        fields: dict[str, FieldLift] = {}
        primary = False
        for f, src in tt.item.items():
            if "." not in src:
                fields[f] = FieldLift(f, src, -1, 0)
                continue
            ch, fld = src.split(".", 1)
            sig = mon.channels[ch].fields[fld]
            mask = 0
            for b in tx.beats[ch]:
                primary |= bool(decide.get(sig, {}).get(b.cycle, 0))
                mask |= rel.get(sig, {}).get(b.cycle, 0) | pin.get(sig, {}).get(b.cycle, 0)
            fields[f] = FieldLift(f, tx.item[f], mask, trace.widths.get(sig, 32))
        timing = False
        for ch, beats in tx.beats.items():
            c = mon.channels[ch]
            for b in beats:
                for t in range(b.valid_cycle, b.cycle + 1):
                    primary |= bool(decide.get(c.valid, {}).get(t))
                    timing |= bool(rel.get(c.valid, {}).get(t) or (c.ready and rel.get(c.ready, {}).get(t)))
        lt = LiftedTxn(tx, primary, fields, timing)
        essential = lt.essential
        if essential:
            lt.idle_before = max(0, tx.issue_cycle - prev_end - 1)
            prev_end = tx.accept_cycle
        res.transactions.append(lt)
    if item_cset is not None:
        check_legality(res, item_cset, kind_map or {})
    return res


def resolve_enum(value: str, field: Field, kind_map: dict[str, str]) -> int:
    name = kind_map.get(value, value)
    members = dict(field.enum)
    if name in members:
        return members[name]
    hits = [m for m in members if m.lower() == name.lower() or m.lower().endswith("_" + name.lower())]
    if len(hits) == 1:
        return members[hits[0]]
    raise ValueError(f"cannot map '{value}' onto enum {sorted(members)} of field '{field.name}'; use --map {value}=<ENUM>")


def item_value(fl: FieldLift, schema: Schema, kind_map: dict[str, str]) -> int | None:
    if fl.mask == -1:
        f = schema.fields.get(fl.name)
        if f is None:
            return None
        return resolve_enum(str(fl.value), f, kind_map) if f.enum else int(str(fl.value), 0)
    return fl.value if isinstance(fl.value, int) else None


def check_legality(res: LiftResult, cset, kind_map: dict[str, str]) -> None:
    schema = cset.schema
    enc = Encoder(schema)
    named = {r.name: enc.bool(r.body()) for r in cset.hard()}
    for lt in res.kept():
        eqs = []
        for fl in lt.fields.values():
            if fl.name not in schema.fields:
                continue
            v = item_value(fl, schema, kind_map)
            if v is None:
                continue
            m = (1 << schema.fields[fl.name].width) - 1 if fl.mask == -1 else fl.mask
            eqs.append((enc.var(fl.name) & m) == (v & m))
        s = z3.Solver()
        s.add(*eqs, *named.values())
        if s.check() == z3.sat:
            lt.legal = True
            continue
        lt.legal = False
        core = unsat_core(named, eqs) or []
        blocks = sorted({c.split("[")[0] for c in core})
        lt.disabled_constraints = blocks
        res.warnings.append(f"transaction #{lt.txn.index} ({lt.txn.kind} @ cycle {lt.txn.issue_cycle}) needs stimulus outside UVM "
                            f"constraints {blocks}; formal environment is looser than the testbench")
