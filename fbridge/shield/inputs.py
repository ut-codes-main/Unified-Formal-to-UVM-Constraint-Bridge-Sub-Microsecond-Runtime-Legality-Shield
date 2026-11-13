from __future__ import annotations

from dataclasses import dataclass, field
from pathlib import Path

import yaml

from ..ir.ast import TRUE, Binary, Const, Expr, Field, Origin, Rule, Schema, free_vars, substitute
from ..frontends.svparse import parse_expr
from .formal_import import FormalFacts, load_facts


class SpecError(Exception):
    pass


@dataclass
class PackedField:
    name: str
    width: int
    lsb: int
    signed: bool = False
    enum: tuple[tuple[str, int], ...] = ()
    priority: int = 0

    @property
    def mask(self) -> int:
        return ((1 << self.width) - 1) << self.lsb


@dataclass
class Transition:
    name: str
    when: Expr
    next: dict[str, Expr]
    kind: str = "action"


@dataclass
class InvariantSource:
    facts: FormalFacts
    expr: Expr
    label: str


@dataclass
class ShieldSpec:
    name: str
    state: list[PackedField]
    action: list[PackedField]
    init: Expr = TRUE
    transitions: list[Transition] = field(default_factory=list)
    legal: list[Rule] = field(default_factory=list)
    invariants: list[InvariantSource] = field(default_factory=list)
    consts: dict[str, int] = field(default_factory=dict)
    reach_bound: int = 256
    warnings: list[str] = field(default_factory=list)
    base_dir: Path = field(default_factory=Path)

    @property
    def state_bits(self) -> int:
        return sum(f.width for f in self.state)

    @property
    def action_bits(self) -> int:
        return sum(f.width for f in self.action)

    def schema(self) -> Schema:
        s = Schema()
        for f in self.state:
            s.add(Field(f.name, f.width, f.signed, "state", f.enum))
        for f in self.action:
            s.add(Field(f.name, f.width, f.signed, "rand", f.enum))
        for k, v in self.consts.items():
            s.consts.setdefault(k, Const(v, 32, True))
        return s

    def field(self, name: str) -> PackedField:
        for f in self.state + self.action:
            if f.name == name:
                return f
        raise KeyError(name)

    def pack(self, values: dict[str, int], which: str) -> int:
        out = 0
        for f in (self.state if which == "state" else self.action):
            out |= (values.get(f.name, 0) & ((1 << f.width) - 1)) << f.lsb
        return out

    def unpack(self, word: int, which: str) -> dict[str, int]:
        return {f.name: (word >> f.lsb) & ((1 << f.width) - 1) for f in (self.state if which == "state" else self.action)}


def _fields(items, what: str) -> list[PackedField]:
    out, lsb = [], 0
    for i, d in enumerate(items or []):
        enum = tuple((str(k), int(v)) for k, v in (d.get("enum") or {}).items())
        width = int(d.get("width", max(1, (max([v for _, v in enum] + [0])).bit_length())))
        out.append(PackedField(d["name"], width, lsb, bool(d.get("signed", False)), enum, int(d.get("priority", i))))
        lsb += width
    if lsb > 64:
        raise SpecError(f"{what} vector is {lsb} bits; at most 64 bits can be packed")
    return out


def _expr(text, consts) -> Expr:
    if isinstance(text, bool):
        return TRUE if text else Const(0, 1, False)
    return parse_expr(str(text), consts)


def _load_rules_fbr(spec: ShieldSpec, d: dict, base: Path) -> None:
    from ..frontends.fbr_dsl import load_single_source
    src = load_single_source(base / d["file"], d.get("item"))
    names = {f.name for f in spec.action} | {f.name for f in spec.state}
    for r in src.cset.rules:
        if r.soft:
            continue
        missing = free_vars(r.body()) - names - set(src.cset.schema.consts) - set(spec.consts)
        if missing:
            spec.warnings.append(f"fbr rule '{r.name}' references unknown fields {sorted(missing)}; skipped")
            continue
        spec.legal.append(Rule(f"fbr:{r.name}", r.body(), "rule", False, r.origin))
    for k, c in src.cset.schema.consts.items():
        spec.consts.setdefault(k, c.value)


def _load_rules_sva(spec: ShieldSpec, d: dict, base: Path) -> None:
    from ..frontends.sva_assume import load_sva
    from ..mapping import load_mapping
    from ..sync.project import ViewProjector
    mapping = load_mapping(base / d["map"])
    files = d.get("files") or [d["file"]]
    sch = spec.schema()
    sva = load_sva([base / f for f in files], schema=mapping.signal_schema(sch))
    sig = mapping.signal_schema(sch).merged(sva.cset.schema)
    for v in mapping.views:
        pj = ViewProjector(sch, sig, v, mapping)
        for r in sva.cset.rules:
            e = pj.syntactic(r)
            if e is None or e == TRUE:
                continue
            body = e if v.when == TRUE else Binary("->", v.when, e)
            spec.legal.append(Rule(f"sva:{r.name}:{v.name}", body, "assume", False, r.origin))
    for k, c in sva.cset.schema.consts.items():
        spec.consts.setdefault(k, c.value)


def load_shield_spec(path: str | Path) -> ShieldSpec:
    p = Path(path)
    d = yaml.safe_load(p.read_text())
    base = p.parent
    consts = {str(k): int(v) for k, v in (d.get("consts") or {}).items()}
    state = _fields(d.get("state"), "state")
    action = _fields(d.get("action"), "action")
    for f in state + action:
        for n, v in f.enum:
            consts.setdefault(n, v)
    spec = ShieldSpec(d.get("name", p.stem), state, action, consts=consts, base_dir=base,
                      reach_bound=int((d.get("options") or {}).get("reach_bound", 256)))
    spec.init = _expr(d.get("init", True), consts)
    for i, t in enumerate(d.get("transitions") or []):
        nxt = {k: _expr(v, consts) for k, v in (t.get("next") or {}).items()}
        spec.transitions.append(Transition(t.get("name", f"t{i}"), _expr(t.get("when", True), consts), nxt, t.get("kind", "action")))
    for i, r in enumerate(d.get("legal") or []):
        if isinstance(r, str):
            r = {"expr": r}
        name = r.get("name", f"legal{i}")
        spec.legal.append(Rule(name, _expr(r["expr"], consts), "legal", False, Origin(str(p), 0, str(r["expr"]))))
    for src in d.get("rules") or []:
        fmt = src.get("format", "fbr")
        if fmt == "fbr":
            _load_rules_fbr(spec, src, base)
        elif fmt == "sva":
            _load_rules_sva(spec, src, base)
        else:
            raise SpecError(f"unknown rule source format '{fmt}'")
    for inv in d.get("invariants") or []:
        facts = load_facts(inv["format"], base / inv["file"], outputs=inv.get("outputs"))
        rename = {k: parse_expr(str(v), consts) for k, v in (inv.get("map") or {}).items()}
        e = substitute(facts.expr(), rename) if rename else facts.expr()
        known = {f.name for f in state + action} | set(consts)
        unknown = free_vars(e) - known
        if unknown:
            raise SpecError(f"invariant {inv['file']} references unmapped names {sorted(unknown)}; add them to 'map'")
        spec.invariants.append(InvariantSource(facts, e, inv.get("name", Path(inv["file"]).name)))
    sch = spec.schema()
    for f in sch.fields:
        if f in sch.consts and f not in consts:
            raise SpecError(f"field '{f}' clashes with a constant name")
    for t in spec.transitions:
        for k in t.next:
            if k not in {f.name for f in state}:
                raise SpecError(f"transition '{t.name}' assigns unknown state field '{k}'")
        if t.kind == "env" and free_vars(t.when) & {f.name for f in action}:
            raise SpecError(f"env transition '{t.name}' may not depend on action fields")
    return spec
