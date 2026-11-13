from __future__ import annotations

from dataclasses import asdict, dataclass, field

import z3

from ..backends.sva_emit import specialize
from ..backends.uvm_emit import sv_ident
from ..ir.ast import TRUE, ConstraintSet, Origin, Rule, Schema, free_vars, is_temporal
from ..ir.printer import to_sv
from ..ir.smt import Encoder, unsat_core
from ..mapping import Mapping, View
from .project import ViewProjector

TIMEOUT_MS = 30000

PAIR_KINDS = {
    "uvm<->sva": ("SIM_ALLOWS_FORMAL_FORBIDS", "FORMAL_ALLOWS_SIM_FORBIDS", "error", "warning"),
    "spec<->sva": ("SVA_EXTRA_ASSUME", "SVA_MISSING_SPEC_RULE", "error", "error"),
}


@dataclass
class Finding:
    kind: str
    severity: str
    pair: str
    subject: str
    source: str
    message: str
    view: str | None = None
    origin: dict | None = None
    witness: dict | None = None
    related: list[str] = field(default_factory=list)
    suggestion: str | None = None


@dataclass
class AssumeInfo:
    name: str
    origin: dict
    kind: str = "no-effect"
    classes: dict[str, str] = field(default_factory=dict)
    projected: dict[str, str] = field(default_factory=dict)


@dataclass
class ViewResult:
    name: str
    when: str
    sample: str
    item_satisfiable: bool = True
    formal_satisfiable: bool = True
    equivalent: bool | None = None


@dataclass
class Audit:
    findings: list[Finding] = field(default_factory=list)
    views: list[ViewResult] = field(default_factory=list)
    assumes: list[AssumeInfo] = field(default_factory=list)
    warnings: list[str] = field(default_factory=list)

    def counts(self) -> dict[str, int]:
        out = {"error": 0, "warning": 0, "info": 0}
        for f in self.findings:
            out[f.severity] = out.get(f.severity, 0) + 1
        return out

    def verdict(self) -> str:
        c = self.counts()
        if any(f.kind in ("UVM_CONFLICT", "FORMAL_VACUOUS") for f in self.findings):
            return "VACUOUS"
        if c["error"] or c["warning"]:
            return "DRIFT"
        return "EQUIVALENT"

    def to_dict(self) -> dict:
        return {
            "verdict": self.verdict(),
            "counts": self.counts(),
            "views": [asdict(v) for v in self.views],
            "findings": [asdict(f) for f in self.findings],
            "assumes": [asdict(a) for a in self.assumes],
            "warnings": list(self.warnings),
        }


def _origin(r: Rule) -> dict:
    o: Origin = r.origin
    return {"file": o.file, "line": o.line, "text": o.text}


def _solver(*cs) -> z3.Solver:
    s = z3.Solver()
    s.set("timeout", TIMEOUT_MS)
    s.add(*cs)
    return s


def _forall(vs, body):
    vs = list(vs)
    return z3.ForAll(vs, body) if vs else body


def format_witness(values: dict[str, int], schema: Schema) -> dict:
    out = {}
    for n, v in values.items():
        f = schema.fields.get(n)
        if f is not None and f.enum:
            names = [m for m, val in f.enum if val == v]
            out[n] = names[0] if names else v
        else:
            out[n] = f"0x{v:X}" if f is not None and f.width > 4 else v
    return out


class ViewAuditor:
    def __init__(self, item: ConstraintSet, assumes: list[Rule], sig_schema: Schema, view: View, mapping: Mapping, pair: str, audit: Audit):
        self.item = item
        self.assumes = assumes
        self.view = view
        self.pair = pair
        self.audit = audit
        self.proj = ViewProjector(item.schema, sig_schema, view, mapping)
        self.enc = self.proj.item
        self.when = self.enc.bool(view.when)
        self.hard = item.hard()
        self.c = {r.name: self.enc.bool(r.body()) for r in self.hard}
        mapped = set(view.fields)
        self.unmapped = [self.enc.var(f) for f in item.schema.fields if f not in mapped]
        self.all_vars = {f: self.enc.var(f) for f in item.schema.fields}
        self.result = ViewResult(view.name, view.when_text or "1", view.sample_text)

    def _model(self, m: z3.ModelRef, names) -> dict[str, int]:
        return {n: m.eval(self.all_vars[n], model_completion=True).as_long() for n in names}

    def _add(self, kind: str, severity: str, subject: str, source: str, message: str, **kw):
        self.audit.findings.append(Finding(kind, severity, self.pair, subject, source, message, self.view.name, **kw))

    def _phi_with(self, rules: list[Rule], fixed: dict[str, int], tag: str) -> bool:
        p = self.proj.project(rules, tag)
        eqs = [self.all_vars[n] == v for n, v in fixed.items() if n in self.view.fields]
        return _solver(p.phi, *eqs).check() == z3.sat

    def run(self) -> ViewResult:
        core = unsat_core(self.c, [self.when])
        if core is not None:
            self.result.item_satisfiable = False
            self._add("UVM_CONFLICT" if self.pair.startswith("uvm") else "SPEC_CONFLICT", "error", ",".join(core), self.pair.split("<->")[0],
                      f"constraints are unsatisfiable in view '{self.view.name}'; randomize() would fail", related=core)
        full = self.proj.project(self.assumes, "F")
        if _solver(full.phi).check() == z3.unsat:
            self.result.formal_satisfiable = False
            core = self._formal_core()
            self._add("FORMAL_VACUOUS", "error", ",".join(core), "sva",
                      f"assumptions admit no transaction in view '{self.view.name}'; every proof in this view is vacuous", related=core)
        if not (self.result.item_satisfiable and self.result.formal_satisfiable):
            return self.result
        before = len(self.audit.findings)
        self._direction_item_allows()
        self._direction_formal_allows(full)
        self.result.equivalent = len(self.audit.findings) == before
        return self.result

    def _formal_core(self) -> list[str]:
        core = list(self.assumes)
        for r in list(core):
            trial = [x for x in core if x is not r]
            if _solver(self.proj.project(trial, "C").phi).check() == z3.unsat:
                core = trial
        return [r.name for r in core]

    def _direction_item_allows(self):
        k_item, _, sev, _ = PAIR_KINDS[self.pair]
        remaining = list(self.assumes)
        rounds = 0
        while remaining and rounds < 32:
            rounds += 1
            p = self.proj.project(remaining, f"A{rounds}")
            s = _solver(self.when, *self.c.values(), _forall(p.free_signals, z3.Not(p.phi)))
            r = s.check()
            if r == z3.unknown:
                self.audit.warnings.append(f"view {self.view.name}: inconclusive item->formal check ({s.reason_unknown()})")
                return
            if r == z3.unsat:
                return
            w = self._model(s.model(), self.item.schema.fields)
            culprits = [a for a in remaining if not self._phi_with([a], w, "X")]
            if not culprits:
                culprits = list(remaining)
                for a in list(culprits):
                    trial = [x for x in culprits if x is not a]
                    if trial and not self._phi_with(trial, w, "Y"):
                        culprits = trial
            for a in culprits:
                wa = self._isolated_witness(a, remaining) or w
                proj = self.proj.syntactic(a)
                sugg = None
                if proj is not None and proj != TRUE:
                    guard = f"{self.view.when_text} -> " if self.view.when_text else ""
                    sugg = f"constraint c_sync_{sv_ident(a.name)} {{ {guard}{to_sv(proj)}; }}"
                src_label = "UVM" if self.pair.startswith("uvm") else "spec"
                self._add(k_item, sev, a.name, "sva",
                          f"{src_label} admits transactions in view '{self.view.name}' that violate assume '{a.name}'",
                          origin=_origin(a), witness=format_witness(wa, self.item.schema), related=[c.name for c in culprits if c is not a],
                          suggestion=sugg)
            remaining = [a for a in remaining if a not in culprits]

    def _isolated_witness(self, a: Rule, pool: list[Rule]) -> dict[str, int] | None:
        pa = self.proj.project([a], "I")
        others = [x for x in pool if x is not a]
        cs = [self.when, *self.c.values(), _forall(pa.free_signals, z3.Not(pa.phi))]
        if others:
            cs.append(self.proj.project(others, "J").phi)
        s = _solver(*cs)
        if s.check() != z3.sat:
            return None
        return self._model(s.model(), self.item.schema.fields)

    def _direction_formal_allows(self, full):
        _, k_formal, _, sev = PAIR_KINDS[self.pair]
        remaining = list(self.hard)
        rounds = 0
        mapped = list(self.view.fields)
        while remaining and rounds < 32:
            rounds += 1
            cr = z3.And(self.when, *[self.enc.bool(r.body()) for r in remaining])
            s = _solver(full.phi, _forall(self.unmapped, z3.Not(cr)))
            r = s.check()
            if r == z3.unknown:
                self.audit.warnings.append(f"view {self.view.name}: inconclusive formal->item check ({s.reason_unknown()})")
                return
            if r == z3.unsat:
                return
            w = self._model(s.model(), mapped)
            eqs = [self.all_vars[n] == v for n, v in w.items()]
            culprits = [c for c in remaining if _solver(self.when, self.enc.bool(c.body()), *eqs).check() == z3.unsat]
            if not culprits:
                culprits = list(remaining)
                for c in list(culprits):
                    trial = [x for x in culprits if x is not c]
                    if trial and _solver(self.when, *[self.enc.bool(x.body()) for x in trial], *eqs).check() == z3.unsat:
                        culprits = trial
            for c in culprits:
                spec = specialize(c.body(), self.view, self.item.schema)
                sugg = None
                if spec != TRUE and not (free_vars(spec) - set(self.proj.sig_schema.fields) - set(self.item.schema.consts)):
                    sugg = f"assume property ({_paren(self.view.sample_text)} |-> {_paren(to_sv(spec))});"
                src_label = "UVM" if self.pair.startswith("uvm") else "spec"
                self._add(k_formal, sev, c.name, self.pair.split("<->")[0],
                          f"formal environment admits transactions in view '{self.view.name}' that {src_label} rule '{c.name}' excludes",
                          origin=_origin(c), witness=format_witness(w, self.item.schema), related=[x.name for x in culprits if x is not c],
                          suggestion=sugg)
            remaining = [c for c in remaining if c not in culprits]


def _paren(s: str) -> str:
    return s if s.replace("_", "").isalnum() else f"({s})"


def classify_assumes(item: ConstraintSet, assumes: list[Rule], sig_schema: Schema, mapping: Mapping) -> list[AssumeInfo]:
    out = []
    for a in assumes:
        info = AssumeInfo(a.name, _origin(a))
        for v in mapping.views:
            pj = ViewProjector(item.schema, sig_schema, v, mapping)
            syn = pj.syntactic(a)
            if syn is not None:
                info.projected[v.name] = to_sv(syn)
                info.classes[v.name] = "no-effect" if syn == TRUE else "transaction"
                continue
            p = pj.project([a], "K")
            s = _solver(pj.item.bool(v.when), _forall(p.free_signals, z3.Not(p.phi)))
            r = s.check()
            info.classes[v.name] = "no-effect" if r == z3.unsat else ("transaction" if r == z3.sat else "unknown")
        if "transaction" in info.classes.values():
            info.kind = "transaction"
        elif is_temporal(a.body()):
            info.kind = "protocol"
        out.append(info)
    return out


def global_item_checks(item: ConstraintSet, pair_src: str, audit: Audit) -> None:
    enc = Encoder(item.schema)
    hard = item.hard()
    cs = {r.name: enc.bool(r.body()) for r in hard}
    if unsat_core(cs) is not None:
        return
    for r in hard:
        others = [cs[x.name] for x in hard if x is not r]
        if _solver(*others, z3.Not(cs[r.name])).check() == z3.unsat:
            audit.findings.append(Finding("REDUNDANT_CONSTRAINT", "info", pair_src, r.name, pair_src,
                                          f"constraint '{r.name}' is implied by the remaining hard constraints", origin=_origin(r)))
    for r in item.rules:
        if r.soft and _solver(*cs.values(), enc.bool(r.body())).check() == z3.unsat:
            audit.findings.append(Finding("DEAD_SOFT", "info", pair_src, r.name, pair_src,
                                          f"soft constraint '{r.name}' can never be honoured under the hard constraints", origin=_origin(r)))


def compare_items(spec: ConstraintSet, uvm: ConstraintSet, audit: Audit) -> None:
    schema = uvm.schema.merged(spec.schema)
    enc = Encoder(schema)
    cu = [enc.bool(r.body()) for r in uvm.hard()]
    cs = [enc.bool(r.body()) for r in spec.hard()]
    names = list(schema.fields)
    for r in spec.hard():
        s = _solver(*cu, z3.Not(enc.bool(r.body())))
        if s.check() == z3.sat:
            w = {n: s.model().eval(enc.var(n), model_completion=True).as_long() for n in names}
            audit.findings.append(Finding("UVM_MISSING_SPEC_RULE", "error", "spec<->uvm", r.name, "spec",
                                          f"UVM constraints permit stimulus violating spec rule '{r.name}'",
                                          origin=_origin(r), witness=format_witness(w, schema)))
    for r in uvm.hard():
        s = _solver(*cs, z3.Not(enc.bool(r.body())))
        if s.check() == z3.sat:
            w = {n: s.model().eval(enc.var(n), model_completion=True).as_long() for n in names}
            audit.findings.append(Finding("UVM_EXTRA_CONSTRAINT", "warning", "spec<->uvm", r.name, "uvm",
                                          f"UVM constraint '{r.name}' excludes stimulus the spec allows (coverage loss)",
                                          origin=_origin(r), witness=format_witness(w, schema)))


def run_audit(uvm: ConstraintSet | None, sva_rules: list[Rule], sig_schema: Schema, mapping: Mapping,
              spec: ConstraintSet | None = None) -> Audit:
    audit = Audit()
    primary = uvm if uvm is not None else spec
    if primary is None:
        raise ValueError("need a UVM item or a spec")
    if uvm is not None:
        global_item_checks(uvm, "uvm", audit)
        for v in mapping.views:
            audit.views.append(ViewAuditor(uvm, sva_rules, sig_schema, v, mapping, "uvm<->sva", audit).run())
    if spec is not None:
        if uvm is not None:
            compare_items(spec, uvm, audit)
        for v in mapping.views:
            vr = ViewAuditor(spec, sva_rules, sig_schema, v, mapping, "spec<->sva", audit).run()
            vr.name = f"spec:{vr.name}"
            audit.views.append(vr)
    audit.assumes = classify_assumes(primary, sva_rules, sig_schema, mapping)
    return audit
