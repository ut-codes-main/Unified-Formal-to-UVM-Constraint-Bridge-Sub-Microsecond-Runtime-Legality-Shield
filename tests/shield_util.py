from __future__ import annotations

import z3
from cffi import FFI

from fbridge.ir import Var, conj, evaluate, holds
from fbridge.ir.smt import Encoder
from fbridge.shield.build import build_shared
from fbridge.shield.compile import CompiledShield
from fbridge.shield.emit import write_artifacts

CDEF = """
typedef unsigned long long shield_u64;
int {P}_is_action_legal(shield_u64, shield_u64);
int {P}_is_state_reachable(shield_u64);
int {P}_class_of(shield_u64);
int {P}_project_or_mask_action(shield_u64, shield_u64, shield_u64 *, shield_u64 *);
int {P}_field_intervals(shield_u64, int, shield_u64 *, shield_u64 *, int);
shield_u64 {P}_class_bitmap_word(int, int);
shield_u64 {P}_explain(shield_u64, shield_u64);
shield_u64 {P}_step_action(shield_u64, shield_u64);
shield_u64 {P}_step_env(shield_u64, int);
int {P}_num_env(void);
int is_action_legal(shield_u64, shield_u64);
"""


class CShield:
    def __init__(self, comp: CompiledShield, out_dir):
        art = write_artifacts(comp, out_dir)
        self.lib_path = build_shared([art.paths["c"]], out_dir / "shield")
        self.ffi = FFI()
        self.P = art.c.prefix
        self.ffi.cdef(CDEF.replace("{P}", self.P))
        self.lib = self.ffi.dlopen(str(self.lib_path))
        self.mask_words = sum(f.mask_words for f in comp.fields) or 1
        self.art = art

    def fn(self, name):
        return getattr(self.lib, f"{self.P}_{name}")

    def project(self, s, tx):
        rep = self.ffi.new("shield_u64 *")
        masks = self.ffi.new(f"shield_u64[{self.mask_words}]")
        st = self.fn("project_or_mask_action")(s, tx, rep, masks)
        return st, rep[0], list(masks)


def oracle_reach(spec) -> set[int]:
    sch = spec.schema()
    legal = conj([r.body() for r in spec.legal])
    inv = conj([i.expr for i in spec.invariants])
    states = set()
    frontier = []
    for s in range(1 << spec.state_bits):
        env = spec.unpack(s, "state")
        if holds(spec.init, sch, env) and holds(inv, sch, env) and _state_domain(spec, env):
            states.add(s)
            frontier.append(s)
    while frontier:
        s = frontier.pop()
        env = spec.unpack(s, "state")
        succ = set()
        for t in spec.transitions:
            if t.kind == "env":
                if holds(t.when, sch, env):
                    nxt = dict(env)
                    for k, e in t.next.items():
                        nxt[k] = evaluate(e, sch, env) & ((1 << spec.field(k).width) - 1)
                    succ.add(spec.pack(nxt, "state"))
                continue
            enc = Encoder(sch)
            sol = z3.Solver()
            for k, v in env.items():
                sol.add(enc.var(k) == v)
            sol.add(enc.bool(legal), enc.bool(t.when))
            for f in spec.action:
                if f.enum:
                    sol.add(z3.Or(*[enc.var(f.name) == v for _, v in f.enum]))
            nexts = {}
            for f in spec.state:
                e = t.next.get(f.name, Var(f.name))
                nexts[f.name] = z3.Extract(f.width - 1, 0, z3.ZeroExt(64, enc.bv(e)))
            while sol.check() == z3.sat:
                mdl = sol.model()
                vals = {k: mdl.eval(v, model_completion=True).as_long() for k, v in nexts.items()}
                succ.add(spec.pack(vals, "state"))
                sol.add(z3.Or(*[nexts[k] != vals[k] for k in vals]))
        for n in succ:
            if n not in states and holds(inv, sch, spec.unpack(n, "state")):
                states.add(n)
                frontier.append(n)
    return states


def _state_domain(spec, env) -> bool:
    for f in spec.state:
        if f.enum and env[f.name] not in {v for _, v in f.enum}:
            return False
    return True


def oracle_legal(spec, reach: set[int], s: int, tx: int) -> bool:
    if s not in reach:
        return False
    sch = spec.schema()
    env = {**spec.unpack(s, "state"), **spec.unpack(tx, "action")}
    for f in spec.action:
        if f.enum and env[f.name] not in {v for _, v in f.enum}:
            return False
    return all(holds(r.body(), sch, env) for r in spec.legal)
