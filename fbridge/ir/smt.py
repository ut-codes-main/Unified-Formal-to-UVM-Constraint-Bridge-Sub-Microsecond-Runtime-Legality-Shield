from __future__ import annotations

from typing import Iterable

import z3

from .ast import Expr, Rule, Schema, temporal_span
from .semantics import Backend, Lowerer, Resolver


class Z3Backend(Backend):
    def __init__(self, prefix: str = "", ctx: z3.Context | None = None):
        self.prefix = prefix
        self.ctx = ctx
        self.vars: dict[tuple[str, int], z3.BitVecRef] = {}

    def name(self, n: str, t: int) -> str:
        return f"{self.prefix}{n}@{t}" if t else f"{self.prefix}{n}"

    def const(self, v, w):
        return z3.BitVecVal(v, w, self.ctx)

    def var(self, name, t, w):
        key = (name, t)
        x = self.vars.get(key)
        if x is None:
            x = z3.BitVec(self.name(name, t), w, self.ctx)
            self.vars[key] = x
        return x

    def ext(self, x, wf, wt, signed):
        return z3.SignExt(wt - wf, x) if signed else z3.ZeroExt(wt - wf, x)

    def extract(self, x, hi, lo, w):
        return z3.Extract(hi, lo, x)

    def concat(self, parts):
        xs = [x for x, _ in parts]
        return xs[0] if len(xs) == 1 else z3.Concat(*xs)

    def arith(self, op, x, y, w, signed):
        if op == "+":
            return x + y
        if op == "-":
            return x - y
        if op == "*":
            return x * y
        if op == "/":
            return x / y if signed else z3.UDiv(x, y)
        return z3.SRem(x, y) if signed else z3.URem(x, y)

    def bitop(self, op, x, y, w):
        if op == "&":
            return x & y
        if op == "|":
            return x | y
        if op == "^":
            return x ^ y
        return ~(x ^ y)

    def bnot(self, x, w):
        return ~x

    def neg(self, x, w):
        return -x

    def shift(self, op, x, y, w, signed):
        if op == "<<":
            return x << y
        if op == ">>":
            return z3.LShR(x, y)
        return x >> y

    def cmp(self, op, x, y, w, signed):
        if op == "==":
            return x == y
        if op == "!=":
            return x != y
        if signed:
            return {"<": x < y, "<=": x <= y, ">": x > y, ">=": x >= y}[op]
        return {"<": z3.ULT, "<=": z3.ULE, ">": z3.UGT, ">=": z3.UGE}[op](x, y)

    def b_not(self, a):
        return z3.Not(a)

    def b_and(self, xs):
        xs = list(xs)
        return xs[0] if len(xs) == 1 else z3.And(*xs)

    def b_or(self, xs):
        xs = list(xs)
        if not xs:
            return z3.BoolVal(False, self.ctx)
        return xs[0] if len(xs) == 1 else z3.Or(*xs)

    def b_iff(self, a, b):
        return a == b

    def b_true(self):
        return z3.BoolVal(True, self.ctx)

    def b_false(self):
        return z3.BoolVal(False, self.ctx)

    def ite(self, c, x, y, w):
        return z3.If(c, x, y)

    def to_bool(self, x, w):
        return x != z3.BitVecVal(0, w, self.ctx)

    def from_bool(self, b):
        return z3.If(b, z3.BitVecVal(1, 1, self.ctx), z3.BitVecVal(0, 1, self.ctx))

    def popcount(self, x, w, wo):
        bits = [z3.ZeroExt(wo - 1, z3.Extract(i, i, x)) for i in range(w)]
        return z3.Sum(bits) if len(bits) > 1 else bits[0]


class Encoder:
    def __init__(self, schema: Schema, prefix: str = "", resolver: Resolver | None = None):
        self.schema = schema
        self.backend = Z3Backend(prefix)
        self.lowerer = Lowerer(schema, self.backend, resolver)

    def bool(self, e: Expr, t: int = 0) -> z3.BoolRef:
        return self.lowerer.bool(e, t)

    def bv(self, e: Expr, t: int = 0) -> z3.BitVecRef:
        w, s = self.lowerer.selfdet(e)
        return self.lowerer.bv(e, t, w, s)

    def var(self, name: str, t: int = 0) -> z3.BitVecRef:
        return self.backend.var(name, t, self.schema.width(name))

    def rule(self, r: Rule, t: int = 0) -> z3.BoolRef:
        body = self.bool(r.body(), t)
        if r.disable is not None:
            body = z3.Or(self.bool(r.disable, t), body)
        return body

    def unroll(self, r: Rule, depth: int) -> list[z3.BoolRef]:
        lo, hi = temporal_span(r.body())
        out = []
        for t in range(max(0, -lo), depth - max(0, hi)):
            out.append(self.rule(r, t))
        return out

    def model_values(self, m: z3.ModelRef, names: Iterable[str], t: int = 0) -> dict[str, int]:
        out = {}
        for n in names:
            v = m.eval(self.var(n, t), model_completion=True)
            out[n] = v.as_long()
        return out


def check(*constraints, timeout_ms: int = 20000) -> tuple[z3.CheckSatResult, z3.ModelRef | None]:
    s = z3.Solver()
    s.set("timeout", timeout_ms)
    s.add(*constraints)
    r = s.check()
    return r, (s.model() if r == z3.sat else None)


def unsat_core(named: dict[str, z3.BoolRef], background: Iterable[z3.BoolRef] = (), timeout_ms: int = 20000) -> list[str] | None:
    s = z3.Solver()
    s.set("timeout", timeout_ms)
    s.set("core.minimize", True)
    s.add(*background)
    lits = {}
    for name, c in named.items():
        p = z3.Bool(f"__trk_{name}")
        lits[str(p)] = name
        s.assert_and_track(c, p)
    r = s.check()
    if r != z3.unsat:
        return None
    return sorted(lits[str(x)] for x in s.unsat_core())
