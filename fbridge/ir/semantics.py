from __future__ import annotations

from typing import Any, Callable, Mapping, Sequence

from .ast import (
    ARITH_OPS, BITWISE_OPS, COMPARE_OPS, LOGIC_OPS, SHIFT_OPS,
    Binary, Concat, Const, Dist, Expr, Func, Inside, Ite, Next, Past, Range, Schema, Slice, Unary, Var,
)


class SemanticsError(Exception):
    pass


class Backend:
    def const(self, v: int, w: int): ...
    def var(self, name: str, t: int, w: int): ...
    def ext(self, x, wf: int, wt: int, signed: bool): ...
    def extract(self, x, hi: int, lo: int, w: int): ...
    def concat(self, parts: Sequence[tuple[Any, int]]): ...
    def arith(self, op: str, x, y, w: int, signed: bool): ...
    def bitop(self, op: str, x, y, w: int): ...
    def bnot(self, x, w: int): ...
    def neg(self, x, w: int): ...
    def shift(self, op: str, x, y, w: int, signed: bool): ...
    def cmp(self, op: str, x, y, w: int, signed: bool): ...
    def b_not(self, a): ...
    def b_and(self, xs): ...
    def b_or(self, xs): ...
    def b_iff(self, a, b): ...
    def b_true(self): ...
    def b_false(self): ...
    def ite(self, c, x, y, w: int): ...
    def to_bool(self, x, w: int): ...
    def from_bool(self, b): ...
    def popcount(self, x, w: int, wo: int): ...


Resolver = Callable[[str, int], "tuple[Any, int, bool] | None"]


class Lowerer:
    def __init__(self, schema: Schema, backend: Backend, resolver: Resolver | None = None):
        self.schema = schema
        self.be = backend
        self.resolver = resolver
        self._self_cache: dict[int, tuple[Expr, tuple[int, bool]]] = {}
        self._memo: dict[tuple, tuple[Expr, Any]] = {}

    def var_type(self, name: str) -> tuple[int, bool]:
        if name in self.schema.fields:
            f = self.schema.fields[name]
            return f.width, f.signed
        if name in self.schema.consts:
            c = self.schema.consts[name]
            return c.width, c.signed
        raise SemanticsError(f"unknown identifier '{name}'")

    def selfdet(self, e: Expr) -> tuple[int, bool]:
        hit = self._self_cache.get(id(e))
        if hit is not None and hit[0] is e:
            return hit[1]
        r = self._selfdet(e)
        self._self_cache[id(e)] = (e, r)
        return r

    def _selfdet(self, e: Expr) -> tuple[int, bool]:
        if isinstance(e, Const):
            return e.width, e.signed
        if isinstance(e, Var):
            return self.var_type(e.name)
        if isinstance(e, Unary):
            if e.op in ("~", "-", "+"):
                return self.selfdet(e.a)
            return 1, False
        if isinstance(e, Binary):
            if e.op in ARITH_OPS or e.op in BITWISE_OPS:
                wa, sa = self.selfdet(e.a)
                wb, sb = self.selfdet(e.b)
                return max(wa, wb), sa and sb
            if e.op in SHIFT_OPS:
                return self.selfdet(e.a)
            return 1, False
        if isinstance(e, Ite):
            wa, sa = self.selfdet(e.then)
            wb, sb = self.selfdet(e.other)
            return max(wa, wb), sa and sb
        if isinstance(e, Slice):
            return e.hi - e.lo + 1, False
        if isinstance(e, Concat):
            return sum(self.selfdet(p)[0] for p in e.parts), False
        if isinstance(e, (Inside, Dist)):
            return 1, False
        if isinstance(e, (Past, Next)):
            return self.selfdet(e.a)
        if isinstance(e, Func):
            if e.name == "$countones":
                return 32, False
            if e.name == "$signed":
                return self.selfdet(e.args[0])[0], True
            if e.name == "$unsigned":
                return self.selfdet(e.args[0])[0], False
            if e.name == "$clog2":
                return 32, True
            return 1, False
        raise SemanticsError(f"cannot type {e!r}")

    def const_eval(self, e: Expr) -> int:
        from .evaluate import evaluate
        return evaluate(e, self.schema, {})

    def bool(self, e: Expr, t: int = 0):
        key = ("b", id(e), t)
        hit = self._memo.get(key)
        if hit is not None and hit[0] is e:
            return hit[1]
        r = self._bool(e, t)
        self._memo[key] = (e, r)
        return r

    def bv(self, e: Expr, t: int, w: int, s: bool):
        key = ("v", id(e), t, w, s)
        hit = self._memo.get(key)
        if hit is not None and hit[0] is e:
            return hit[1]
        r = self._bv(e, t, w, s)
        self._memo[key] = (e, r)
        return r

    def _bool(self, e: Expr, t: int = 0):
        be = self.be
        if isinstance(e, Unary) and e.op == "!":
            return be.b_not(self.bool(e.a, t))
        if isinstance(e, Binary):
            op = e.op
            if op == "&&":
                return be.b_and([self.bool(e.a, t), self.bool(e.b, t)])
            if op == "||":
                return be.b_or([self.bool(e.a, t), self.bool(e.b, t)])
            if op == "->":
                return be.b_or([be.b_not(self.bool(e.a, t)), self.bool(e.b, t)])
            if op == "<->":
                return be.b_iff(self.bool(e.a, t), self.bool(e.b, t))
            if op in COMPARE_OPS:
                wa, sa = self.selfdet(e.a)
                wb, sb = self.selfdet(e.b)
                w, s = max(wa, wb), sa and sb
                x = self.bv(e.a, t, w, s)
                y = self.bv(e.b, t, w, s)
                return be.cmp(op.replace("===", "==").replace("!==", "!="), x, y, w, s)
        if isinstance(e, Ite) and self.selfdet(e) == (1, False):
            c = self.bool(e.cond, t)
            return be.b_or([be.b_and([c, self.bool(e.then, t)]), be.b_and([be.b_not(c), self.bool(e.other, t)])])
        if isinstance(e, Inside):
            return self._inside(e.a, e.items, t)
        if isinstance(e, Dist):
            return self.bool(e.support(), t)
        if isinstance(e, Past):
            return self.bool(e.a, t - e.n)
        if isinstance(e, Next):
            return self.bool(e.a, t + e.n)
        if isinstance(e, Func) and e.name in ("$stable", "$changed", "$rose", "$fell", "$onehot", "$onehot0", "$isunknown"):
            return self._func_bool(e, t)
        w, s = self.selfdet(e)
        return be.to_bool(self.bv(e, t, w, s), w)

    def _inside(self, a: Expr, items, t: int):
        be = self.be
        ws = [self.selfdet(a)]
        for it in items:
            if isinstance(it, Range):
                ws += [self.selfdet(it.lo), self.selfdet(it.hi)]
            else:
                ws.append(self.selfdet(it))
        w = max(x[0] for x in ws)
        s = all(x[1] for x in ws)
        x = self.bv(a, t, w, s)
        terms = []
        for it in items:
            if isinstance(it, Range):
                lo = self.bv(it.lo, t, w, s)
                hi = self.bv(it.hi, t, w, s)
                terms.append(be.b_and([be.cmp(">=", x, lo, w, s), be.cmp("<=", x, hi, w, s)]))
            else:
                terms.append(be.cmp("==", x, self.bv(it, t, w, s), w, s))
        return be.b_or(terms) if terms else be.b_false()

    def _func_bool(self, e: Func, t: int):
        be = self.be
        a = e.args[0] if e.args else None
        if e.name == "$isunknown":
            return be.b_false()
        w, s = self.selfdet(a)
        if e.name in ("$stable", "$changed"):
            eq = be.cmp("==", self.bv(a, t, w, s), self.bv(a, t - 1, w, s), w, s)
            return eq if e.name == "$stable" else be.b_not(eq)
        if e.name in ("$rose", "$fell"):
            now = be.to_bool(be.extract(self.bv(a, t, w, s), 0, 0, w), 1)
            prev = be.to_bool(be.extract(self.bv(a, t - 1, w, s), 0, 0, w), 1)
            if e.name == "$rose":
                return be.b_and([now, be.b_not(prev)])
            return be.b_and([be.b_not(now), prev])
        x = self.bv(a, t, w, s)
        cnt = be.popcount(x, w, 32)
        if e.name == "$onehot":
            return be.cmp("==", cnt, be.const(1, 32), 32, False)
        return be.cmp("<=", cnt, be.const(1, 32), 32, False)

    def _fit(self, x, w_have: int, s_have: bool, w: int, s: bool):
        if w_have == w:
            return x
        if w_have > w:
            return self.be.extract(x, w - 1, 0, w_have)
        return self.be.ext(x, w_have, w, s and s_have)

    def _bv(self, e: Expr, t: int, w: int, s: bool):
        be = self.be
        if isinstance(e, Const):
            v = e.value
            if s and e.signed and e.width < w and (v >> (e.width - 1)) & 1:
                v = v - (1 << e.width)
            return be.const(v & ((1 << w) - 1), w)
        if isinstance(e, Var):
            if self.resolver is not None:
                r = self.resolver(e.name, t)
                if r is not None:
                    x, vw, vs = r
                    return self._fit(x, vw, vs, w, s)
            if e.name in self.schema.consts and e.name not in self.schema.fields:
                return self.bv(self.schema.consts[e.name], t, w, s)
            vw, vs = self.var_type(e.name)
            return self._fit(be.var(e.name, t, vw), vw, vs, w, s)
        if isinstance(e, Unary):
            if e.op == "~":
                return be.bnot(self.bv(e.a, t, w, s), w)
            if e.op == "-":
                return be.neg(self.bv(e.a, t, w, s), w)
            if e.op == "+":
                return self.bv(e.a, t, w, s)
            if e.op == "!":
                return self._fit(be.from_bool(self.bool(e, t)), 1, False, w, s)
            wa, sa = self.selfdet(e.a)
            x = self.bv(e.a, t, wa, sa)
            bits = [be.extract(x, i, i, wa) for i in range(wa)]
            base = e.op.lstrip("~")[0]
            acc = bits[0]
            for b in bits[1:]:
                acc = be.bitop(base, acc, b, 1)
            if e.op.startswith("~"):
                acc = be.bnot(acc, 1)
            return self._fit(acc, 1, False, w, s)
        if isinstance(e, Binary):
            if e.op in ARITH_OPS:
                return be.arith(e.op, self.bv(e.a, t, w, s), self.bv(e.b, t, w, s), w, s)
            if e.op in BITWISE_OPS:
                return be.bitop(e.op, self.bv(e.a, t, w, s), self.bv(e.b, t, w, s), w)
            if e.op in SHIFT_OPS:
                x = self.bv(e.a, t, w, s)
                wb, _ = self.selfdet(e.b)
                y = self.bv(e.b, t, wb, False)
                ww = max(w, wb)
                xr = self._fit(x, w, s, ww, s)
                yr = self._fit(y, wb, False, ww, False)
                op = e.op
                if op == ">>>" and not s:
                    op = ">>"
                if op == "<<<":
                    op = "<<"
                r = be.shift(op, xr, yr, ww, s)
                return self._fit(r, ww, s, w, s)
            if e.op in COMPARE_OPS or e.op in LOGIC_OPS:
                return self._fit(be.from_bool(self.bool(e, t)), 1, False, w, s)
        if isinstance(e, Ite):
            c = self.bool(e.cond, t)
            return be.ite(c, self.bv(e.then, t, w, s), self.bv(e.other, t, w, s), w)
        if isinstance(e, Slice):
            wa, sa = self.selfdet(e.a)
            x = self.bv(e.a, t, wa, sa)
            if e.hi >= wa:
                x = be.ext(x, wa, e.hi + 1, False)
                wa = e.hi + 1
            r = be.extract(x, e.hi, e.lo, wa)
            return self._fit(r, e.hi - e.lo + 1, False, w, s)
        if isinstance(e, Concat):
            parts = []
            for p in e.parts:
                pw, ps = self.selfdet(p)
                parts.append((self.bv(p, t, pw, ps), pw))
            total = sum(pw for _, pw in parts)
            return self._fit(be.concat(parts), total, False, w, s)
        if isinstance(e, (Inside, Dist)):
            return self._fit(be.from_bool(self.bool(e, t)), 1, False, w, s)
        if isinstance(e, Past):
            return self.bv(e.a, t - e.n, w, s)
        if isinstance(e, Next):
            return self.bv(e.a, t + e.n, w, s)
        if isinstance(e, Func):
            if e.name in ("$signed", "$unsigned"):
                wa, _ = self.selfdet(e.args[0])
                x = self.bv(e.args[0], t, wa, False)
                return self._fit(x, wa, e.name == "$signed", w, s)
            if e.name == "$countones":
                wa, sa = self.selfdet(e.args[0])
                return self._fit(be.popcount(self.bv(e.args[0], t, wa, sa), wa, 32), 32, False, w, s)
            if e.name == "$clog2":
                v = self.const_eval(e.args[0])
                return be.const(max(0, (v - 1).bit_length()) & ((1 << w) - 1), w)
            return self._fit(be.from_bool(self.bool(e, t)), 1, False, w, s)
        raise SemanticsError(f"cannot lower {e!r}")


def to_signed(v: int, w: int) -> int:
    return v - (1 << w) if (v >> (w - 1)) & 1 else v


class PyBackend(Backend):
    def __init__(self, env: Callable[[str, int], int] | Mapping[str, int]):
        if callable(env):
            self.env = env
        else:
            m = env
            self.env = lambda n, t: m.get(n, 0) if t == 0 else 0

    def const(self, v, w):
        return v & ((1 << w) - 1)

    def var(self, name, t, w):
        return self.env(name, t) & ((1 << w) - 1)

    def ext(self, x, wf, wt, signed):
        if signed and (x >> (wf - 1)) & 1:
            return x | (((1 << wt) - 1) ^ ((1 << wf) - 1))
        return x

    def extract(self, x, hi, lo, w):
        return (x >> lo) & ((1 << (hi - lo + 1)) - 1)

    def concat(self, parts):
        out = 0
        for x, w in parts:
            out = (out << w) | x
        return out

    def arith(self, op, x, y, w, signed):
        m = (1 << w) - 1
        if op == "+":
            return (x + y) & m
        if op == "-":
            return (x - y) & m
        if op == "*":
            return (x * y) & m
        if signed:
            a, b = to_signed(x, w), to_signed(y, w)
            if b == 0:
                return (m if a >= 0 else 1) if op == "/" else x
            q = abs(a) // abs(b)
            if (a < 0) != (b < 0):
                q = -q
            if op == "/":
                return q & m
            return (a - q * b) & m
        if y == 0:
            return m if op == "/" else x
        return (x // y) if op == "/" else (x % y)

    def bitop(self, op, x, y, w):
        m = (1 << w) - 1
        if op == "&":
            return x & y
        if op == "|":
            return x | y
        if op == "^":
            return x ^ y
        return ~(x ^ y) & m

    def bnot(self, x, w):
        return ~x & ((1 << w) - 1)

    def neg(self, x, w):
        return (-x) & ((1 << w) - 1)

    def shift(self, op, x, y, w, signed):
        m = (1 << w) - 1
        if op == "<<":
            return (x << y) & m if y < w else 0
        if op == ">>":
            return x >> y if y < w else 0
        sx = to_signed(x, w)
        return (sx >> min(y, w)) & m

    def cmp(self, op, x, y, w, signed):
        if signed:
            x, y = to_signed(x, w), to_signed(y, w)
        return {"==": x == y, "!=": x != y, "<": x < y, "<=": x <= y, ">": x > y, ">=": x >= y}[op]

    def b_not(self, a):
        return not a

    def b_and(self, xs):
        return all(xs)

    def b_or(self, xs):
        return any(xs)

    def b_iff(self, a, b):
        return a == b

    def b_true(self):
        return True

    def b_false(self):
        return False

    def ite(self, c, x, y, w):
        return x if c else y

    def to_bool(self, x, w):
        return x != 0

    def from_bool(self, b):
        return 1 if b else 0

    def popcount(self, x, w, wo):
        return bin(x).count("1")
