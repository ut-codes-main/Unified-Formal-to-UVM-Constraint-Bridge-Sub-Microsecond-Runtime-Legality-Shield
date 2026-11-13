from __future__ import annotations

import sys
from dataclasses import dataclass
from typing import Iterable, Sequence

from .ir.semantics import Backend

FALSE = 0
TRUE = 1


class BDD:
    def __init__(self, nvars: int = 0, names: Sequence[str] | None = None):
        self.var_of = [1 << 30, 1 << 30]
        self.lo = [0, 1]
        self.hi = [0, 1]
        self.unique: dict[tuple[int, int, int], int] = {}
        self.cache: dict[tuple, int] = {}
        self.names: list[str] = list(names) if names else [f"v{i}" for i in range(nvars)]
        if sys.getrecursionlimit() < 20000:
            sys.setrecursionlimit(20000)

    @property
    def nvars(self) -> int:
        return len(self.names)

    def add_var(self, name: str) -> int:
        self.names.append(name)
        return len(self.names) - 1

    def mk(self, v: int, lo: int, hi: int) -> int:
        if lo == hi:
            return lo
        key = (v, lo, hi)
        n = self.unique.get(key)
        if n is None:
            n = len(self.var_of)
            self.var_of.append(v)
            self.lo.append(lo)
            self.hi.append(hi)
            self.unique[key] = n
        return n

    def var(self, v: int) -> int:
        return self.mk(v, FALSE, TRUE)

    def nvar(self, v: int) -> int:
        return self.mk(v, TRUE, FALSE)

    def neg(self, a: int) -> int:
        return self.ite(a, FALSE, TRUE)

    def AND(self, a: int, b: int) -> int:
        return self.ite(a, b, FALSE)

    def OR(self, a: int, b: int) -> int:
        return self.ite(a, TRUE, b)

    def XOR(self, a: int, b: int) -> int:
        return self.ite(a, self.neg(b), b)

    def XNOR(self, a: int, b: int) -> int:
        return self.ite(a, b, self.neg(b))

    def IMP(self, a: int, b: int) -> int:
        return self.ite(a, b, TRUE)

    def and_all(self, xs: Iterable[int]) -> int:
        out = TRUE
        for x in xs:
            out = self.AND(out, x)
            if out == FALSE:
                break
        return out

    def or_all(self, xs: Iterable[int]) -> int:
        out = FALSE
        for x in xs:
            out = self.OR(out, x)
            if out == TRUE:
                break
        return out

    def ite(self, f: int, g: int, h: int) -> int:
        if f == TRUE:
            return g
        if f == FALSE:
            return h
        if g == h:
            return g
        if g == TRUE and h == FALSE:
            return f
        key = ("ite", f, g, h)
        r = self.cache.get(key)
        if r is not None:
            return r
        v = min(self.var_of[f], self.var_of[g], self.var_of[h])
        f0, f1 = self._cof(f, v)
        g0, g1 = self._cof(g, v)
        h0, h1 = self._cof(h, v)
        r = self.mk(v, self.ite(f0, g0, h0), self.ite(f1, g1, h1))
        self.cache[key] = r
        return r

    def _cof(self, n: int, v: int) -> tuple[int, int]:
        if self.var_of[n] == v:
            return self.lo[n], self.hi[n]
        return n, n

    def restrict(self, f: int, assign: dict[int, int]) -> int:
        memo: dict[int, int] = {}

        def go(n: int) -> int:
            if n <= TRUE:
                return n
            r = memo.get(n)
            if r is not None:
                return r
            v = self.var_of[n]
            if v in assign:
                r = go(self.hi[n] if assign[v] else self.lo[n])
            else:
                r = self.mk(v, go(self.lo[n]), go(self.hi[n]))
            memo[n] = r
            return r
        return go(f)

    def exists(self, f: int, vars_: Iterable[int]) -> int:
        vs = frozenset(vars_)
        memo: dict[int, int] = {}

        def go(n: int) -> int:
            if n <= TRUE:
                return n
            r = memo.get(n)
            if r is not None:
                return r
            v = self.var_of[n]
            lo, hi = go(self.lo[n]), go(self.hi[n])
            r = self.OR(lo, hi) if v in vs else self.mk(v, lo, hi)
            memo[n] = r
            return r
        return go(f)

    def forall(self, f: int, vars_: Iterable[int]) -> int:
        return self.neg(self.exists(self.neg(f), vars_))

    def rename(self, f: int, mapping: dict[int, int]) -> int:
        memo: dict[int, int] = {}

        def go(n: int) -> int:
            if n <= TRUE:
                return n
            r = memo.get(n)
            if r is not None:
                return r
            v = self.var_of[n]
            r = self.ite(self.var(mapping.get(v, v)), go(self.hi[n]), go(self.lo[n]))
            memo[n] = r
            return r
        return go(f)

    def eval(self, f: int, assign) -> bool:
        n = f
        while n > TRUE:
            n = self.hi[n] if assign(self.var_of[n]) else self.lo[n]
        return n == TRUE

    def support(self, f: int) -> set[int]:
        out, seen, stack = set(), set(), [f]
        while stack:
            n = stack.pop()
            if n <= TRUE or n in seen:
                continue
            seen.add(n)
            out.add(self.var_of[n])
            stack += [self.lo[n], self.hi[n]]
        return out

    def nodes(self, roots: Iterable[int]) -> list[int]:
        seen, order, stack = set(), [], list(roots)
        while stack:
            n = stack.pop()
            if n in seen:
                continue
            seen.add(n)
            order.append(n)
            if n > TRUE:
                stack += [self.lo[n], self.hi[n]]
        return order

    def size(self, f: int) -> int:
        return len(self.nodes([f]))

    def satcount(self, f: int, vars_: Sequence[int]) -> int:
        level = {v: i for i, v in enumerate(sorted(vars_))}
        nv = len(level)
        memo: dict[int, int] = {}

        def lv(n: int) -> int:
            return nv if n <= TRUE else level[self.var_of[n]]

        def go(n: int) -> int:
            if n == FALSE:
                return 0
            if n == TRUE:
                return 1
            r = memo.get(n)
            if r is None:
                l = lv(n)
                r = go(self.lo[n]) * (1 << (lv(self.lo[n]) - l - 1)) + go(self.hi[n]) * (1 << (lv(self.hi[n]) - l - 1))
                memo[n] = r
            return r
        return go(f) * (1 << lv(f))

    def pick(self, f: int) -> dict[int, int] | None:
        if f == FALSE:
            return None
        out, n = {}, f
        while n > TRUE:
            if self.lo[n] != FALSE:
                out[self.var_of[n]] = 0
                n = self.lo[n]
            else:
                out[self.var_of[n]] = 1
                n = self.hi[n]
        return out

    def depth(self, f: int, stop: int | None = None) -> int:
        memo: dict[int, int] = {}

        def go(n: int) -> int:
            if n <= TRUE or (stop is not None and self.var_of[n] >= stop):
                return 0
            r = memo.get(n)
            if r is None:
                r = 1 + max(go(self.lo[n]), go(self.hi[n]))
                memo[n] = r
            return r
        return go(f)

    def gc_cache(self) -> None:
        self.cache.clear()


@dataclass
class VarBlock:
    name: str
    width: int
    vars: list[int]
    t: int = 0


class BddBackend(Backend):
    def __init__(self, bdd: BDD, blocks: dict[tuple[str, int], VarBlock]):
        self.m = bdd
        self.blocks = blocks

    def const(self, v, w):
        return [TRUE if (v >> i) & 1 else FALSE for i in range(w)]

    def var(self, name, t, w):
        blk = self.blocks.get((name, t))
        if blk is None:
            raise KeyError(f"no BDD variables allocated for {name}@{t}")
        bits = [self.m.var(v) for v in reversed(blk.vars)]
        return (bits + [FALSE] * w)[:w]

    def ext(self, x, wf, wt, signed):
        fill = x[wf - 1] if signed else FALSE
        return list(x) + [fill] * (wt - wf)

    def extract(self, x, hi, lo, w):
        return list(x[lo:hi + 1])

    def concat(self, parts):
        out = []
        for x, _ in reversed(parts):
            out += list(x)
        return out

    def _add(self, x, y, cin=FALSE):
        m = self.m
        out, c = [], cin
        for a, b in zip(x, y):
            axb = m.XOR(a, b)
            out.append(m.XOR(axb, c))
            c = m.OR(m.AND(a, b), m.AND(c, axb))
        return out, c

    def _ult(self, x, y):
        m = self.m
        lt = FALSE
        for a, b in zip(x, y):
            lt = m.ite(m.XOR(a, b), b, lt)
        return lt

    def _udivrem(self, x, y, w):
        m = self.m
        rem = [FALSE] * w
        q = [FALSE] * w
        for i in reversed(range(w)):
            rem = [x[i]] + rem[:-1]
            ge = m.neg(self._ult(rem, y))
            diff, _ = self._add(rem, [m.neg(b) for b in y], TRUE)
            rem = [m.ite(ge, d, r) for d, r in zip(diff, rem)]
            q[i] = ge
        yz = m.neg(m.or_all(y))
        q = [m.OR(yz, b) for b in q]
        rem = [m.ite(yz, a, r) for a, r in zip(x, rem)]
        return q, rem

    def arith(self, op, x, y, w, signed):
        m = self.m
        if op == "+":
            return self._add(x, y)[0]
        if op == "-":
            return self._add(x, [m.neg(b) for b in y], TRUE)[0]
        if op == "*":
            acc = [FALSE] * w
            for i in range(w):
                part = [FALSE] * i + [m.AND(y[i], b) for b in x[: w - i]]
                acc = self._add(acc, part)[0]
            return acc
        if signed:
            sx, sy = x[w - 1], y[w - 1]
            ax = [m.ite(sx, a, b) for a, b in zip(self.neg(x, w), x)]
            ay = [m.ite(sy, a, b) for a, b in zip(self.neg(y, w), y)]
            q, r = self._udivrem(ax, ay, w)
            yz = m.neg(m.or_all(y))
            if op == "/":
                nq = self.neg(q, w)
                flip = m.AND(m.XOR(sx, sy), m.neg(yz))
                res = [m.ite(flip, a, b) for a, b in zip(nq, q)]
                ones = [TRUE] * w
                one = [TRUE] + [FALSE] * (w - 1)
                dz = [m.ite(sx, a, b) for a, b in zip(one, ones)]
                return [m.ite(yz, a, b) for a, b in zip(dz, res)]
            nr = self.neg(r, w)
            res = [m.ite(sx, a, b) for a, b in zip(nr, r)]
            return [m.ite(yz, a, b) for a, b in zip(x, res)]
        q, r = self._udivrem(x, y, w)
        return q if op == "/" else r

    def bitop(self, op, x, y, w):
        f = {"&": self.m.AND, "|": self.m.OR, "^": self.m.XOR, "~^": self.m.XNOR}[op]
        return [f(a, b) for a, b in zip(x, y)]

    def bnot(self, x, w):
        return [self.m.neg(a) for a in x]

    def neg(self, x, w):
        return self._add([self.m.neg(a) for a in x], [FALSE] * w, TRUE)[0]

    def shift(self, op, x, y, w, signed):
        m = self.m
        cur = list(x)
        fill = x[w - 1] if op == ">>>" else FALSE
        big = FALSE
        for k in range(len(y)):
            amt = 1 << k
            if amt >= w:
                big = m.OR(big, y[k])
                continue
            if op == "<<":
                sh = [FALSE] * amt + cur[: w - amt]
            else:
                sh = cur[amt:] + [fill] * amt
            cur = [m.ite(y[k], a, b) for a, b in zip(sh, cur)]
        return [m.ite(big, fill, b) for b in cur]

    def cmp(self, op, x, y, w, signed):
        m = self.m
        if op in ("==", "!="):
            eq = m.and_all(m.XNOR(a, b) for a, b in zip(x, y))
            return eq if op == "==" else m.neg(eq)
        if signed:
            x = x[:-1] + [m.neg(x[-1])]
            y = y[:-1] + [m.neg(y[-1])]
        if op == "<":
            return self._ult(x, y)
        if op == ">":
            return self._ult(y, x)
        if op == "<=":
            return m.neg(self._ult(y, x))
        return m.neg(self._ult(x, y))

    def b_not(self, a):
        return self.m.neg(a)

    def b_and(self, xs):
        return self.m.and_all(xs)

    def b_or(self, xs):
        return self.m.or_all(xs)

    def b_iff(self, a, b):
        return self.m.XNOR(a, b)

    def b_true(self):
        return TRUE

    def b_false(self):
        return FALSE

    def ite(self, c, x, y, w):
        return [self.m.ite(c, a, b) for a, b in zip(x, y)]

    def to_bool(self, x, w):
        return self.m.or_all(x)

    def from_bool(self, b):
        return [b]

    def popcount(self, x, w, wo):
        acc = [FALSE] * wo
        for b in x:
            acc = self._add(acc, [b] + [FALSE] * (wo - 1))[0]
        return acc


@dataclass
class Levelized:
    var: list[int]
    child: list[tuple[int, int]]
    index: dict[int, int]
    depth: int


def levelize(bdd: BDD, roots: Sequence[int], var_pos: dict[int, int] | None = None) -> Levelized:
    # Terminals become self-loops, so a walk of exactly `depth` steps lands on 0/1 without branching.
    order = [FALSE, TRUE] + [n for n in sorted(bdd.nodes(roots)) if n > TRUE]
    index = {n: i for i, n in enumerate(order)}
    var, child = [], []
    for n in order:
        if n <= TRUE:
            var.append(0)
            child.append((index[n], index[n]))
        else:
            v = bdd.var_of[n]
            var.append(var_pos[v] if var_pos is not None else v)
            child.append((index[bdd.lo[n]], index[bdd.hi[n]]))
    depth = max([bdd.depth(r) for r in roots] + [0])
    return Levelized(var, child, index, depth)
