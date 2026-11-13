from __future__ import annotations

import re
from dataclasses import dataclass, field
from functools import lru_cache
from pathlib import Path

from lark import Lark, Token, Transformer, v_args
from lark.exceptions import LarkError

from ..ir.ast import (
    TRUE, Binary, Concat, Const, Dist, DistItem, Expr, Func, Inside, Ite, Range, Schema, Slice,
    Unary, Var, conj, disj, shift_time,
)
from ..ir.evaluate import evaluate

GRAMMAR = Path(__file__).with_name("sv.lark")


class ParseError(Exception):
    pass


@lru_cache(maxsize=None)
def _parser(start: str) -> Lark:
    return Lark(GRAMMAR.read_text(), start=start, parser="lalr", maybe_placeholders=True)


def parse_number(text: str) -> Const:
    t = text.replace("_", "").replace(" ", "")
    if "'" not in t:
        return Const(int(t), 32, True)
    size, rest = t.split("'", 1)
    if rest in ("0", "1", "x", "X", "z", "Z"):
        return Const(1 if rest == "1" else 0, 1, False)
    signed = rest[0] in "sS"
    if signed:
        rest = rest[1:]
    base = {"b": 2, "o": 8, "d": 10, "h": 16}[rest[0].lower()]
    digits = re.sub(r"[xXzZ?]", "0", rest[1:])
    v = int(digits, base)
    width = int(size) if size else 32
    return Const(v, width, signed)


BIN = {
    "||": "||", "&&": "&&", "|": "|", "^": "^", "~^": "~^", "^~": "~^", "&": "&",
    "==": "==", "!=": "!=", "===": "==", "!==": "!=", "==?": "==", "!=?": "!=",
    "<": "<", "<=": "<=", ">": ">", ">=": ">=",
    "<<": "<<", ">>": ">>", "<<<": "<<<", ">>>": ">>>",
    "+": "+", "-": "-", "*": "*", "/": "/", "%": "%",
}
UN = {"!": "!", "~": "~", "-": "-", "+": "+", "&": "&r", "|": "|r", "^": "^r", "~&": "~&r", "~|": "~|r", "~^": "~^r", "^~": "~^r"}


@dataclass
class SeqElem:
    expr: Expr
    rep: tuple[int, int] = (1, 1)


@dataclass
class Seq:
    first_delay: tuple[int, int] | None
    elems: list[SeqElem]
    delays: list[tuple[int, int]]


@dataclass
class Prop:
    kind: str
    seq: Seq | None = None
    rhs: "Prop | None" = None
    op: str = ""


@dataclass
class PropertySpec:
    clock: Expr | None
    edge: str | None
    disable: Expr | None
    prop: Prop


@dataclass
class FbrField:
    kind: str
    width: int
    signed: bool
    name: str
    enum: list[tuple[str, Expr | None]] = field(default_factory=list)


@dataclass
class FbrItem:
    name: str
    fields: list[FbrField]


@dataclass
class FbrRule:
    name: str
    soft: bool
    guard: Expr | None
    exprs: list[Expr]
    line: int = 0


@dataclass
class FbrProtocol:
    name: str
    spec: PropertySpec
    line: int = 0


@dataclass
class FbrConst:
    name: str
    expr: Expr


class _ToAst(Transformer):
    def __init__(self, consts: dict[str, int] | None = None):
        super().__init__()
        self.consts = consts or {}

    def _fold(self, e: Expr) -> int | None:
        if isinstance(e, Const):
            return e.value
        try:
            s = Schema()
            for k, v in self.consts.items():
                s.consts[k] = Const(v, 32, True)
            return evaluate(e, s, {})
        except Exception:
            return None

    def _binchain(self, items):
        items = [i for i in items]
        out = items[0]
        i = 1
        while i < len(items):
            op = str(items[i])
            out = Binary(BIN[op], out, items[i + 1])
            i += 2
        return out

    lor = land = bor = bxor = band = eq = shift = add = mul = _binchain

    def rel(self, items):
        return self._binchain(items)

    def unary(self, items):
        return Unary(UN[str(items[0])], items[1])

    def implies(self, items):
        return Binary("->", items[0], items[1])

    def iff(self, items):
        return Binary("<->", items[0], items[1])

    def ite(self, items):
        return Ite(*items)

    def inside(self, items):
        a = items[0]
        its = next(i for i in items[1:] if isinstance(i, list))
        return Inside(a, tuple(its))

    def dist(self, items):
        a = items[0]
        its = next(i for i in items[1:] if isinstance(i, list))
        return Dist(a, tuple(its))

    def items(self, items):
        return list(items)

    def ditems(self, items):
        return list(items)

    def ditem(self, items):
        item, op, w = items
        wv = self._fold(w)
        if wv is None:
            raise ParseError("dist weight must be constant")
        return DistItem(item, wv, str(op) == ":=")

    def range(self, items):
        lo, hi = items
        if isinstance(hi, Token):
            hi = Const(0xFFFFFFFF, 32, False)
        return Range(lo, hi)

    def number(self, items):
        text = str(items[0])
        if text == "'1":
            return Unary("-", Const(1, 1, False))
        return parse_number(text)

    def ident(self, items):
        names = [str(t) for t in items]
        if names[0] == "this" and len(names) > 1:
            names = names[1:]
        return Var(".".join(names))

    def call(self, items):
        name = str(items[0])
        args = tuple(items[1]) if items[1] is not None else ()
        if name == "$past":
            n = 1
            if len(args) > 1:
                nv = self._fold(args[1])
                if nv is None:
                    raise ParseError("$past depth must be constant")
                n = nv
            return shift_time(args[0], -n)
        if name == "$bits":
            raise ParseError("$bits is not supported in constraint expressions")
        return Func(name, args)

    def call0(self, items):
        return Func(str(items[0]), ())

    def arglist(self, items):
        return list(items)

    def concat(self, items):
        parts = items[0]
        return parts[0] if len(parts) == 1 else Concat(tuple(parts))

    def replicate(self, items):
        n = self._fold(items[0])
        if n is None:
            raise ParseError("replication count must be constant")
        parts = tuple(items[1]) * n
        return parts[0] if len(parts) == 1 else Concat(parts)

    def _index(self, base: Expr, idx: Expr, width: int = 1) -> Expr:
        v = self._fold(idx)
        if v is not None:
            return Slice(base, v + width - 1, v)
        sh = Binary(">>", base, idx)
        return Binary("&", sh, Const((1 << width) - 1, width, False))

    def bitsel(self, items):
        return self._index(items[0], items[1])

    def partsel(self, items):
        hi, lo = self._fold(items[1]), self._fold(items[2])
        if hi is None or lo is None:
            raise ParseError("part-select bounds must be constant")
        return Slice(items[0], hi, lo)

    def upsel(self, items):
        w = self._fold(items[2])
        if w is None:
            raise ParseError("indexed part-select width must be constant")
        return self._index(items[0], items[1], w)

    def downsel(self, items):
        w = self._fold(items[2])
        if w is None:
            raise ParseError("indexed part-select width must be constant")
        return self._index(items[0], Binary("-", items[1], Const(w - 1)), w)

    def delay_fixed(self, items):
        n = int(str(items[0]))
        return (n, n)

    def delay_range(self, items):
        lo = int(str(items[0]))
        hi_t = str(items[1])
        if hi_t == "$":
            raise ParseError("unbounded delay ##[n:$] is not supported in bounded projection")
        return (lo, int(hi_t))

    def rep(self, items):
        lo = int(str(items[0]))
        hi = int(str(items[1])) if items[1] is not None else lo
        return (lo, hi)

    def seq_elem(self, items):
        return SeqElem(items[0], items[1] or (1, 1))

    def seq(self, items):
        first = items[0]
        rest = items[1:]
        elems, delays = [rest[0]], []
        for i in range(1, len(rest), 2):
            delays.append(rest[i])
            elems.append(rest[i + 1])
        return Seq(first, elems, delays)

    def prop_impl(self, items):
        s, op, rhs = items
        return Prop("impl", s, _as_prop(rhs), str(op))

    def prop_not(self, items):
        return Prop("not", rhs=_as_prop(items[0]))

    def clocking(self, items):
        return (str(items[0]) if items[0] is not None else None, items[1])

    def disable_iff(self, items):
        return items[0]

    def property_spec(self, items):
        clk, dis, p = items
        edge, ce = clk if clk is not None else (None, None)
        return PropertySpec(ce, edge, dis, _as_prop(p))

    def fbr(self, items):
        return list(items)

    def const_decl(self, items):
        return FbrConst(str(items[0]), items[1])

    def dim(self, items):
        hi, lo = int(str(items[0])), int(str(items[1]))
        return abs(hi - lo) + 1

    def scalar_type(self, items):
        _, sign, width = items
        return ("scalar", width or 1, str(sign) == "signed" if sign is not None else False, [])

    def enum_item(self, items):
        return (str(items[0]), items[1])

    def enum_type(self, items):
        width = items[0]
        members = list(items[1:])
        if width is None:
            width = max(1, (len(members) - 1).bit_length())
        return ("enum", width, False, members)

    def field_decl(self, items):
        kind, ty, name = items
        _, width, signed, enum = ty
        return FbrField(str(kind) if kind is not None else "rand", width, signed, str(name), enum)

    def item_decl(self, items):
        return FbrItem(str(items[0]), list(items[1:]))

    def body_one(self, items):
        return [items[0]]

    def body_many(self, items):
        return list(items)

    def rule_decl(self, items):
        soft, name, guard, body = items
        return FbrRule(str(name), soft is not None, guard, body, name.line)

    def protocol_decl(self, items):
        return FbrProtocol(str(items[0]), items[1], items[0].line)


def _as_prop(x) -> Prop:
    if isinstance(x, Prop):
        return x
    if isinstance(x, Seq):
        return Prop("seq", x)
    raise ParseError(f"unexpected property node {x!r}")


def _run(start: str, text: str, consts: dict[str, int] | None):
    try:
        tree = _parser(start).parse(text)
    except LarkError as ex:
        raise ParseError(f"{start}: {ex}") from None
    return _ToAst(consts).transform(tree)


def parse_expr(text: str, consts: dict[str, int] | None = None) -> Expr:
    return _run("expr", text, consts)


def parse_property(text: str, consts: dict[str, int] | None = None) -> PropertySpec:
    return _run("property_spec", text, consts)


def parse_fbr(text: str, consts: dict[str, int] | None = None) -> list:
    return _run("fbr", text, consts)


class PropertyLoweringError(Exception):
    pass


def _seq_alternatives(seq: Seq, max_alts: int = 64) -> list[tuple[Expr, int]]:
    alts: list[tuple[list[Expr], int]] = [([], 0)]
    for i, el in enumerate(seq.elems):
        if el.rep[0] < 1:
            raise PropertyLoweringError("empty repetition [*0] is not supported")
        dlo, dhi = (seq.first_delay or (0, 0)) if i == 0 else seq.delays[i - 1]
        nxt = []
        for terms, end in alts:
            for d in range(dlo, dhi + 1):
                start = end + d
                for r in range(el.rep[0], el.rep[1] + 1):
                    ts = list(terms) + [shift_time(el.expr, start + k) for k in range(r)]
                    nxt.append((ts, start + r - 1))
        alts = nxt
        if len(alts) > max_alts:
            raise PropertyLoweringError("sequence expands to too many alternatives")
    return [(conj(ts) if ts else TRUE, end) for ts, end in alts]


def lower_property(p: Prop) -> Expr:
    if p.kind == "seq":
        return disj([e for e, _ in _seq_alternatives(p.seq)])
    if p.kind == "not":
        return Unary("!", lower_property(p.rhs))
    alts = _seq_alternatives(p.seq)
    parts = []
    for ante, end in alts:
        offset = end + (1 if p.op == "|=>" else 0)
        parts.append(Binary("->", ante, shift_time(lower_property(p.rhs), offset)))
    return conj(parts)


def lower_spec(spec: PropertySpec) -> tuple[Expr, Expr | None]:
    return lower_property(spec.prop), spec.disable
