from __future__ import annotations

from dataclasses import dataclass, field, fields, is_dataclass
from typing import Callable, Iterator, Union

UNARY_OPS = ("!", "~", "-", "+", "&r", "|r", "^r", "~&r", "~|r", "~^r")
ARITH_OPS = ("+", "-", "*", "/", "%")
BITWISE_OPS = ("&", "|", "^", "~^")
SHIFT_OPS = ("<<", ">>", "<<<", ">>>")
COMPARE_OPS = ("==", "!=", "<", "<=", ">", ">=", "===", "!==")
LOGIC_OPS = ("&&", "||", "->", "<->")
BINARY_OPS = ARITH_OPS + BITWISE_OPS + SHIFT_OPS + COMPARE_OPS + LOGIC_OPS
FUNCS = ("$countones", "$onehot", "$onehot0", "$stable", "$rose", "$fell", "$changed", "$clog2", "$signed", "$unsigned", "$isunknown")


class Expr:
    __slots__ = ()

    def children(self) -> tuple["Expr", ...]:
        return ()

    def __and__(self, other: "Expr") -> "Expr":
        return Binary("&&", self, other)

    def __or__(self, other: "Expr") -> "Expr":
        return Binary("||", self, other)

    def __invert__(self) -> "Expr":
        return Unary("!", self)


@dataclass(frozen=True)
class Const(Expr):
    value: int
    width: int = 32
    signed: bool = True

    def __post_init__(self):
        mask = (1 << self.width) - 1
        object.__setattr__(self, "value", self.value & mask)


@dataclass(frozen=True)
class Var(Expr):
    name: str


@dataclass(frozen=True)
class Unary(Expr):
    op: str
    a: Expr

    def children(self):
        return (self.a,)


@dataclass(frozen=True)
class Binary(Expr):
    op: str
    a: Expr
    b: Expr

    def children(self):
        return (self.a, self.b)


@dataclass(frozen=True)
class Ite(Expr):
    cond: Expr
    then: Expr
    other: Expr

    def children(self):
        return (self.cond, self.then, self.other)


@dataclass(frozen=True)
class Slice(Expr):
    a: Expr
    hi: int
    lo: int

    def children(self):
        return (self.a,)


@dataclass(frozen=True)
class Concat(Expr):
    parts: tuple[Expr, ...]

    def children(self):
        return self.parts


@dataclass(frozen=True)
class Range:
    lo: Expr
    hi: Expr


Item = Union[Expr, Range]


@dataclass(frozen=True)
class Inside(Expr):
    a: Expr
    items: tuple[Item, ...]

    def children(self):
        out = [self.a]
        for it in self.items:
            out.extend((it.lo, it.hi) if isinstance(it, Range) else (it,))
        return tuple(out)


@dataclass(frozen=True)
class DistItem:
    item: Item
    weight: int
    per_value: bool = True


@dataclass(frozen=True)
class Dist(Expr):
    a: Expr
    items: tuple[DistItem, ...]

    def children(self):
        return Inside(self.a, tuple(d.item for d in self.items)).children()

    def support(self) -> Inside:
        return Inside(self.a, tuple(d.item for d in self.items if d.weight != 0))


@dataclass(frozen=True)
class Past(Expr):
    a: Expr
    n: int = 1

    def children(self):
        return (self.a,)


@dataclass(frozen=True)
class Next(Expr):
    a: Expr
    n: int = 1

    def children(self):
        return (self.a,)


@dataclass(frozen=True)
class Func(Expr):
    name: str
    args: tuple[Expr, ...]

    def children(self):
        return self.args


TRUE = Const(1, 1, False)
FALSE = Const(0, 1, False)


@dataclass(frozen=True)
class Field:
    name: str
    width: int = 1
    signed: bool = False
    kind: str = "rand"
    enum: tuple[tuple[str, int], ...] = ()

    @property
    def mask(self) -> int:
        return (1 << self.width) - 1


@dataclass
class Schema:
    fields: dict[str, Field] = field(default_factory=dict)
    consts: dict[str, Const] = field(default_factory=dict)

    def add(self, f: Field) -> Field:
        self.fields[f.name] = f
        for name, val in f.enum:
            self.consts[name] = Const(val, f.width, False)
        return f

    def width(self, name: str) -> int:
        return self.fields[name].width

    def __contains__(self, name: str) -> bool:
        return name in self.fields

    def merged(self, other: "Schema") -> "Schema":
        s = Schema(dict(self.fields), dict(self.consts))
        for f in other.fields.values():
            s.fields.setdefault(f.name, f)
        for k, v in other.consts.items():
            s.consts.setdefault(k, v)
        return s


@dataclass(frozen=True)
class Origin:
    file: str = ""
    line: int = 0
    text: str = ""


@dataclass
class Rule:
    name: str
    expr: Expr
    kind: str = "constraint"
    soft: bool = False
    origin: Origin = field(default_factory=Origin)
    guard: Expr | None = None
    disable: Expr | None = None

    def body(self) -> Expr:
        e = self.expr
        if self.guard is not None:
            e = Binary("->", self.guard, e)
        return e


@dataclass
class ConstraintSet:
    name: str
    schema: Schema
    rules: list[Rule] = field(default_factory=list)
    source: str = ""

    def hard(self) -> list[Rule]:
        return [r for r in self.rules if not r.soft]

    def rule(self, name: str) -> Rule:
        for r in self.rules:
            if r.name == name:
                return r
        raise KeyError(name)


def walk(e: Expr) -> Iterator[Expr]:
    stack = [e]
    while stack:
        n = stack.pop()
        yield n
        stack.extend(reversed(n.children()))


def free_vars(e: Expr) -> set[str]:
    return {n.name for n in walk(e) if isinstance(n, Var)}


def temporal_span(e: Expr, offset: int = 0) -> tuple[int, int]:
    lo = hi = offset
    if isinstance(e, Past):
        return temporal_span(e.a, offset - e.n)
    if isinstance(e, Next):
        return temporal_span(e.a, offset + e.n)
    if isinstance(e, Func) and e.name in ("$stable", "$rose", "$fell", "$changed"):
        lo = offset - 1
    for c in e.children():
        a, b = temporal_span(c, offset)
        lo, hi = min(lo, a), max(hi, b)
    return lo, hi


def is_temporal(e: Expr) -> bool:
    return temporal_span(e) != (0, 0)


def _rebuild(e, fn: Callable[[Expr], Expr]):
    if isinstance(e, Range):
        return Range(fn(e.lo), fn(e.hi))
    if isinstance(e, DistItem):
        return DistItem(_rebuild(e.item, fn), e.weight, e.per_value)
    if not isinstance(e, Expr):
        return e
    if isinstance(e, (Const, Var)):
        return e
    kw = {}
    for f in fields(e):
        v = getattr(e, f.name)
        if isinstance(v, tuple):
            kw[f.name] = tuple(_rebuild(x, fn) if isinstance(x, (Range, DistItem)) else fn(x) if isinstance(x, Expr) else x for x in v)
        elif isinstance(v, Expr):
            kw[f.name] = fn(v)
        else:
            kw[f.name] = v
    return type(e)(**kw)


def transform(e: Expr, fn: Callable[[Expr], Expr | None]) -> Expr:
    def go(n: Expr) -> Expr:
        r = fn(n)
        if r is not None:
            return r
        return _rebuild(n, go)
    return go(e)


def substitute(e: Expr, mapping: dict[str, Expr]) -> Expr:
    return transform(e, lambda n: mapping.get(n.name) if isinstance(n, Var) else None)


def shift_time(e: Expr, n: int) -> Expr:
    if n == 0:
        return e
    return Next(e, n) if n > 0 else Past(e, -n)


def conj(es) -> Expr:
    es = [e for e in es if e != TRUE]
    if not es:
        return TRUE
    out = es[0]
    for e in es[1:]:
        out = Binary("&&", out, e)
    return out


def disj(es) -> Expr:
    es = [e for e in es if e != FALSE]
    if not es:
        return FALSE
    out = es[0]
    for e in es[1:]:
        out = Binary("||", out, e)
    return out


def const_value(e: Expr, schema: Schema | None = None) -> int | None:
    if isinstance(e, Const):
        return e.value
    if isinstance(e, Var) and schema is not None and e.name in schema.consts:
        return schema.consts[e.name].value
    return None


_KIND = {cls.__name__: cls for cls in (Const, Var, Unary, Binary, Ite, Slice, Concat, Inside, Dist, Past, Next, Func)}


def to_json(e):
    if isinstance(e, Range):
        return {"range": [to_json(e.lo), to_json(e.hi)]}
    if isinstance(e, DistItem):
        return {"item": to_json(e.item), "weight": e.weight, "per_value": e.per_value}
    if isinstance(e, tuple):
        return [to_json(x) for x in e]
    if is_dataclass(e):
        d = {"k": type(e).__name__}
        for f in fields(e):
            v = getattr(e, f.name)
            d[f.name] = to_json(v) if isinstance(v, (Expr, tuple, Range, DistItem)) else v
        return d
    return e


def from_json(d):
    if isinstance(d, list):
        return tuple(from_json(x) for x in d)
    if not isinstance(d, dict):
        return d
    if "range" in d:
        return Range(from_json(d["range"][0]), from_json(d["range"][1]))
    if "item" in d and "weight" in d:
        return DistItem(from_json(d["item"]), d["weight"], d["per_value"])
    cls = _KIND[d["k"]]
    return cls(**{k: from_json(v) for k, v in d.items() if k != "k"})


def schema_to_json(s: Schema) -> dict:
    return {
        "fields": [{"name": f.name, "width": f.width, "signed": f.signed, "kind": f.kind, "enum": [list(x) for x in f.enum]} for f in s.fields.values()],
        "consts": {k: {"value": v.value, "width": v.width} for k, v in s.consts.items()},
    }


def schema_from_json(d: dict) -> Schema:
    s = Schema()
    for f in d["fields"]:
        s.add(Field(f["name"], f["width"], f["signed"], f["kind"], tuple(tuple(x) for x in f["enum"])))
    for k, v in d.get("consts", {}).items():
        s.consts[k] = Const(v["value"], v["width"], False)
    return s
