from __future__ import annotations

from .ast import Binary, Concat, Const, Dist, Expr, Func, Inside, Ite, Next, Past, Range, Slice, Unary, Var

PREC = {
    "->": 1, "<->": 1,
    "||": 3, "&&": 4,
    "|": 5, "^": 6, "~^": 6, "&": 7,
    "==": 8, "!=": 8, "===": 8, "!==": 8,
    "<": 9, "<=": 9, ">": 9, ">=": 9,
    "<<": 10, ">>": 10, "<<<": 10, ">>>": 10,
    "+": 11, "-": 11,
    "*": 12, "/": 12, "%": 12,
}
ASSOC = {"||", "&&", "|", "&", "^", "+", "*"}
P_ITE, P_INSIDE, P_UNARY, P_PRIMARY = 2, 9, 14, 16
UNARY_TXT = {"&r": "&", "|r": "|", "^r": "^", "~&r": "~&", "~|r": "~|", "~^r": "~^"}


def fmt_const(c: Const) -> str:
    if c.width == 32 and c.signed:
        v = c.value - (1 << 32) if c.value >> 31 else c.value
        return str(v)
    if c.width == 1:
        return f"1'b{c.value}"
    if c.value < 10:
        return f"{c.width}'d{c.value}"
    return f"{c.width}'h{c.value:X}"


def prec(e: Expr) -> int:
    if isinstance(e, Binary):
        return PREC[e.op]
    if isinstance(e, Ite):
        return P_ITE
    if isinstance(e, (Inside, Dist)):
        return P_INSIDE
    if isinstance(e, Unary):
        return P_UNARY
    return P_PRIMARY


def _item(it) -> str:
    if isinstance(it, Range):
        return f"[{to_sv(it.lo)}:{to_sv(it.hi)}]"
    return to_sv(it)


def _wrap(e: Expr, need: int, strict: bool = False) -> str:
    p = prec(e)
    s = to_sv(e)
    return f"({s})" if p < need or (strict and p == need) else s


def to_sv(e: Expr) -> str:
    if isinstance(e, Const):
        return fmt_const(e)
    if isinstance(e, Var):
        return e.name
    if isinstance(e, Unary):
        op = UNARY_TXT.get(e.op, e.op)
        return f"{op}{_wrap(e.a, P_UNARY)}"
    if isinstance(e, Binary):
        p = PREC[e.op]
        left = _wrap(e.a, p, strict=e.op in ("->", "<->"))
        assoc_ok = e.op in ASSOC and isinstance(e.b, Binary) and e.b.op == e.op
        right = to_sv(e.b) if assoc_ok else _wrap(e.b, p, strict=e.op not in ("->", "<->"))
        if e.op in ("&&", "||") and isinstance(e.a, Binary) and e.a.op in ("&&", "||") and e.a.op != e.op:
            left = f"({to_sv(e.a)})"
        return f"{left} {e.op} {right}"
    if isinstance(e, Ite):
        return f"{_wrap(e.cond, P_ITE + 1)} ? {_wrap(e.then, P_ITE + 1)} : {_wrap(e.other, P_ITE)}"
    if isinstance(e, Slice):
        base = _wrap(e.a, P_PRIMARY)
        return f"{base}[{e.hi}]" if e.hi == e.lo else f"{base}[{e.hi}:{e.lo}]"
    if isinstance(e, Concat):
        return "{" + ", ".join(to_sv(p) for p in e.parts) + "}"
    if isinstance(e, Inside):
        return f"{_wrap(e.a, P_INSIDE + 1)} inside {{{', '.join(_item(i) for i in e.items)}}}"
    if isinstance(e, Dist):
        parts = [f"{_item(d.item)} {':=' if d.per_value else ':/'} {d.weight}" for d in e.items]
        return f"{_wrap(e.a, P_INSIDE + 1)} dist {{{', '.join(parts)}}}"
    if isinstance(e, Past):
        return f"$past({to_sv(e.a)})" if e.n == 1 else f"$past({to_sv(e.a)}, {e.n})"
    if isinstance(e, Next):
        return f"nexttime[{e.n}] ({to_sv(e.a)})"
    if isinstance(e, Func):
        return f"{e.name}({', '.join(to_sv(a) for a in e.args)})"
    raise TypeError(e)
