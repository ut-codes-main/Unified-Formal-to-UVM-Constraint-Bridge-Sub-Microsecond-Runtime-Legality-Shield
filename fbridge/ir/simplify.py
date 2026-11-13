from __future__ import annotations

from .ast import FALSE, TRUE, Binary, Const, Expr, Inside, Ite, Range, Schema, Unary, Var, _rebuild, walk
from .evaluate import evaluate, holds
from .semantics import SemanticsError


def _closed(e: Expr, schema: Schema) -> bool:
    for n in walk(e):
        if isinstance(n, Var) and (n.name in schema.fields or n.name not in schema.consts):
            return False
    return True


def _truth(e: Expr) -> bool | None:
    if e == TRUE:
        return True
    if e == FALSE:
        return False
    return None


def simplify(e: Expr, schema: Schema) -> Expr:
    def go(n: Expr) -> Expr:
        if isinstance(n, (Const, Var)):
            return n
        n = _rebuild(n, go)
        if _closed(n, schema):
            try:
                lw_bool = isinstance(n, (Binary, Unary, Inside)) and (
                    (isinstance(n, Binary) and n.op in ("==", "!=", "<", "<=", ">", ">=", "&&", "||", "->", "<->"))
                    or (isinstance(n, Unary) and n.op == "!") or isinstance(n, Inside))
                if lw_bool:
                    return TRUE if holds(n, schema, {}) else FALSE
                from .semantics import Lowerer, PyBackend
                w, s = Lowerer(schema, PyBackend({})).selfdet(n)
                return Const(evaluate(n, schema, {}), w, s)
            except SemanticsError:
                return n
        if isinstance(n, Unary) and n.op == "!":
            t = _truth(n.a)
            if t is not None:
                return FALSE if t else TRUE
            if isinstance(n.a, Unary) and n.a.op == "!":
                return n.a.a
        if isinstance(n, Binary):
            ta, tb = _truth(n.a), _truth(n.b)
            if n.op == "&&":
                if ta is False or tb is False:
                    return FALSE
                if ta:
                    return n.b
                if tb:
                    return n.a
            elif n.op == "||":
                if ta or tb:
                    return TRUE
                if ta is False:
                    return n.b
                if tb is False:
                    return n.a
            elif n.op == "->":
                if ta is False or tb:
                    return TRUE
                if ta:
                    return n.b
                if tb is False:
                    return Unary("!", n.a)
        if isinstance(n, Ite):
            t = _truth(n.cond)
            if t is not None:
                return n.then if t else n.other
        if isinstance(n, Inside):
            items = tuple(i for i in n.items if not (isinstance(i, Range) and _closed(i.lo, schema) and _closed(i.hi, schema)
                                                     and evaluate(i.lo, schema, {}) > evaluate(i.hi, schema, {})))
            if not items:
                return FALSE
            return Inside(n.a, items)
        return n
    return go(e)
