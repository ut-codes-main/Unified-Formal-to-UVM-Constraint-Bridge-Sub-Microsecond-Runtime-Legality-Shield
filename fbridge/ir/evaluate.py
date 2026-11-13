from __future__ import annotations

from typing import Mapping, Sequence

from .ast import Expr, Schema
from .semantics import Lowerer, PyBackend


def _env(env):
    if isinstance(env, Mapping):
        return env
    trace: Sequence[Mapping[str, int]] = env

    def lookup(name: str, t: int) -> int:
        if 0 <= t < len(trace):
            return trace[t].get(name, 0)
        return 0
    return lookup


def evaluate(e: Expr, schema: Schema, env, t: int = 0) -> int:
    lw = Lowerer(schema, PyBackend(_env(env)))
    w, s = lw.selfdet(e)
    return lw.bv(e, t, w, s)


def holds(e: Expr, schema: Schema, env, t: int = 0) -> bool:
    return bool(Lowerer(schema, PyBackend(_env(env))).bool(e, t))
