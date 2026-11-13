import random

import z3

from fbridge.ir import (
    Binary, Concat, Const, Dist, DistItem, Field, Func, Inside, Ite, Past, Range, Rule, Schema, Slice, Unary, Var,
    evaluate, from_json, holds, temporal_span, to_json, to_sv,
)
from fbridge.ir.smt import Encoder, check, unsat_core


def schema():
    s = Schema()
    s.add(Field("a", 8))
    s.add(Field("b", 8))
    s.add(Field("c", 4))
    s.add(Field("sa", 8, signed=True))
    s.add(Field("sb", 8, signed=True))
    return s


OPS = ["+", "-", "*", "/", "%", "&", "|", "^", "~^", "<<", ">>", ">>>", "==", "!=", "<", "<=", ">", ">=", "&&", "||", "->"]


def rand_expr(rng, depth):
    if depth == 0 or rng.random() < 0.25:
        if rng.random() < 0.6:
            return Var(rng.choice(["a", "b", "c", "sa", "sb"]))
        w = rng.choice([1, 3, 8, 32])
        return Const(rng.randrange(0, 1 << min(w, 9)), w, w == 32)
    k = rng.random()
    if k < 0.55:
        return Binary(rng.choice(OPS), rand_expr(rng, depth - 1), rand_expr(rng, depth - 1))
    if k < 0.7:
        return Unary(rng.choice(["!", "~", "-", "&r", "|r", "^r"]), rand_expr(rng, depth - 1))
    if k < 0.8:
        return Ite(rand_expr(rng, depth - 1), rand_expr(rng, depth - 1), rand_expr(rng, depth - 1))
    if k < 0.88:
        return Slice(Var(rng.choice(["a", "b", "sa"])), rng.randrange(4, 8), rng.randrange(0, 4))
    if k < 0.94:
        return Inside(rand_expr(rng, depth - 1), (Const(3), Range(Const(10), Const(40))))
    return Concat((Var("c"), Slice(Var("a"), 3, 0)))


def test_python_and_z3_semantics_agree():
    rng = random.Random(7)
    s = schema()
    for _ in range(300):
        e = rand_expr(rng, 3)
        env = {n: rng.randrange(0, 1 << s.width(n)) for n in s.fields}
        enc = Encoder(s)
        x = enc.bv(e)
        subs = [(enc.var(n), z3.BitVecVal(v, s.width(n))) for n, v in env.items()]
        zval = z3.simplify(z3.substitute(x, *subs)).as_long()
        assert zval == evaluate(e, s, env), (to_sv(e), env)
        zb = z3.is_true(z3.simplify(z3.substitute(enc.bool(e), *subs)))
        assert zb == holds(e, s, env), (to_sv(e), env)


def test_context_width_keeps_carry():
    s = schema()
    e = Binary("==", Binary("+", Var("a"), Var("b")), Const(256, 9, False))
    assert holds(e, s, {"a": 200, "b": 56})
    e8 = Binary("==", Binary("+", Var("a"), Var("b")), Const(0, 8, False))
    assert holds(e8, s, {"a": 200, "b": 56})


def test_signed_compare():
    s = schema()
    assert holds(Binary("<", Var("sa"), Var("sb")), s, {"sa": 0xFF, "sb": 1})
    assert not holds(Binary("<", Var("sa"), Var("b")), s, {"sa": 0xFF, "b": 1})


def test_temporal_trace():
    s = schema()
    e = Func("$rose", (Slice(Var("a"), 0, 0),))
    trace = [{"a": 0}, {"a": 1}, {"a": 1}]
    assert [holds(e, s, trace, t) for t in range(3)] == [False, True, False]
    assert holds(Binary("==", Past(Var("a")), Const(0)), s, trace, 1)
    assert temporal_span(Binary("&&", Past(Var("a"), 2), Func("$stable", (Var("b"),)))) == (-2, 0)


def test_json_roundtrip_and_printer():
    e = Binary("->", Binary("==", Var("c"), Const(2, 4, False)),
               Dist(Var("a"), (DistItem(Const(0), 1), DistItem(Range(Const(1), Const(9)), 3, False))))
    assert from_json(to_json(e)) == e
    assert to_sv(e) == "c == 4'd2 -> a dist {0 := 1, [1:9] :/ 3}"
    assert to_sv(Binary("&&", Binary("||", Var("a"), Var("b")), Var("c"))) == "(a || b) && c"


def test_unsat_core_and_unroll():
    s = schema()
    enc = Encoder(s)
    named = {
        "lo": enc.bool(Binary(">", Var("a"), Const(10))),
        "hi": enc.bool(Binary("<", Var("a"), Const(5))),
        "free": enc.bool(Binary("==", Var("b"), Const(1))),
    }
    assert unsat_core(named) == ["hi", "lo"]
    r = Rule("stable_b", Binary("->", Var("c"), Func("$stable", (Var("b"),))))
    assert len(enc.unroll(r, 4)) == 3
    res, m = check(*enc.unroll(r, 4))
    assert res == z3.sat
