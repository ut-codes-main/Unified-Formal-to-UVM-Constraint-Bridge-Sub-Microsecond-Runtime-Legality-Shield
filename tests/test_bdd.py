import itertools
import random

from fbridge.bdd import BDD, FALSE, TRUE, BddBackend, VarBlock, levelize
from fbridge.ir import Binary, Const, Var, evaluate, holds
from fbridge.ir.semantics import Lowerer

from test_ir import rand_expr, schema


def blocks_for(bdd, s):
    blocks = {}
    for f in s.fields.values():
        vs = [bdd.add_var(f"{f.name}[{i}]") for i in reversed(range(f.width))]
        blocks[(f.name, 0)] = VarBlock(f.name, f.width, vs)
    return blocks


def assign_fn(blocks, env):
    lookup = {}
    for (name, _), blk in blocks.items():
        for k, v in enumerate(blk.vars):
            lookup[v] = (env[name] >> (blk.width - 1 - k)) & 1
    return lambda v: lookup[v]


def test_bdd_backend_matches_python_semantics():
    rng = random.Random(11)
    s = schema()
    for _ in range(150):
        e = rand_expr(rng, 3)
        bdd = BDD()
        blocks = blocks_for(bdd, s)
        lw = Lowerer(s, BddBackend(bdd, blocks))
        w, sg = lw.selfdet(e)
        bits = lw.bv(e, 0, w, sg)
        root = lw.bool(e, 0)
        for _ in range(12):
            env = {n: rng.randrange(0, 1 << s.width(n)) for n in s.fields}
            fn = assign_fn(blocks, env)
            got = sum(int(bdd.eval(b, fn)) << i for i, b in enumerate(bits))
            assert got == evaluate(e, s, env)
            assert bdd.eval(root, fn) == holds(e, s, env)


def test_quantify_rename_count_pick():
    bdd = BDD(4)
    x0, x1, x2, x3 = (bdd.var(i) for i in range(4))
    f = bdd.AND(bdd.OR(x0, x1), bdd.XOR(x2, x3))
    assert bdd.satcount(f, range(4)) == 6
    assert bdd.exists(f, [2, 3]) == bdd.OR(x0, x1)
    assert bdd.forall(f, [0]) == bdd.AND(x1, bdd.XOR(x2, x3))
    g = bdd.rename(bdd.AND(x0, bdd.neg(x1)), {0: 3, 1: 2})
    assert g == bdd.AND(x3, bdd.neg(x2))
    p = bdd.pick(f)
    assert bdd.eval(f, lambda v: p.get(v, 0))
    assert bdd.pick(FALSE) is None


def test_levelized_fixed_depth_walk_is_exact():
    bdd = BDD(6)
    xs = [bdd.var(i) for i in range(6)]
    f = bdd.or_all([bdd.AND(xs[0], xs[3]), bdd.AND(bdd.neg(xs[1]), xs[5]), bdd.XOR(xs[2], xs[4])])
    lv = levelize(bdd, [f])
    root = lv.index[f]
    for bits in itertools.product([0, 1], repeat=6):
        n = root
        for _ in range(lv.depth):
            n = lv.child[n][bits[lv.var[n]]]
        assert (n == 1) == bdd.eval(f, lambda v: bits[v])
    assert lv.child[0] == (0, 0) and lv.child[1] == (1, 1)


def test_dag_sharing_does_not_explode():
    s = schema()
    e = Var("a")
    for _ in range(40):
        e = Binary("+", e, e)
    bdd = BDD()
    blocks = blocks_for(bdd, s)
    lw = Lowerer(s, BddBackend(bdd, blocks))
    root = lw.bool(Binary("==", e, Const(0, 8, False)), 0)
    assert root == TRUE
