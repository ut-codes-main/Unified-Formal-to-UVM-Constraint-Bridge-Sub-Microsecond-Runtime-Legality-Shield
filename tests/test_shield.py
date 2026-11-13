import random
from pathlib import Path

import pytest

from fbridge.frontends.slang_util import syntax_errors
from fbridge.shield.bench import make_samples, run_bench
from fbridge.shield.compile import compile_shield
from fbridge.shield.inputs import load_shield_spec
from fbridge.shield.model import FIXED_FIELD_CONFLICT, LEGAL, NO_LEGAL_ACTION, REPAIRED, ShieldModel

from shield_util import CShield, oracle_legal, oracle_reach

ROOT = Path(__file__).resolve().parents[1] / "examples"
MESI = ROOT / "mesi_coherence" / "shield.yaml"
AXIL = ROOT / "axi_lite_csr" / "shield.yaml"


@pytest.fixture(scope="module")
def mesi():
    spec = load_shield_spec(MESI)
    comp = compile_shield(spec)
    return spec, comp, ShieldModel(comp)


@pytest.fixture(scope="module")
def mesi_c(mesi, tmp_path_factory):
    return CShield(mesi[1], tmp_path_factory.mktemp("mesi_c"))


@pytest.fixture(scope="module")
def axil():
    spec = load_shield_spec(AXIL)
    comp = compile_shield(spec)
    return spec, comp, ShieldModel(comp)


@pytest.fixture(scope="module")
def axil_c(axil, tmp_path_factory):
    return CShield(axil[1], tmp_path_factory.mktemp("axil_c"))


def test_reachability_matches_explicit_oracle(mesi):
    spec, comp, model = mesi
    reach = oracle_reach(spec)
    got = {s for s in range(1 << spec.state_bits) if model.is_state_reachable(s)}
    assert got == reach
    assert comp.reachable_states == len(reach) == 22
    bad = spec.pack({"line": 3, "excl": 1, "pend": 0, "credits": 3}, "state")
    assert bad not in got


def test_invariants_prune_state_space():
    spec = load_shield_spec(MESI)
    spec.invariants = []
    loose = compile_shield(spec)
    assert loose.reachable_states > 22
    s = spec.pack({"line": 3, "excl": 1, "pend": 0, "credits": 3}, "state")
    assert ShieldModel(loose).is_state_reachable(s)


def test_model_matches_expression_semantics(mesi):
    spec, comp, model = mesi
    reach = oracle_reach(spec)
    rng = random.Random(3)
    states = sorted(reach) + [rng.randrange(256) for _ in range(20)]
    for _ in range(3000):
        s = rng.choice(states)
        tx = rng.getrandbits(spec.action_bits)
        assert model.is_action_legal(s, tx) == oracle_legal(spec, reach, s, tx), (spec.unpack(s, "state"), spec.unpack(tx, "action"))
    for s, tx in make_samples(comp, 500):
        assert model.is_action_legal(s, tx) == oracle_legal(spec, reach, s, tx)


def test_table_and_bdd_walk_agree_per_class(mesi):
    spec, comp, model = mesi
    lv = comp.table
    for k, c in enumerate(comp.classes, 1):
        node = lv.index[c.node]
        for tx in range(1 << spec.action_bits):
            n = node
            for _ in range(comp.action_depth):
                n = lv.child[n][(tx >> (lv.var[n] - 64)) & 1]
            assert ((comp.bitmaps[k - 1] >> tx) & 1) == (n == 1)


def test_repair_is_always_legal_and_respects_priority(mesi):
    spec, comp, model = mesi
    rng = random.Random(5)
    reach = sorted(oracle_reach(spec))
    for _ in range(3000):
        s = rng.choice(reach)
        tx = rng.getrandbits(spec.action_bits)
        st, rep, masks = model.project_or_mask_action(s, tx)
        if model.class_of(s) == 0:
            assert st == NO_LEGAL_ACTION
            continue
        assert model.is_action_legal(s, rep)
        assert (st == LEGAL) == model.is_action_legal(s, tx)
        if st == LEGAL:
            assert rep == tx
        else:
            assert st == REPAIRED
        a = spec.unpack(rep, "action")
        for name, mask in masks.items():
            assert (mask >> a[name]) & 1


def test_field_masks_are_exact_marginals(mesi):
    spec, comp, model = mesi
    for k, c in enumerate(comp.classes, 1):
        seen = {f.name: 0 for f in comp.fields}
        for tx in range(1 << spec.action_bits):
            if (comp.bitmaps[k - 1] >> tx) & 1:
                for n, v in spec.unpack(tx, "action").items():
                    seen[n] |= 1 << v
        assert seen == c.masks


def test_immutable_fields_report_conflicts():
    spec = load_shield_spec(MESI)
    comp = compile_shield(spec, {"op"})
    model = ShieldModel(comp)
    s_m = spec.pack({"line": 3, "pend": 0, "credits": 3, "excl": 0}, "state")
    bad_op = spec.pack({"op": 0, "size": 6}, "action")
    st, rep, _ = model.project_or_mask_action(s_m, bad_op)
    assert st == FIXED_FIELD_CONFLICT
    good_op = spec.pack({"op": 3, "size": 2, "ns": 1}, "action")
    st, rep, _ = model.project_or_mask_action(s_m, good_op)
    assert st == REPAIRED and spec.unpack(rep, "action")["op"] == 3 and model.is_action_legal(s_m, rep)


def test_c_matches_model_exhaustively_on_reachable_states(mesi, mesi_c):
    spec, comp, model = mesi
    legal = mesi_c.fn("is_action_legal")
    cls = mesi_c.fn("class_of")
    reach_fn = mesi_c.fn("is_state_reachable")
    for s in range(1 << spec.state_bits):
        assert cls(s) == model.class_of(s)
        assert bool(reach_fn(s)) == model.is_state_reachable(s)
    for s in [s for s in range(1 << spec.state_bits) if model.is_state_reachable(s)]:
        for tx in range(1 << spec.action_bits):
            assert bool(legal(s, tx)) == model.is_action_legal(s, tx)
    assert not legal(1 << spec.state_bits, 0) and not legal(0, 1 << spec.action_bits)
    assert mesi_c.lib.is_action_legal(0, spec.pack({"op": 0, "size": 6}, "action")) == model.is_action_legal(0, spec.pack({"op": 0, "size": 6}, "action"))


def test_c_project_explain_and_step_match_model(mesi, mesi_c):
    spec, comp, model = mesi
    rng = random.Random(9)
    explain = mesi_c.fn("explain")
    step_a = mesi_c.fn("step_action")
    step_e = mesi_c.fn("step_env")
    offs = []
    o = 0
    for f in comp.fields:
        offs.append(o)
        o += f.mask_words
    for _ in range(5000):
        s = rng.randrange(1 << spec.state_bits)
        tx = rng.getrandbits(spec.action_bits + (1 if rng.random() < 0.05 else 0))
        st, rep, masks = mesi_c.project(s, tx)
        mst, mrep, mmasks = model.project_or_mask_action(s, tx)
        assert (st, rep) == (mst, mrep)
        for f, off in zip(comp.fields, offs):
            assert sum(masks[off + w] << (64 * w) for w in range(f.mask_words)) == mmasks[f.name]
        assert explain(s, tx) == model.explain(s, tx)
        assert step_a(s, tx) == model.step_action(s, tx)
        e = rng.randrange(-1, len(model.env_transitions()) + 1)
        assert step_e(s, e) == model.step_env(s, e)


def test_explain_names_violated_rules(mesi):
    spec, comp, model = mesi
    s = spec.pack({"line": 0, "pend": 0, "credits": 3, "excl": 0}, "state")
    tx = spec.pack({"op": 3, "size": 7, "addr_lo": 1}, "action")
    ex = model.explain(s, tx)
    names = {comp.rule_names[i] for i in range(len(comp.rule_names)) if (ex >> i) & 1}
    assert {"size_range", "natural_alignment", "wb_needs_dirty", "full_line_copyback"} <= names
    assert not (ex >> 63) & 1


def test_bdd_mode_wide_fields_and_rule_imports(axil, axil_c):
    spec, comp, model = axil
    assert comp.mode == "bdd"
    assert any(r.name.startswith("fbr:") for r in spec.legal) and any(r.name.startswith("sva:") for r in spec.legal)
    assert comp.reachable_states == 3
    reach = oracle_reach(spec)
    assert {s for s in range(8) if model.is_state_reachable(s)} == reach
    rng = random.Random(4)
    legal = axil_c.fn("is_action_legal")
    samples = make_samples(comp, 3000) + [(rng.randrange(8), rng.getrandbits(40)) for _ in range(2000)]
    for s, tx in samples:
        ref = oracle_legal(spec, reach, s, tx)
        assert model.is_action_legal(s, tx) == ref
        assert bool(legal(s, tx)) == ref
        st, rep, _ = axil_c.project(s, tx)
        assert (st, rep) == model.project_or_mask_action(s, tx)[:2]
        if st in (LEGAL, REPAIRED):
            assert oracle_legal(spec, reach, s, rep)


def test_wide_field_intervals_cover_all_legal_values(axil, axil_c):
    spec, comp, model = axil
    ffi = axil_c.ffi
    lo, hi = ffi.new("shield_u64[64]"), ffi.new("shield_u64[64]")
    addr_id = [f.name for f in comp.fields].index("addr")
    for s in range(8):
        n = axil_c.fn("field_intervals")(s, addr_id, lo, hi, 64)
        if model.class_of(s) == 0:
            assert n == 0
            continue
        ivs = [(lo[i], hi[i]) for i in range(n)]
        for s2, tx in make_samples(comp, 400):
            if s2 == s and model.is_action_legal(s, tx):
                a = spec.unpack(tx, "action")["addr"]
                assert any(x <= a <= y for x, y in ivs)


def test_generated_sv_parses(mesi_c, axil_c):
    for c in (mesi_c, axil_c):
        for key in ("sv_pkg", "sv_item"):
            assert syntax_errors(c.art.paths[key].read_text()) == []


def test_latency_under_one_microsecond(mesi, tmp_path):
    res = run_bench(mesi[1], tmp_path / "bench", rounds=20000, samples=1024)
    assert res["is_action_legal"]["p99_ns"] < 1000
    assert res["project_or_mask_action"]["p99_ns"] < 1000
