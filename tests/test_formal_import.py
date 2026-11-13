import itertools
from pathlib import Path

import pytest
import z3

from fbridge.ir import Field, Schema, holds
from fbridge.shield.formal_import import (
    FormalImportError, load_aiger, load_btor2, load_smt2, parse_aiger, aig_to_facts, z3_to_expr,
)
from fbridge.shield.inputs import SpecError, load_shield_spec

EX = Path(__file__).resolve().parents[1] / "examples" / "mesi_coherence"


def sch(widths):
    s = Schema()
    for n, w in widths.items():
        s.add(Field(n, w))
    return s


def test_aiger_ascii_invariant():
    f = load_aiger(EX / "formal" / "inv_wb.aag")
    assert f.widths == {"pend_q": 3, "line_q": 2}
    s = sch(f.widths)
    for pend, line in itertools.product(range(8), range(4)):
        assert holds(f.expr(), s, {"pend_q": pend, "line_q": line}) == (pend != 4 or line == 3)


def _varint(x):
    out = bytearray()
    while x >= 0x80:
        out.append((x & 0x7F) | 0x80)
        x >>= 7
    out.append(x)
    return bytes(out)


def test_aiger_binary_matches_ascii():
    ascii_aig = parse_aiger((EX / "formal" / "inv_wb.aag").read_bytes())
    body = b"aig 9 5 0 1 4\n19\n"
    for lhs in sorted(ascii_aig.ands):
        r0, r1 = ascii_aig.ands[lhs]
        body += _varint(lhs - r0) + _varint(r0 - r1)
    body += b"i0 pend_q[0]\ni1 pend_q[1]\ni2 pend_q[2]\ni3 line_q[0]\ni4 line_q[1]\no0 inv\n"
    bin_facts = aig_to_facts(parse_aiger(body), "bin")
    asc_facts = aig_to_facts(ascii_aig, "ascii")
    s = sch(asc_facts.widths)
    for pend, line in itertools.product(range(8), range(4)):
        env = {"pend_q": pend, "line_q": line}
        assert holds(bin_facts.expr(), s, env) == holds(asc_facts.expr(), s, env)


def test_btor2_bad_is_negated():
    f = load_btor2(EX / "formal" / "inv_credit.btor2")
    s = sch(f.widths)
    for pend, cr in itertools.product(range(8), range(4)):
        assert holds(f.expr(), s, {"pend_q": pend, "credits_q": cr}) == (pend != 0 or cr == 3)


def test_btor2_signed_and_ext_ops():
    txt = """
    1 sort bitvec 4
    2 sort bitvec 8
    3 sort bitvec 1
    4 input 1 a
    5 sext 2 4 4
    6 constd 2 -3
    7 slt 3 5 6
    8 uext 2 4 4
    9 consth 2 0f
    10 ulte 3 8 9
    11 and 3 7 10
    12 output 11
    """
    f = load_btor2(text=txt)
    s = sch(f.widths)
    for a in range(16):
        sa = a - 16 if a >= 8 else a
        assert holds(f.expr(), s, {"a": a}) == (sa < -3)


def test_btor2_rejects_arrays():
    with pytest.raises(FormalImportError):
        load_btor2(text="1 sort array 2 2\n")


def test_smt2_roundtrip_against_z3():
    f = load_smt2(EX / "formal" / "inv_excl.smt2")
    s = sch(f.widths)
    for line, ex in itertools.product(range(4), range(2)):
        assert holds(f.expr(), s, {"cache_line_q": line, "excl_mon_q": ex}) == (not (line == 3 and ex == 1))


def test_z3_converter_signed_shift_and_div():
    a, b = z3.BitVecs("a b", 6)
    exprs = [a >> 2, a / b, a % b, z3.UDiv(a, b), z3.LShR(a, b), z3.SignExt(2, a) < z3.ZeroExt(2, b), z3.Extract(4, 1, a * b) == 3]
    widths = {}
    s = None
    for ze in exprs:
        e = z3_to_expr(ze if z3.is_bool(ze) else ze == 5, widths)
        s = sch(widths)
        for va in range(0, 64, 7):
            for vb in range(0, 64, 5):
                ref = z3.is_true(z3.simplify(z3.substitute(ze if z3.is_bool(ze) else ze == 5, (a, z3.BitVecVal(va, 6)), (b, z3.BitVecVal(vb, 6)))))
                assert holds(e, s, {"a": va, "b": vb}) == ref, (ze, va, vb)


def test_shield_spec_loads_and_maps_invariants():
    spec = load_shield_spec(EX / "shield.yaml")
    assert spec.state_bits == 8 and spec.action_bits == 14
    assert [f.lsb for f in spec.action] == [0, 3, 6, 12, 13]
    assert len(spec.invariants) == 3
    w = spec.pack({"op": 3, "size": 6, "addr_lo": 0, "xflag": 0, "ns": 1}, "action")
    assert spec.unpack(w, "action")["ns"] == 1 and spec.unpack(w, "action")["size"] == 6
    assert {t.kind for t in spec.transitions} == {"action", "env"}


def test_spec_rejects_unmapped_invariant(tmp_path):
    (tmp_path / "i.smt2").write_text("(declare-const foo (_ BitVec 2))\n(assert (= foo #b00))\n")
    (tmp_path / "s.yaml").write_text("state:\n  - {name: a, width: 2}\naction:\n  - {name: b, width: 1}\n"
                                     "invariants:\n  - {format: smt2, file: i.smt2}\n")
    with pytest.raises(SpecError):
        load_shield_spec(tmp_path / "s.yaml")
