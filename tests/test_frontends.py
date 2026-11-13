from pathlib import Path

import pytest
import z3

from fbridge.backends.sva_emit import emit_assumes
from fbridge.backends.uvm_emit import emit_item_class
from fbridge.frontends.fbr_dsl import load_fbr, load_single_source
from fbridge.frontends.slang_util import syntax_errors
from fbridge.frontends.sva_assume import load_sva, parse_sva
from fbridge.frontends.svparse import ParseError, lower_spec, parse_expr, parse_property
from fbridge.frontends.uvm_constraints import load_uvm_item, parse_uvm_items
from fbridge.ir import Schema, Field, conj, holds, to_sv
from fbridge.ir.smt import Encoder
from fbridge.mapping import load_mapping

EX = Path(__file__).resolve().parents[1] / "examples" / "axi_lite_csr"


@pytest.mark.parametrize("src,expected", [
    ("addr[1:0] == 2'b00", "addr[1:0] == 2'd0"),
    ("kind == WRITE -> strb != 0", "kind == WRITE -> strb != 0"),
    ("a dist { 0 := 1, [4:8] :/ 2 }", "a dist {0 := 1, [4:8] :/ 2}"),
    ("{a, b[3:0]} == {2{c}}", "{a, b[3:0]} == {c, c}"),
    ("x[4 +: 4] != '1", "x[7:4] != '1"),
    ("this.addr < 16'h1_000", "addr < 16'h1000"),
])
def test_expression_roundtrip(src, expected):
    assert to_sv(parse_expr(src)) == expected


def test_unbased_fill_matches_context():
    s = Schema()
    s.add(Field("x", 8))
    assert holds(parse_expr("x == '1"), s, {"x": 0xFF})
    assert not holds(parse_expr("x == '1"), s, {"x": 0x7F})


def test_property_lowering_ranges_and_reps():
    e, dis = lower_spec(parse_property("@(posedge clk) disable iff (!rst_n) a ##1 b[*2] |=> ##[1:2] c"))
    assert to_sv(dis) == "!rst_n"
    s = Schema()
    for n in "abc":
        s.add(Field(n))
    trace = [{"a": 1}, {"b": 1}, {"b": 1}, {}, {"c": 1}]
    assert holds(e, s, trace, 0)
    trace[4]["c"] = 0
    assert not holds(e, s, trace, 0)


def test_unbounded_delay_rejected():
    with pytest.raises(Exception):
        lower_spec(parse_property("a |-> ##[1:$] b"))


def test_bad_syntax_raises():
    with pytest.raises(ParseError):
        parse_expr("a + + ")


def test_uvm_frontend_extracts_rules():
    it = load_uvm_item(EX / "tb" / "axil_item.sv")
    sch = it.cset.schema
    assert sch.fields["kind"].enum == (("AXIL_READ", 0), ("AXIL_WRITE", 1))
    assert sch.fields["addr"].width == 32 and sch.fields["resp"].kind == "state"
    names = [r.name for r in it.cset.rules]
    assert "c_rd_strb[0]" in names and "c_rd_strb[1]" in names
    assert it.cset.rule("c_full").soft
    assert it.solve_before == [("kind", "strb")]
    assert to_sv(it.cset.rule("c_rd_strb[1]").body()) == "kind == AXIL_READ -> data == 32'd0"


def test_uvm_frontend_nested_and_unique():
    src = """
    class t extends uvm_sequence_item;
      rand bit [3:0] a, b; rand bit c;
      constraint k { if (c) { a < 3; if (b > 2) a != 0; } else a == b; unique {a, b}; foreach (q[i]) q[i] < 2; }
    endclass
    """
    it = parse_uvm_items(text=src)[0]
    exprs = [to_sv(r.body()) for r in it.cset.rules]
    assert "c -> a < 3" in exprs
    assert "c && b > 2 -> a != 0" in exprs
    assert "!c -> a == b" in exprs
    assert "a != b" in exprs
    assert any("LoopConstraint" in w for w in it.warnings)


def test_sva_frontend_named_props_and_defaults():
    src = """
    module m(input logic clk, rst_n, input logic [7:0] d, e);
      default disable iff (!rst_n);
      property p_d; @(posedge clk) d != 0 |-> e == d; endproperty
      a1: assume property (p_d);
      assume property (@(posedge clk) d == 1 |=> ##2 e == 0);
      assert property (@(posedge clk) d < 9);
    endmodule
    """
    u = parse_sva(text=src)[0]
    assert [r.name for r in u.cset.rules] == ["a1", "assume_L6"]
    assert u.cset.schema.fields["e"].width == 8 and u.cset.schema.fields["rst_n"].width == 1
    assert to_sv(u.cset.rules[0].disable) == "!rst_n"
    u2 = parse_sva(text=src, kinds=("assert",))[0]
    assert len(u2.cset.rules) == 1


def test_fbr_and_emitters_roundtrip():
    ss = load_single_source(EX / "spec" / "axil.fbr")
    assert ss.cset.rule("write_strobe").guard is not None
    assert len(ss.protocols) == 3
    cls = emit_item_class(ss.cset)
    assert syntax_errors(cls) == []
    re_item = parse_uvm_items(text=cls)[0]
    enc_a, enc_b = Encoder(ss.cset.schema), Encoder(re_item.cset.schema)
    a = conj([r.body() for r in ss.cset.hard()])
    b = conj([r.body() for r in re_item.cset.hard()])
    s = z3.Solver()
    s.add(enc_a.bool(a) != enc_b.bool(b))
    assert s.check() == z3.unsat
    m = load_mapping(EX / "formal" / "mapping.yaml")
    em = emit_assumes(ss.cset, m, ss.protocols)
    assert syntax_errors(em.text) == []
    assert "as_write_strobe__write" in em.text and "as_write_strobe__read" not in em.text
    assert any("read_idle_payload" in w for w in em.warnings)
    back = parse_sva(text=em.text)[0]
    assert len(back.cset.rules) == sum(len(v) for v in em.emitted.values())


def test_fbr_requires_item_first():
    with pytest.raises(ValueError):
        load_fbr(text="rule r: a == 1;")


def test_hand_written_sva_example_parses():
    u = load_sva(EX / "formal" / "axil_env_assumes.sv")
    assert len(u.cset.rules) == 12 and u.clock == "clk" and not u.warnings
