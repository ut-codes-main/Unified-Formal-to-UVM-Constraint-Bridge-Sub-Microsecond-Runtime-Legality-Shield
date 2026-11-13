import importlib.util
import shutil
from pathlib import Path

import pytest

from fbridge.cex.cli import main as cex_main
from fbridge.cex.emit_seq import SeqOptions, emit_sequence, field_constraint
from fbridge.cex.lift import FieldLift, lift
from fbridge.cex.monitor import assemble, load_monitor
from fbridge.cex.vcd import VcdError, load_waveform, parse_vcd, write_vcd
from fbridge.frontends.slang_util import syntax_errors
from fbridge.frontends.uvm_constraints import load_uvm_item, parse_uvm_items

EX = Path(__file__).resolve().parents[1] / "examples" / "axi_lite_csr"
RTL = [EX / "rtl" / "axil_csr.sv"]
PROP = "@(posedge clk) disable iff (!rst_n) dma_busy |-> dma_cnt <= {1'b0, DMA_MAX}"


def _trace_module():
    spec = importlib.util.spec_from_file_location("make_cex_trace", EX / "formal" / "make_cex_trace.py")
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


@pytest.fixture(scope="module")
def trace(tmp_path_factory):
    mod = _trace_module()
    cycles = mod.simulate(mod.scenario())
    path = tmp_path_factory.mktemp("cex") / "trace.vcd"
    write_vcd(path, "axil_csr", mod.SIGNALS, cycles)
    return path, cycles, mod


def test_committed_trace_matches_generator(trace):
    path, _, _ = trace
    assert (EX / "formal" / "cex_dma_len.vcd").read_text() == path.read_text()


def test_vcd_roundtrip_and_sampling(trace):
    path, cycles, mod = trace
    wf = load_waveform(path)
    assert wf.width("s_axi_awaddr") == 32 and wf.resolve("dma_cnt") == "axil_csr.dma_cnt"
    sampled = wf.sample(list(mod.SIGNALS), clock="clk")
    assert len(sampled) == len(cycles)
    for got, want in zip(sampled, cycles):
        assert all(got[k] == want[k] for k in mod.SIGNALS)


def test_vcd_parser_aliases_xz_and_reals():
    text = """$timescale 1ps $end
$scope module top $end
$var wire 1 ! clk $end
$var wire 4 " bus $end
$var wire 4 " bus_alias $end
$var real 64 # r $end
$scope module sub $end
$var reg 1 $ q $end
$upscope $end
$upscope $end
$enddefinitions $end
$dumpvars
0!
bxx01 "
r2.5 #
x$
$end
#5
1!
#10
0!
b1111 "
1$
#15
1!
"""
    wf = parse_vcd(text)
    assert wf.resolve("bus_alias") == "top.bus_alias" and wf.resolve("q") == "top.sub.q"
    assert wf.value_before("bus", 5) == (1, True)
    assert wf.value_before("bus_alias", 15) == (15, False)
    assert wf.edges("clk") == [5, 15]
    assert wf.sample(["bus", "q", "r"], clock="clk") == [{"bus": 1, "q": 0, "r": 2}, {"bus": 15, "q": 1, "r": 2}]
    with pytest.raises(VcdError):
        wf.resolve("missing")


def test_monitor_assembles_transactions(trace):
    path, cycles, _ = trace
    mon = load_monitor("axi4_lite")
    txns = assemble(mon, cycles)
    assert [(t.kind, t.issue_cycle, t.item["addr"]) for t in txns] == [
        ("write", 3, 0x10), ("write", 5, 0x0), ("read", 7, 0x4), ("write", 9, 0x28), ("write", 12, 0x2C)]
    assert txns[3].item["strb"] == 0x3 and txns[3].observed == {"resp": 0}
    assert txns[2].observed["rdata"] == 0
    assert load_monitor("axi4").channels["w"].beats


def test_lift_keeps_minimal_transactions_and_bits(trace):
    path, _, _ = trace
    item = load_uvm_item(EX / "tb" / "axil_item.sv")
    res = lift(load_waveform(path), load_monitor("axi4_lite"), RTL, "axil_csr", PROP, item.cset)
    assert res.fail_cycle == 13
    kept = res.kept()
    assert [t.txn.item["addr"] for t in kept] == [0x0, 0x28, 0x2C]
    by_addr = {t.txn.item["addr"]: t for t in kept}
    assert by_addr[0x28].fields["data"].mask == 0xFFF
    assert by_addr[0x2C].fields["data"].mask == 0x1
    assert by_addr[0x28].fields["strb"].mask == 0 and by_addr[0x2C].fields["prot"].mask == 0
    assert all(t.legal for t in kept) and not res.warnings
    assert [t.idle_before for t in kept] == [3, 3, 2]


def test_keep_timing_retains_backpressure_writes(trace):
    path, _, _ = trace
    res = lift(load_waveform(path), load_monitor("axi4_lite"), RTL, "axil_csr", PROP, keep_timing=True)
    assert [t.txn.item["addr"] for t in res.kept()] == [0x10, 0x0, 0x28, 0x2C]


def test_lift_flags_constraints_blocking_reproduction(trace, tmp_path):
    path, _, _ = trace
    src = (EX / "tb" / "axil_item.sv").read_text().replace(
        "constraint c_window   { addr < CSR_SPAN; }", "constraint c_window   { addr < CSR_SPAN; }\n  constraint c_no_dma_len { addr != 32'h28; }")
    item = parse_uvm_items(text=src, class_name="axil_item")[0]
    res = lift(load_waveform(path), load_monitor("axi4_lite"), RTL, "axil_csr", PROP, item.cset)
    blocked = [t for t in res.kept() if not t.legal]
    assert len(blocked) == 1 and blocked[0].disabled_constraints == ["c_no_dma_len"]
    seq = emit_sequence(res, SeqOptions("cex_dma", "axil_item"), item.cset.schema)
    assert "req.c_no_dma_len.constraint_mode(0);" in seq
    assert "WARNING" in seq


def test_emitted_sequence_is_valid_sv(trace):
    path, _, _ = trace
    item = load_uvm_item(EX / "tb" / "axil_item.sv")
    res = lift(load_waveform(path), load_monitor("axi4_lite"), RTL, "axil_csr", PROP, item.cset)
    seq = emit_sequence(res, SeqOptions("cex_dma_len", "axil_item", source="trace.vcd"), item.cset.schema)
    assert syntax_errors(seq) == []
    assert "data[11:0] == 12'h900" in seq and "data[0] == 1'd1" in seq and "kind == AXIL_WRITE" in seq
    assert "dropped #0 write @ cycle 3" in seq


def test_field_constraint_forms():
    assert field_constraint(FieldLift("d", 0xA5, 0xF0, 8), "d", None, {}) == "d[7:4] == 4'hA"
    assert field_constraint(FieldLift("d", 0xA5, 0x81, 8), "d", None, {}) == "(d & 8'h81) == 8'h81"
    assert field_constraint(FieldLift("d", 0xA5, 0, 8), "d", None, {}) is None
    assert field_constraint(FieldLift("k", "WRITE", -1, 0), "k", None, {"WRITE": "MY_WR"}) == "k == MY_WR"


def test_property_that_holds_is_rejected(trace):
    path, _, _ = trace
    with pytest.raises(ValueError):
        lift(load_waveform(path), load_monitor("axi4_lite"), RTL, "axil_csr", "@(posedge clk) dma_cnt <= 13'h1FFF")


def test_cli_end_to_end(tmp_path):
    rc = cex_main(["--vcd", str(EX / "formal" / "cex_dma_len.vcd"), "--monitor", "axi4_lite", "--rtl", str(RTL[0]), "--top", "axil_csr",
                   "--assert-file", str(RTL[0]), "--assert-label", "ap_dma_len_bound", "--define", "FORMAL",
                   "--uvm", str(EX / "tb" / "axil_item.sv"), "--name", "cex_dma_len", "--out", str(tmp_path)])
    assert rc == 0
    seq = (tmp_path / "cex_dma_len_seq.sv").read_text()
    assert "class cex_dma_len_seq extends uvm_sequence #(axil_item);" in seq
    assert (tmp_path / "cex_dma_len_lift.json").exists()


@pytest.mark.skipif(shutil.which("fst2vcd") is not None, reason="fst2vcd available")
def test_fst_requires_converter(tmp_path):
    p = tmp_path / "x.fst"
    p.write_bytes(b"\x00")
    with pytest.raises(VcdError):
        load_waveform(p)
