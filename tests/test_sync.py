import json
from pathlib import Path

import pytest

from fbridge.backends.sva_emit import emit_assumes
from fbridge.backends.uvm_emit import emit_item_class
from fbridge.frontends.fbr_dsl import load_single_source
from fbridge.frontends.sva_assume import load_sva, parse_sva
from fbridge.frontends.uvm_constraints import load_uvm_item, parse_uvm_items
from fbridge.mapping import load_mapping
from fbridge.sync.checker import run_audit
from fbridge.sync.cli import main as sync_main

EX = Path(__file__).resolve().parents[1] / "examples" / "axi_lite_csr"


@pytest.fixture(scope="module")
def ctx():
    m = load_mapping(EX / "formal" / "mapping.yaml")
    it = load_uvm_item(EX / "tb" / "axil_item.sv")
    sva = load_sva(EX / "formal" / "axil_env_assumes.sv")
    spec = load_single_source(EX / "spec" / "axil.fbr")
    sig = m.signal_schema(it.cset.schema).merged(sva.cset.schema)
    return m, it, sva, spec, sig


def kinds(audit):
    return {(f.pair, f.kind, f.view, f.subject) for f in audit.findings}


def test_example_drift_catalogue(ctx):
    m, it, sva, spec, sig = ctx
    audit = run_audit(it.cset, sva.cset.rules, sig, m, spec.cset)
    got = kinds(audit)
    assert ("uvm<->sva", "SIM_ALLOWS_FORMAL_FORBIDS", "write", "a_no_lock_wr") in got
    assert ("uvm<->sva", "SIM_ALLOWS_FORMAL_FORBIDS", "write", "a_aw_prot") in got
    assert ("uvm<->sva", "FORMAL_ALLOWS_SIM_FORBIDS", "read", "c_reserved") in got
    assert ("spec<->sva", "SVA_MISSING_SPEC_RULE", "read", "addr_not_reserved") in got
    assert ("uvm", "REDUNDANT_CONSTRAINT", None, "c_mix") in got
    assert not any(k[1] == "UVM_MISSING_SPEC_RULE" for k in got)
    assert audit.verdict() == "DRIFT"
    prot = next(f for f in audit.findings if f.subject == "a_aw_prot" and f.pair == "uvm<->sva")
    assert prot.witness["kind"] == "AXIL_WRITE" and prot.witness["prot"] in (2, 4, 6)
    assert prot.suggestion == "constraint c_sync_a_aw_prot { kind == AXIL_WRITE -> prot == 3'd0; }"
    classes = {a.name: a.kind for a in audit.assumes}
    assert classes["a_aw_stable"] == "protocol" and classes["a_aw_align"] == "transaction"


def test_generated_pair_is_equivalent(ctx):
    m, _, _, spec, _ = ctx
    em = emit_assumes(spec.cset, m, spec.protocols)
    gen_sva = parse_sva(text=em.text)[0]
    gen_item = parse_uvm_items(text=emit_item_class(spec.cset))[0]
    sig = m.signal_schema(gen_item.cset.schema).merged(gen_sva.cset.schema)
    audit = run_audit(gen_item.cset, gen_sva.cset.rules, sig, m, spec.cset)
    blocking = [f for f in audit.findings if f.severity != "info"]
    assert blocking == []
    assert audit.verdict() == "EQUIVALENT"
    assert all(v.equivalent for v in audit.views)


def test_uvm_conflict_reports_core(ctx):
    m, _, sva, _, _ = ctx
    src = """
    typedef enum bit {AXIL_READ = 0, AXIL_WRITE = 1} axil_kind_e;
    class axil_item extends uvm_sequence_item;
      rand axil_kind_e kind; rand bit [31:0] addr; rand bit [31:0] data; rand bit [3:0] strb; rand bit [2:0] prot;
      constraint lo { addr > 32'h20; }
      constraint hi { addr < 32'h10; }
      constraint other { prot == 0; }
    endclass
    """
    it = parse_uvm_items(text=src)[0]
    sig = m.signal_schema(it.cset.schema).merged(sva.cset.schema)
    audit = run_audit(it.cset, sva.cset.rules, sig, m)
    conflicts = [f for f in audit.findings if f.kind == "UVM_CONFLICT"]
    assert conflicts and sorted(conflicts[0].related) == ["hi", "lo"]
    assert audit.verdict() == "VACUOUS"


def test_formal_vacuity_core(ctx):
    m, it, _, _, _ = ctx
    src = """
    module env(input logic clk, rst_n, s_axi_awvalid, s_axi_wvalid, s_axi_arvalid, input logic [31:0] s_axi_awaddr, s_axi_araddr);
      default disable iff (!rst_n);
      a1: assume property (@(posedge clk) s_axi_awvalid |-> s_axi_awaddr > 32'h100);
      a2: assume property (@(posedge clk) s_axi_awvalid |-> s_axi_awaddr < 32'h10);
      a3: assume property (@(posedge clk) s_axi_arvalid |-> s_axi_araddr < 32'h10);
    endmodule
    """
    u = parse_sva(text=src)[0]
    sig = m.signal_schema(it.cset.schema).merged(u.cset.schema)
    audit = run_audit(it.cset, u.cset.rules, sig, m)
    vac = [f for f in audit.findings if f.kind == "FORMAL_VACUOUS"]
    assert len(vac) == 1 and vac[0].view == "write" and sorted(vac[0].related) == ["a1", "a2"]


def test_temporal_assume_projects_through_past(ctx):
    m, it, _, _, _ = ctx
    src = """
    module env(input logic clk, rst_n, s_axi_awvalid, s_axi_wvalid, s_axi_arvalid, input logic [2:0] s_axi_awprot, input logic [31:0] s_axi_awaddr);
      default disable iff (!rst_n);
      a_hold: assume property (@(posedge clk) s_axi_awvalid |-> $past(s_axi_awprot) == s_axi_awprot);
      a_prev: assume property (@(posedge clk) s_axi_awvalid |-> $past(s_axi_awprot) == 3'd0);
    endmodule
    """
    u = parse_sva(text=src)[0]
    sig = m.signal_schema(it.cset.schema).merged(u.cset.schema)
    audit = run_audit(it.cset, u.cset.rules, sig, m)
    joint = [f for f in audit.findings if f.kind == "SIM_ALLOWS_FORMAL_FORBIDS"]
    assert {f.subject for f in joint} == {"a_hold", "a_prev"}
    assert all(f.related for f in joint)
    assert all(f.witness["prot"] != 0 for f in joint)


def test_cli_check_and_gen(tmp_path):
    rc = sync_main(["check", "--uvm", str(EX / "tb" / "axil_item.sv"), "--sva", str(EX / "formal" / "axil_env_assumes.sv"),
                    "--map", str(EX / "formal" / "mapping.yaml"), "--out", str(tmp_path / "sync")])
    assert rc == 1
    audit = json.loads((tmp_path / "sync" / "audit.json").read_text())
    assert audit["verdict"] == "DRIFT"
    ast = json.loads((tmp_path / "sync" / "unified_ast.json").read_text())
    assert ast["format"] == "fbridge.unified_ast/1" and len(ast["sva"]["rules"]) == 12
    assert "# Constraint / Assumption Equivalence Audit" in (tmp_path / "sync" / "audit.md").read_text()
    rc = sync_main(["check", "--uvm", str(EX / "tb" / "axil_item.sv"), "--sva", str(EX / "formal" / "axil_env_assumes.sv"),
                    "--map", str(EX / "formal" / "mapping.yaml"), "--out", str(tmp_path / "sync2"), "--fail-on", "never"])
    assert rc == 0
    rc = sync_main(["gen", "--spec", str(EX / "spec" / "axil.fbr"), "--map", str(EX / "formal" / "mapping.yaml"), "--out", str(tmp_path / "gen")])
    assert rc == 0
    assert (tmp_path / "gen" / "axil_item.sv").exists() and (tmp_path / "gen" / "axil_item_env_assumes.sv").exists()
