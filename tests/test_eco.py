import json
import shutil
import subprocess
from pathlib import Path

import pytest

from fbridge.eco.cli import main as eco_main
from fbridge.eco.cones import load_design, normalize
from fbridge.eco.diff import parse_unified_diff
from fbridge.eco.tracker import Certificate, evaluate, import_sby, load_certs, seal, svh_include, unreachable_bins

EX = Path(__file__).resolve().parents[1] / "examples" / "axi_lite_csr"
CERTS = ["axil_csr_cover.c_irq_without_enable", "axil_csr_cover.c_bresp_exokay", "axil_csr_cover.c_rresp_decerr"]


def git(repo, *args):
    subprocess.run(["git", "-c", "user.name=t", "-c", "user.email=t@t", *args], cwd=repo, check=True, capture_output=True)


@pytest.fixture
def repo(tmp_path):
    (tmp_path / "rtl").mkdir()
    (tmp_path / "formal").mkdir()
    shutil.copy(EX / "rtl" / "axil_csr.sv", tmp_path / "rtl" / "axil_csr.sv")
    shutil.copy(EX / "formal" / "axil_csr_cover.sv", tmp_path / "formal" / "axil_csr_cover.sv")
    shutil.copy(EX / "formal" / "sby_cover.log", tmp_path / "formal" / "sby_cover.log")
    git(tmp_path, "init", "-q")
    git(tmp_path, "add", "-A")
    git(tmp_path, "commit", "-q", "-m", "base")
    rc = eco_main(["import-sby", "--rtl", str(tmp_path / "rtl" / "axil_csr.sv"), str(tmp_path / "formal" / "axil_csr_cover.sv"),
                   "--root", str(tmp_path), "--log", str(tmp_path / "formal" / "sby_cover.log"), "--out", str(tmp_path / "index.json")])
    assert rc == 0
    return tmp_path


def edit(repo, old, new, path="rtl/axil_csr.sv"):
    p = repo / path
    text = p.read_text()
    assert old in text
    p.write_text(text.replace(old, new, 1))


def update(repo):
    out = repo / "bins.json"
    eco_main(["update", "--rtl", str(repo / "rtl" / "axil_csr.sv"), str(repo / "formal" / "axil_csr_cover.sv"), "--root", str(repo),
              "--index", str(repo / "index.json"), "--git-base", "HEAD", "--out", str(out), "--svh", str(repo / "bins.svh")])
    return json.loads(out.read_text())


def test_sby_import_builds_certificates(repo):
    certs, meta = load_certs(repo / "index.json")
    assert sorted(c.id for c in certs) == sorted(CERTS)
    rresp = next(c for c in certs if c.label == "c_rresp_decerr")
    assert "axil_csr.s_axi_rresp" in rresp.cone and "axil_csr.rd_reserved" in rresp.cone
    assert "axil_csr.irq_stat" not in rresp.cone
    assert all(c.engine == "smtbmc boolector" for c in certs)
    assert any(d["file"] == "rtl/axil_csr.sv" for d in rresp.drivers)


def test_unchanged_design_keeps_every_certificate(repo):
    res = update(repo)
    assert res["summary"] == {"certificates": 3, "unreachable": 3, "invalidated": 0}
    assert set(res["mask"]) == set(CERTS)
    assert '"axil_csr_cover.c_rresp_decerr"' in (repo / "bins.svh").read_text()


def test_eco_invalidates_only_touched_cone(repo):
    edit(repo, "s_axi_rresp  <= rd_reserved ? 2'b10 : 2'b00;", "s_axi_rresp  <= rd_reserved ? 2'b11 : 2'b00;")
    res = update(repo)
    assert res["summary"]["invalidated"] == 1
    inv = res["invalidated"][0]
    assert inv["bin"] == "axil_csr_cover.c_rresp_decerr"
    assert "axil_csr.s_axi_rresp" in inv["touched_signals"]
    assert inv["hunks"] and inv["hunks"][0]["file"] == "rtl/axil_csr.sv"
    assert set(res["mask"]) == {"axil_csr_cover.c_irq_without_enable", "axil_csr_cover.c_bresp_exokay"}


def test_formatting_only_change_invalidates_nothing(repo):
    edit(repo, "s_axi_bresp  <= (wr_reserved || (locked && waddr != A_LOCK)) ? 2'b10 : 2'b00;",
         "s_axi_bresp  <=  (wr_reserved ||  (locked && waddr != A_LOCK)) ? 2'b10 : 2'b00; // decode error on reserved")
    res = update(repo)
    assert res["summary"]["invalidated"] == 0


def test_irq_logic_eco_and_unrelated_eco(repo):
    edit(repo, "assign irq = |(irq_en & irq_stat);", "assign irq = |(irq_en & irq_stat) | dma_busy;")
    edit(repo, "A_SCRATCH1: scratch1 <= apply_strb(scratch1, s_axi_wdata, s_axi_wstrb);",
         "A_SCRATCH1: scratch1 <= apply_strb(scratch1, ~s_axi_wdata, s_axi_wstrb);")
    res = update(repo)
    assert [v["bin"] for v in res["invalidated"]] == ["axil_csr_cover.c_irq_without_enable"]
    assert "axil_csr.irq" in res["invalidated"][0]["touched_signals"]


def test_condition_change_inside_cone_is_detected(repo):
    edit(repo, "if (dma_cnt <= 13'd4) begin", "if (dma_cnt < 13'd4) begin")
    res = update(repo)
    bins = {v["bin"] for v in res["invalidated"]}
    assert "axil_csr_cover.c_irq_without_enable" in bins
    assert "axil_csr_cover.c_rresp_decerr" not in bins


def test_cover_text_change_and_removal(repo):
    edit(repo, "c_bresp_exokay:       cover property (s_axi_bvalid && s_axi_bresp == 2'b01);",
         "c_bresp_exokay:       cover property (s_axi_bvalid && s_axi_bresp == 2'b11);", "formal/axil_csr_cover.sv")
    edit(repo, "c_rresp_decerr:", "c_rresp_decerr_v2:", "formal/axil_csr_cover.sv")
    res = update(repo)
    reasons = {v["bin"]: v["reason"] for v in res["invalidated"]}
    assert reasons["axil_csr_cover.c_bresp_exokay"] == "cover property text changed"
    assert reasons["axil_csr_cover.c_rresp_decerr"] == "cover directive removed or renamed"


def test_unified_diff_parser_and_svh_ignore_bins():
    patch = """diff --git a/rtl/x.sv b/rtl/x.sv
--- a/rtl/x.sv
+++ b/rtl/x.sv
@@ -10,2 +10,3 @@ module x
@@ -40 +41,0 @@
"""
    hunks = parse_unified_diff(patch)
    assert [(h.file, h.old_start, h.old_len, h.new_start, h.new_len) for h in hunks] == [("rtl/x.sv", 10, 2, 10, 3), ("rtl/x.sv", 40, 1, 41, 0)]
    c = Certificate("a.c", "cg_csr.cp_addr.reserved", "a", "c", [], coverage={"covergroup": "cg_csr", "coverpoint": "cp_addr",
                                                                         "bin_name": "reserved", "values": "[8'h40:8'h7C]"})
    res = {"unreachable_bins": [{"bin": c.bin, "certificate": c.id}]}
    svh = svh_include(res, [c])
    assert "`define FB_IGNORE_CG_CSR_CP_ADDR ignore_bins reserved_unreach = {[8'h40:8'h7C]};" in svh


def test_normalize_strips_comments_and_whitespace():
    assert normalize("a <=  b; // x\n /* y */ c") == "a <= b; c"


def test_design_api_directly():
    d = load_design([EX / "rtl" / "axil_csr.sv", EX / "formal" / "axil_csr_cover.sv"], EX)
    certs = import_sby((EX / "formal" / "sby_cover.log").read_text(), d)
    certs = [seal(c, d, "r0") for c in certs]
    verdicts = evaluate(certs, d)
    assert all(v.valid for v in verdicts)
    out = unreachable_bins(certs, verdicts)
    assert out["summary"]["unreachable"] == 3
    assert "axil_csr.dma_cnt" in d.cone(["axil_csr_cover.dma_cnt"])
