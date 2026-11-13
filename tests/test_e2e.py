import importlib.util
import json
import random
from pathlib import Path

from fbridge.shield.compile import compile_shield
from fbridge.shield.inputs import load_shield_spec
from fbridge.shield.runtime import ShieldRuntime, initial_states
from fbridge.sync.cli import main as sync_main

ROOT = Path(__file__).resolve().parents[1]
AXI = ROOT / "examples" / "axi_lite_csr"
MESI = ROOT / "examples" / "mesi_coherence"


def _load(path: Path, name: str):
    spec = importlib.util.spec_from_file_location(name, path)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


def test_single_source_roundtrip_is_equivalent(tmp_path):
    assert sync_main(["gen", "--spec", str(AXI / "spec" / "axil.fbr"), "--map", str(AXI / "formal" / "mapping.yaml"),
                      "--out", str(tmp_path / "gen")]) == 0
    rc = sync_main(["check", "--uvm", str(tmp_path / "gen" / "axil_item.sv"), "--sva", str(tmp_path / "gen" / "axil_item_env_assumes.sv"),
                    "--map", str(AXI / "formal" / "mapping.yaml"), "--spec", str(AXI / "spec" / "axil.fbr"),
                    "--out", str(tmp_path / "audit"), "--fail-on", "warning"])
    assert rc == 0
    assert json.loads((tmp_path / "audit" / "audit.json").read_text())["verdict"] == "EQUIVALENT"


def test_handwritten_collateral_drifts(tmp_path):
    rc = sync_main(["check", "--uvm", str(AXI / "tb" / "axil_item.sv"), "--sva", str(AXI / "formal" / "axil_env_assumes.sv"),
                    "--map", str(AXI / "formal" / "mapping.yaml"), "--out", str(tmp_path)])
    assert rc == 1


def test_mesi_fuzz_demo_shield_eliminates_illegal_actions(tmp_path):
    demo = _load(MESI / "fuzz_demo.py", "fuzz_demo")
    comp = compile_shield(load_shield_spec(MESI / "shield.yaml"))
    rt = ShieldRuntime(comp, tmp_path)
    raw = demo.run(rt, 3000, False, 1)
    safe = demo.run(rt, 3000, True, 1)
    assert raw["illegal_rate"] > 0.5
    assert safe["illegal"] == 0 and safe["issued"] > raw["issued"]
    assert safe["states_visited"] >= raw["states_visited"]
    assert all(st["line"] == 3 and st["excl"] == 1 for st in safe["formally_unreachable_visits"])


def test_axil_shield_runtime_repairs_random_stimulus(tmp_path):
    comp = compile_shield(load_shield_spec(AXI / "shield.yaml"))
    rt = ShieldRuntime(comp, tmp_path)
    rng = random.Random(2)
    s = initial_states(comp)[0]
    for _ in range(2000):
        tx = rng.getrandbits(comp.spec.action_bits)
        st, rep = rt.project(s, tx)
        assert st in (0, 1) and rt.is_action_legal(s, rep)
        s = rt.step_action(s, rep)
        if rng.random() < 0.5:
            s = rt.step_env(s, rng.randrange(rt.num_env))
        assert rt.is_state_reachable(s)
