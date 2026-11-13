import importlib


def test_package_imports():
    for mod in ["fbridge", "fbridge.ir", "fbridge.frontends", "fbridge.backends",
                "fbridge.sync", "fbridge.shield", "fbridge.eco", "fbridge.cex"]:
        importlib.import_module(mod)
