#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
# Authors: Formal Frontier Agents
"""Negative and source-only replay tests for the fixed native API adapter.

Adapted by Hive Task hive-request-c7ca28ca844342869a863efb7f45969528a9294c
(UID 18f200b6-23a9-4db1-a379-74a5b9db4cb8) from the accepted
FormalFrontier/finite-group-tate-cohomology test at
61577f7cf2e02715f621a724aa692921ab6bbad9, authored by worker-b Task
hive-request-381dc6f93292eb39ea2d5b25f09baacdc8b20d9e (UID
cd8c84f8-2dbf-4399-9c70-1de364ffa99f), with PolynomialRootStability
95ac896f81a3190b2634a4246a3e924d2a267a61 / Anchor
f0c8c34386109116e4912fb425a8ad15d9dc42a4 lineage.
"""

if not __debug__:
    raise SystemExit("optimized Python is not supported for API tests")

import argparse
import copy
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest


ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "scripts"))
import generate_api as api


PARSER = argparse.ArgumentParser(description=__doc__)
PARSER.add_argument("--native-data", type=Path, required=True)
PARSER.add_argument("--second-native-data", type=Path)


class NativeReferenceTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.original = {module: (ARGS.native_data / ("declaration-data-" + module + ".bmp")).read_bytes()
                        for module in api.MODULES}
        cls.records = {module: json.loads(raw) for module, raw in cls.original.items()}
        cls.sources = {path: (ROOT / path).read_bytes() for path in api.SOURCE_INPUT_SHA256}

    def corrupt(self, change, diagnostic):
        records = copy.deepcopy(self.records)
        sources = dict(self.sources)
        change(records, sources)
        raw = {module: json.dumps(record, ensure_ascii=False).encode("utf-8")
               if record != self.records[module] else self.original[module]
               for module, record in records.items()}
        with self.assertRaisesRegex(ValueError, diagnostic):
            api.validate(records, raw, sources, api.SOURCE)

    def test_real_native_records_and_generated_output(self):
        markdown, manifest_raw = api.render(self.records, self.original, self.sources, api.SOURCE)
        self.assertEqual((ROOT / "docs/API.md").read_bytes(), markdown)
        self.assertEqual((ROOT / "docs/api-manifest.json").read_bytes(), manifest_raw)
        manifest = json.loads(manifest_raw)
        self.assertEqual(len(manifest["production_declarations"]), 66)
        self.assertEqual(len(manifest["client_and_local_declarations"]), 8)
        self.assertEqual(manifest["undocumented_count"], 25)
        self.assertTrue(all(not value for value in manifest["native_instance_tables"].values()))
        self.assertIn("Subgroup.le_ker_of_mapsTo_centeredArc", manifest["production_declarations"])
        self.assertIn("RestrictedProduct.punitBicharacter", manifest["client_and_local_declarations"])
        self.assertIn("RestrictedProduct.zmodBicharacter", manifest["client_and_local_declarations"])
        self.assertIn("RestrictedProduct.zmodTwoTopologicalSpaceNaturality",
                      manifest["client_and_local_declarations"])
        self.assertIn("RestrictedProduct.zmodTwoDiscreteTopologyNaturality",
                      manifest["client_and_local_declarations"])
        self.assertNotIn(b"forgejo.vpn", markdown + manifest_raw)
        self.assertNotIn(b"zulip.vpn", markdown + manifest_raw)
        self.assertFalse(manifest["proof_certification"] or manifest["release_acceptance"])
        if ARGS.second_native_data:
            self.assertEqual(self.original, {module: (ARGS.second_native_data /
                             ("declaration-data-" + module + ".bmp")).read_bytes()
                             for module in api.MODULES})

    def test_missing_extra_duplicate_kind_name_module_source_line(self):
        compact = api.MODULES[0]
        controls = [
            ("missing/extra native declaration", lambda records, sources:
             records[compact]["declarations"].pop()),
            ("missing/extra native declaration", lambda records, sources:
             records[compact]["declarations"].append(copy.deepcopy(records[compact]["declarations"][0]))),
            ("duplicate native declaration", lambda records, sources:
             records[compact]["declarations"].__setitem__(1, copy.deepcopy(records[compact]["declarations"][0]))),
            ("native module name differs", lambda records, sources:
             records[compact].__setitem__("name", "Other")),
            ("wrong native name/kind", lambda records, sources:
             records[compact]["declarations"][0]["info"].__setitem__("kind", "axiom")),
            ("wrong native name/kind", lambda records, sources:
             records[compact]["declarations"][0]["info"].__setitem__("name", "Mathlib.other")),
            ("native source module/revision/path differs", lambda records, sources:
             records[compact]["declarations"][0]["info"].__setitem__(
                 "sourceLink", "https://example.invalid/commit/main/CompactStage.lean")),
            ("native self link differs", lambda records, sources:
             records[compact]["declarations"][0]["info"].__setitem__("docLink", "./other.html#name")),
            ("missing/extra/wrong native instance table", lambda records, sources:
             records[compact]["instances"].append({"name": "bogus", "className": "Bogus", "typeNames": []})),
            ("missing/extra/wrong native instance table", lambda records, sources:
             records[compact]["instances"].extend([
                 {"name": "duplicate", "className": "Bogus", "typeNames": []}] * 2)),
            ("native source docstring position differs", lambda records, sources:
             records[compact]["declarations"][0]["info"].__setitem__("line", 1)),
        ]
        for diagnostic, change in controls:
            with self.subTest(diagnostic=diagnostic):
                self.corrupt(change, diagnostic)
        def swap_source_name(records, sources):
            info = records[compact]["declarations"][0]["info"]
            info["name"] = "RestrictedProduct.unrelated"
            info["docLink"] = "./RestrictedProductDuality/CompactStage.html#RestrictedProduct.unrelated"
        self.corrupt(swap_source_name, "native source/name position differs")

    def test_active_html_docstring_and_missing_implicit_binder(self):
        compact = api.MODULES[0]
        for fragment in ("<script>alert(1)</script>", "<img src='x'>",
                         "<a href='javascript:evil'>x</a>", "<span onclick='evil'>x</span>",
                         "<div><span></div>"):
            with self.subTest(fragment=fragment):
                self.corrupt(lambda records, sources: records[compact]["declarations"][0]
                             .__setitem__("header", fragment), "native header")
        self.corrupt(lambda records, sources: records[compact]["declarations"][0]["info"]
                     .__setitem__("doc", "<script>alert(1)</script>"),
                     "active/unsupported native docstring")
        for module, name, old, new in (
            (compact, "RestrictedProduct.exists_subset_cofiniteStage", "u_2", "u_9"),
            (api.MODULES[4], "RestrictedProduct.pontryaginDualEquiv", "Finite", "Infinite"),
            (api.MODULES[5], "RestrictedProduct.symmetricPontryaginDualEquiv", "Finite", "Infinite"),
            (api.MODULES[6], "RestrictedProduct.toPontryaginDual_natural", "u_5", "u_9"),
        ):
            with self.subTest(name=name):
                def remove_binder(records, sources):
                    row = next(row for row in records[module]["declarations"]
                               if row["info"]["name"] == name)
                    self.assertIn(old, row["header"])
                    row["header"] = row["header"].replace(old, new, 1)
                self.corrupt(remove_binder, "missing signature binder")

    def test_native_bytes_source_inputs_revision_and_optimizer(self):
        module = api.MODULES[0]
        tampered = dict(self.original)
        tampered[module] += b" "
        with self.assertRaisesRegex(ValueError, "native raw record differs from pinned tool/input"):
            api.validate(self.records, tampered, self.sources, api.SOURCE)
        self.corrupt(lambda records, sources: records[module]["declarations"][0]["info"]
                     .__setitem__("doc", "Invented source comment"),
                     "native docstring/source mismatch")
        for path in self.sources:
            with self.subTest(path=path):
                changed = dict(self.sources)
                changed[path] += b"\n"
                with self.assertRaisesRegex(ValueError, "source/pin drift from accepted input"):
                    api.check_snapshot(api.SOURCE, changed)
        with self.assertRaisesRegex(ValueError, "source/pin inventory differs"):
            api.check_snapshot(api.SOURCE, {**self.sources, "extra.lean": b""})
        with self.assertRaisesRegex(ValueError, "unexpected/stale analyzed source revision"):
            api.check_snapshot("main", self.sources)
        with tempfile.TemporaryDirectory() as temporary:
            result = subprocess.run([sys.executable, "-O", str(ROOT / "scripts/generate_api.py"),
                                     "--native-data", temporary, "--source-revision", api.SOURCE,
                                     "--docgen-revision", api.TOOL],
                                    capture_output=True, text=True, check=False)
            self.assertNotEqual(result.returncode, 0)
            self.assertIn("optimized Python is not supported", result.stderr)
            self.assertFalse(list(Path(temporary).iterdir()))

    def test_extra_native_record_refused(self):
        with tempfile.TemporaryDirectory() as temporary:
            for module, raw in self.original.items():
                (Path(temporary) / ("declaration-data-" + module + ".bmp")).write_bytes(raw)
            (Path(temporary) / "declaration-data-Unapproved.Extra.bmp").write_bytes(b"{}")
            command = [sys.executable, "-B", str(ROOT / "scripts/generate_api.py"),
                       "--native-data", temporary, "--source-revision", api.SOURCE,
                       "--docgen-revision", api.TOOL, "--check"]
            for missing in (False, True):
                with self.subTest(missing=missing):
                    if missing:
                        (Path(temporary) / "declaration-data-Unapproved.Extra.bmp").unlink()
                        (Path(temporary) / ("declaration-data-" + api.MODULES[0] + ".bmp")).unlink()
                    result = subprocess.run(command, capture_output=True, text=True, check=False)
                    self.assertNotEqual(result.returncode, 0)
                    self.assertIn("missing/extra native record file", result.stderr)

    def test_source_only_archive_without_git_executable_and_stale_output(self):
        with tempfile.TemporaryDirectory() as temporary:
            archive = Path(temporary) / "source-archive"
            (archive / "scripts").mkdir(parents=True)
            (archive / "docs").mkdir()
            for path, raw in self.sources.items():
                target = archive / path
                target.parent.mkdir(parents=True, exist_ok=True)
                target.write_bytes(raw)
            for path in ("scripts/generate_api.py", "docs/API.md", "docs/api-manifest.json"):
                (archive / path).write_bytes((ROOT / path).read_bytes())
            native = Path(temporary) / "retained-native-inputs"
            native.mkdir()
            for module, raw in self.original.items():
                (native / ("declaration-data-" + module + ".bmp")).write_bytes(raw)
            command = [sys.executable, "-I", "-B", str(archive / "scripts/generate_api.py"),
                       "--native-data", str(native), "--source-revision", api.SOURCE,
                       "--docgen-revision", api.TOOL, "--check"]
            result = subprocess.run(command, cwd=archive, env={"PATH": "/no-git-binary"},
                                    capture_output=True, text=True, check=False)
            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertIn('"status": "matched"', result.stdout)
            (archive / "docs/api-manifest.json").write_bytes(b"{}")
            result = subprocess.run(command, cwd=archive, env={"PATH": "/no-git-binary"},
                                    capture_output=True, text=True, check=False)
            self.assertNotEqual(result.returncode, 0)
            self.assertIn("generated file differs/stale manifest", result.stderr)


if __name__ == "__main__":
    ARGS = PARSER.parse_args()
    unittest.main(argv=[sys.argv[0]], verbosity=2)
