#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
# Authors: Formal Frontier Agents
"""Bounded native doc-gen4 declaration reference for restricted-product duality.

Adapted from the Formal Frontier finite-group Tate cohomology generator,
itself based on polynomial-root stability and Anchor's ideal-completion
documentation recipe. See docs/README.md for contributor and rights context.
Pinned records are documentation inputs, not proof or release certificates.
"""

if not __debug__:
    raise SystemExit("optimized Python is not supported for API generation")

import argparse
import hashlib
from html.parser import HTMLParser
import json
from pathlib import Path
import re


TOOL = "97d4ecdfc8e09e7f511724c25e303d448de6a3db"
SOURCE = "ae1998d20adc0b4fea4b311818b9d1b0a2859825"
SOURCE_TREE = "fc6764ae85ce01f9741b1f86f4c588434a2f9c3b"
MODULES = (
    "RestrictedProductDuality.CompactStage",
    "RestrictedProductDuality.SmallArc",
    "RestrictedProductDuality.Pairing",
    "RestrictedProductDuality.TopologicalPairing",
    "RestrictedProductDuality.CharacterReconstruction",
    "RestrictedProductDuality.SymmetricDuality",
    "RestrictedProductDuality.Naturality",
    "RestrictedProductDuality",
    "RestrictedProductDuality.Clients",
    "RestrictedProductDuality.SymmetricClients",
    "RestrictedProductDuality.NaturalityClients",
    "RestrictedProductDualityTest",
)
COUNTS = (7, 1, 13, 6, 26, 8, 5, 0, 6, 0, 2, 0)
SOURCE_INPUT_SHA256 = {
    "RestrictedProductDuality/CompactStage.lean": "9acb184a1e45a8d450a1a361fb0f7ad9f981a98f317502ee0446dabac6757e9c",
    "RestrictedProductDuality/SmallArc.lean": "993d3ff75abc9a88edb0a3c7a076562477e77ca1865b16230a0a5321f6f9c691",
    "RestrictedProductDuality/Pairing.lean": "bb9d3f2c4f8d6c8416d66bf52ab9ea11aeb6f15d7e4768be8b25975a21af168d",
    "RestrictedProductDuality/TopologicalPairing.lean": "21bac903aab1e028260bb2a5e976fd4c187fb308576d78148a4347a8220cc365",
    "RestrictedProductDuality/CharacterReconstruction.lean": "8e7cb41804271de8b1b75a1a964a98fa9433ae952ea8b5a18a06f4b0f59bf95c",
    "RestrictedProductDuality/SymmetricDuality.lean": "ff60e1d921cc0d4fed38c9b54198cb7d395e705e5bb8e4252b49871104e7d660",
    "RestrictedProductDuality/Naturality.lean": "648eae535bc2b9f202801df914a6054e8e752f8bb36ba251938d022f80c2c60f",
    "RestrictedProductDuality.lean": "9dd88dd1a1e0128346ec57ca122c95ecb7f871088e5d2ad2c168e7f243bb27fc",
    "RestrictedProductDuality/Clients.lean": "a6ed75db001c7231e9c7efca71c5a758515ad0b71e78d1aec09af01dac1ad961",
    "RestrictedProductDuality/SymmetricClients.lean": "0f18780faaa7b3b39e87003e03206f33cafb106f6f7488cca03dc73a12567be4",
    "RestrictedProductDuality/NaturalityClients.lean": "588fc412bce76fc6b081e4e233feb86fca0c286cfb75d5252eb91f3bbe87ccab",
    "RestrictedProductDualityTest.lean": "028d534df6b06b470731be12fb0bd3f8615b38ee0c1cadd3c7ed330279d12d2a",
    "lean-toolchain": "8190e75a201741065fe508b28955dd64dd72d090babe5f70ce6848879d68ae88",
    "lakefile.lean": "c222c8d738a6e69149b8291c8f0f91a88bc5afd53eb2dd11d2df177d76cff296",
    "lake-manifest.json": "3b2440a01f65292927368f07bc450062f08f3b75a4ef16db4ef1c70a9702fb8b",
}
NATIVE_RECORD_SHA256 = {
    "RestrictedProductDuality.CompactStage": "b54575c4a1ac77d4cab056c4fd4693c82676ac36891695c8ed532938a152b762",
    "RestrictedProductDuality.SmallArc": "838ae70e60313535e53a4b7535d00f8c0afe011e2d5421cd7540b8e7054a6cf9",
    "RestrictedProductDuality.Pairing": "d89fdfda6865c99b008f89fa70682282628cfc90cca0d66e631eaecaaac40bf2",
    "RestrictedProductDuality.TopologicalPairing": "5ba49c70c5ab579fa3f2afee9c2f4cbb0326e0a59dc74af663c1468e91259457",
    "RestrictedProductDuality.CharacterReconstruction": "e149d417bb1746ad1015f20f98de755a99837e0858f023021fd1bd7fd3c7321b",
    "RestrictedProductDuality.SymmetricDuality": "23720d87053889bb2bb7411479911fe416d4b24d1767e395b584a365cb55b3ef",
    "RestrictedProductDuality.Naturality": "2036b20aafa5f30b8f736395913483c66a80c8fa838cd3fa06c1a82913d1654b",
    "RestrictedProductDuality": "b197c55f5bd4295a1aabb9fce8aa3ea44dfcfeb9ca0c9ccf4bb921337a325939",
    "RestrictedProductDuality.Clients": "160123119e9351784e5076fd3bf30fc6377969e04dc1837af92ba63c444fd823",
    "RestrictedProductDuality.SymmetricClients": "3345ba487ae1c3f1d3c99fcbda3174e2987fd6ddc0ad3c2ea41063f17e3a1537",
    "RestrictedProductDuality.NaturalityClients": "c29a99d0ea694568ad9821580788aa25964a383e7e1d0921fcd32bc6c59899d5",
    "RestrictedProductDualityTest": "0e2c1bf6b38e9107ea0805291ad70fbe56aebfae74271bd95de18fb2afaf7638",
}
KEY_TOKENS = {
    "RestrictedProduct.exists_subset_cofiniteStage": ("{ι : Type u_1}", "{R : ι → Type u_2}", "(hAopen :", "(hK : IsCompact K)"),
    "Subgroup.le_ker_of_mapsTo_centeredArc": ("[Group G]", "Circle.centeredArc (Real.pi / 2)"),
    "RestrictedProduct.pairing_hasFiniteMulSupport": ("{X : ι → Type u_2}", "{Y : ι → Type u_3}", "(horth :"),
    "RestrictedProduct.toPontryaginDual_injective": ("(hUopen :", "(hVopen :", "(hsep :"),
    "RestrictedProduct.toPontryaginDual_surjective": ("Function.Bijective", "rightAnnihilator (U i)"),
    "RestrictedProduct.pontryaginDualEquiv": ("[∀ (i : ι), Finite (X i)]", "[∀ (i : ι), DiscreteTopology (X i)]", "[∀ (i : ι), IsTopologicalGroup (Y i)]", "(hperfect :", "(hV :"),
    "RestrictedProduct.symmetricPontryaginDualEquiv": ("[∀ (i : ι), Finite (Y i)]", "[∀ (i : ι), DiscreteTopology (Y i)]", "[∀ (i : ι), IsTopologicalGroup (X i)]", "(hperfect :", "(hU :"),
    "RestrictedProduct.toPontryaginDual_natural": ("{X' : ι → Type u_3}", "{Y : ι → Type u_4}", "{Y' : ι → Type u_5}", "Filter.cofinite", "PontryaginDual.map"),
    "RestrictedProduct.mapContinuousMonoidHom": ("Filter.cofinite", "Set.MapsTo"),
}
CATALOGUE = {
    "RestrictedProduct.mem_cofiniteStage": "Membership in a cofinite stage means every coordinate outside its finite exceptional set lies in the distinguished subset.",
    "RestrictedProduct.mem_cofiniteStage_exceptionalFinset": "Each restricted-product element belongs to the stage cut out by its own finite exceptional-coordinate set.",
    "RestrictedProduct.pairing_mulSingle_left": "A single nontrivial character-domain coordinate evaluates the global pairing by its corresponding local bicharacter.",
    "RestrictedProduct.pairing_mulSingle_right": "A single representing coordinate evaluates the global pairing by the corresponding local bicharacter.",
    "RestrictedProduct.pairing_one_left": "The global pairing is one when its first argument is the identity.",
    "RestrictedProduct.pairing_one_right": "The global pairing is one when its second argument is the identity.",
    "RestrictedProduct.pairing_mul_left": "The global pairing multiplies pointwise under multiplication in its first argument.",
    "RestrictedProduct.pairing_mul_right": "The global pairing multiplies pointwise under multiplication in its second argument.",
    "RestrictedProduct.pairingMonoidHom_apply": "Evaluating the pairing monoid homomorphism at a first-product element yields the global pairing with its fixed second-product element.",
    "RestrictedProduct.pairingHom_apply": "The curried pairing homomorphism evaluates to the underlying global bicharacter at both arguments.",
    "RestrictedProduct.pairingCharacter_apply": "Evaluation of the constructed continuous character at a first-product element is the global pairing.",
    "RestrictedProduct.toPontryaginDual_apply": "Evaluating the canonical continuous dual map on a representing element and a character-domain element gives the global pairing.",
    "RestrictedProduct.rightCharacter_apply": "A local right character evaluated on the left group element is the original local bicharacter value.",
    "RestrictedProduct.mem_rightAnnihilator": "Membership in the right annihilator is equivalent to pairing to one with every element of the chosen left subgroup.",
    "RestrictedProduct.structureMapMonoidHom_apply": "The distinguished product's structure map evaluates coordinatewise by the underlying subgroup inclusion.",
    "RestrictedProduct.mem_productTail": "Membership in the product tail means every coordinate in the selected finite set equals one.",
    "RestrictedProduct.structureMapMonoidHom_pi_mulSingle": "The structure map sends a single distinguished subgroup coordinate to the corresponding single restricted-product coordinate.",
    "RestrictedProduct.coordinateCharacter_apply": "The coordinate character obtained by probing a global character at a single coordinate evaluates at that coordinate's element.",
    "RestrictedProduct.reconstructedCoordinate_spec": "The reconstructed representing coordinate has the specified local right-character values on every coordinate-domain element.",
    "RestrictedProduct.finset_prod_mulSingle_apply": "At a coordinate in the selected finite set, the finite product of single-coordinate elements has the prescribed value; elsewhere it is one.",
    "RestrictedProduct.toPontryaginDualMulEquiv_apply": "The algebraic equivalence acts on a representing element through the canonical continuous dual map.",
    "RestrictedProduct.pontryaginDualEquiv_apply": "The topological multiplicative equivalence acts through the same canonical continuous dual map.",
    "RestrictedProduct.mem_leftAnnihilator": "Membership in the left annihilator is equivalent to pairing to one with every element of the chosen right subgroup.",
    "RestrictedProduct.mapContinuousMonoidHom_apply": "The induced continuous restricted-product homomorphism evaluates each coordinate through its original coordinate map.",
    "RestrictedProduct.zmodBicharacter_apply": "Evaluation of the cyclic multiplicative bicharacter is the standard finite-character value from the two underlying residues.",
}


def require(condition, message):
    if not condition:
        raise ValueError(message)


def digest(raw):
    return hashlib.sha256(raw).hexdigest()


class Header(HTMLParser):
    """Read displayed native text without dropping CSS-collapsed implicit binders."""

    def __init__(self, value):
        super().__init__(convert_charrefs=True)
        self.stack = []
        self.text = []
        self.kinds = []
        self.names = []
        self.feed(value)
        self.close()
        require(not self.stack, "unclosed native header")

    def handle_starttag(self, tag, attrs):
        require(tag in {"div", "span", "a"}, "unexpected/active native header tag")
        attributes = dict(attrs)
        require(len(attrs) == len(attributes) and set(attributes) <= {"class", "href"},
                "active/unknown native header attribute")
        require(tag == "a" or "href" not in attributes, "unexpected native header link")
        require("href" not in attributes or
                re.fullmatch(r"\./[\w./#-]+", attributes["href"]) is not None,
                "active/external native header link")
        classes = set(attributes.get("class", "").split())
        if tag == "div" and "decl_type" in classes:
            self.text.append(" ")
        self.stack.append((tag, classes))

    def handle_endtag(self, tag):
        require(bool(self.stack) and self.stack[-1][0] == tag, "unbalanced native header")
        self.stack.pop()

    def handle_data(self, value):
        require(bool(self.stack) or not value.strip(), "text outside native header")
        self.text.append(value)
        if any("decl_kind" in classes for _, classes in self.stack):
            self.kinds.append(value)
        if any("decl_name" in classes for _, classes in self.stack):
            self.names.append(value)

    def handle_comment(self, _):
        raise ValueError("unexpected native header comment")

    def handle_decl(self, _):
        raise ValueError("unexpected native header declaration")

    def rendered(self):
        return " ".join("".join(self.text).split())


def source_anchor(raw, line, name, doc):
    lines = raw.decode("utf-8").splitlines()
    require(type(line) is int and 0 < line <= len(lines), "invalid native source line: " + name)
    rest = "\n".join(lines[line - 1:])
    if doc:
        require(rest.startswith("/--"), "native source docstring position differs: " + name)
        source_doc, closing, rest = rest.partition("-/")
        require(bool(closing) and source_doc[3:].strip() == doc.strip(),
                "native docstring/source mismatch: " + name)
    else:
        require(not rest.startswith("/--"), "native docstring missing: " + name)
    declaration = re.match(r"\s*(?:(?:@\[[^\]\n]*\]\s*|"
                           r"(?:noncomputable|private|protected|local)\s+))*"
                           r"(def|lemma|theorem|instance|abbrev)\s+(\S+)", rest)
    require(declaration is not None, "native source declaration absent: " + name)
    require(declaration.group(2) == name.rsplit(".", 1)[-1] and
            "/--" not in rest[:declaration.start()],
            "native source/name position differs: " + name)


def check_snapshot(revision, sources):
    require(revision == SOURCE, "unexpected/stale analyzed source revision")
    require(set(sources) == set(SOURCE_INPUT_SHA256), "source/pin inventory differs")
    for path, expected in SOURCE_INPUT_SHA256.items():
        require(digest(sources[path]) == expected, "source/pin drift from accepted input: " + path)


def validate(records, raw_records, sources, revision):
    check_snapshot(revision, sources)
    require(set(records) == set(raw_records) == set(MODULES), "native module inventory differs")
    sections = {"production": [], "clients": [], "test": []}
    names = set()
    undocumented = set()
    for module, expected_count in zip(MODULES, COUNTS):
        record = records[module]
        require(json.loads(raw_records[module]) == record, "native record bytes/JSON differ: " + module)
        require(type(record) is dict and set(record) == {"name", "declarations", "instances", "imports"},
                "native module shape differs: " + module)
        require(record["name"] == module, "native module name differs: " + module)
        require(type(record["declarations"]) is list and len(record["declarations"]) == expected_count,
                "missing/extra native declaration: " + module)
        require(type(record["instances"]) is list and not record["instances"] and
                type(record["imports"]) is list,
                "missing/extra/wrong native instance table: " + module)
        path = module.replace(".", "/") + ".lean"
        for row in record["declarations"]:
            require(type(row) is dict and set(row) == {"info", "header"} and
                    type(row["info"]) is dict, "native declaration shape differs: " + module)
            info = row["info"]
            require(set(info) == {"name", "kind", "doc", "docLink", "sourceLink", "line"},
                    "native declaration info shape differs: " + module)
            name, kind = info["name"], info["kind"]
            require(type(name) is str and type(kind) is str and kind in {"def", "theorem"} and
                    (name.startswith("RestrictedProduct.") or
                     name == "Subgroup.le_ker_of_mapsTo_centeredArc"),
                    "wrong native name/kind: " + str(name))
            require(name not in names, "duplicate native declaration: " + name)
            names.add(name)
            require(type(info["doc"]) is str and type(row["header"]) is str,
                    "malformed native doc/header: " + name)
            require(info["sourceLink"] == "https://example.invalid/commit/" + revision + "/" + path,
                    "native source module/revision/path differs: " + name)
            require(info["docLink"] == "./" + module.replace(".", "/") + ".html#" + name,
                    "native self link differs: " + name)
            require("```" not in info["doc"] and
                    re.search(r"<\s*[/!?a-zA-Z]", info["doc"]) is None,
                    "active/unsupported native docstring: " + name)
            source_anchor(sources[path], info["line"], name, info["doc"])
            header = Header(row["header"])
            text = header.rendered()
            visible_kind = "".join(header.kinds)
            require((visible_kind in {"noncomputable def", "def", "abbrev"} if kind == "def"
                     else visible_kind == "theorem") and "".join(header.names) == name and
                    text.startswith(visible_kind + " " + name + " ") and "```" not in text,
                    "native signature identity/format differs: " + name)
            for token in KEY_TOKENS.get(name, ()):
                require(token in text, "missing signature binder: " + name + " / " + token)
            if not info["doc"]:
                require(name in CATALOGUE and kind == "theorem",
                        "missing original catalogue explanation: " + name)
                undocumented.add(name)
            section = "test" if module == "RestrictedProductDualityTest" else (
                "clients" if module.split(".")[-1] in
                {"Clients", "SymmetricClients", "NaturalityClients"} else "production")
            sections[section].append(dict(name=name, kind=kind, module=module, path=path,
                                          line=info["line"], signature=text,
                                          doc=info["doc"].strip(), note=CATALOGUE.get(name)))
        require(digest(raw_records[module]) == NATIVE_RECORD_SHA256[module],
                "native raw record differs from pinned tool/input: " + module)
    require(len(names) == 74 and len(sections["production"]) == 66 and
            len(sections["clients"]) == 8 and not sections["test"] and
            undocumented == set(CATALOGUE), "mixed public/client/undocumented inventory differs")
    return sections


def render(records, raw_records, sources, revision):
    sections = validate(records, raw_records, sources, revision)
    lines = ["# Native API reference", "",
             "Fixed Lean `v4.34.0-rc2`, mathlib `e37d88a26f3791ed5a93daa1f949af1021b8d103`",
             "and separately pinned doc-gen4 `" + TOOL + "`. These are the full",
             "displayed signatures, including implicit parameters and independent universes,",
             "of **all 74 entries in the native declarations tables for all 12 shipped modules**.",
             "All twelve native instance tables have zero rows. Two named `local instance`s",
             "in `NaturalityClients` occur in the native declarations table as `def` and",
             "`theorem`, not as instance-table rows; the local instance attribute is not",
             "asserted to be exported. The `Subgroup` lemma is retained across namespaces.",
             "This public/native filtered reference is not a census of private or",
             "compiler-generated proofs and does not certify axioms, source coverage",
             "or rights. [Reproduce and assess provenance](README.md).", "",
             "Source links target only the unchanged `.lean` files shipped here.",
             "**Native source docstring** matches an original Lean comment;",
             "**Original catalogue explanation** is newly written here for an",
             "entry without a source docstring, not a fabricated Lean docstring.", "",
             "## Native module inventory", "",
             "| Shipped module | Definitions | Theorems | Native instance-table rows |",
             "| --- | ---: | ---: | ---: |"]
    for module in MODULES:
        module_rows = records[module]["declarations"]
        source = "../" + module.replace(".", "/") + ".lean"
        definitions = sum(row["info"]["kind"] == "def" for row in module_rows)
        theorems = sum(row["info"]["kind"] == "theorem" for row in module_rows)
        lines.append(f"| [`{module}`]({source}) | {definitions} | {theorems} | 0 |")
    lines.append("")
    for section, heading in (("production", "Production API (66 native entries)"),
                             ("clients", "Legacy client and scoped local entries (8 native entries)"),
                             ("test", "Default-built public-import test (0 native entries)")):
        lines.extend(["## " + heading, ""])
        rows = sorted(sections[section], key=lambda row: (MODULES.index(row["module"]),
                                                         row["line"], row["name"]))
        if not rows:
            lines.extend(["No public/native named entries in this section.", ""])
        for row in rows:
            lines.extend(["### " + row["name"], "", "Kind: `" + row["kind"] + "`.", "",
                          "```lean", row["signature"], "```", ""])
            if row["doc"]:
                lines.extend(["**Native source docstring:** " + row["doc"], ""])
            else:
                lines.extend(["**Original catalogue explanation (not a Lean docstring):** " +
                              row["note"], ""])
            lines.extend([f"[Source](../{row['path']}#L{row['line']}) "
                          "(native source start line).", ""])
    markdown = "\n".join(lines).encode("utf-8")
    normalized = {module: digest(json.dumps(records[module], ensure_ascii=False,
                     sort_keys=True, separators=(",", ":")).encode("utf-8")) for module in MODULES}
    manifest = dict(format=2, generator="scripts/generate_api.py", docgen_revision=TOOL,
                    analyzed_source_revision=SOURCE, analyzed_source_tree=SOURCE_TREE,
                    modules=list(MODULES), inputs=SOURCE_INPUT_SHA256,
                    native_record_sha256=NATIVE_RECORD_SHA256,
                    normalized_record_sha256=normalized,
                    production_declarations=[row["name"] for row in sections["production"]],
                    client_and_local_declarations=[row["name"] for row in sections["clients"]],
                    test_declarations=[], native_instance_tables={module: [] for module in MODULES},
                    undocumented_count=len(CATALOGUE), api_sha256=digest(markdown),
                    proof_certification=False, release_acceptance=False)
    return markdown, (json.dumps(manifest, indent=2, sort_keys=True) + "\n").encode("utf-8")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--native-data", type=Path, required=True)
    parser.add_argument("--source-revision", required=True)
    parser.add_argument("--docgen-revision", required=True)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    require(args.docgen_revision == TOOL, "unexpected/stale doc-gen4 revision")
    root = Path(__file__).resolve().parent.parent
    sources = {}
    for path in SOURCE_INPUT_SHA256:
        source_path = root / path
        require(source_path.is_file() and not source_path.is_symlink(), "missing/linked source input: " + path)
        sources[path] = source_path.read_bytes()
    check_snapshot(args.source_revision, sources)
    require(args.native_data.is_dir() and not args.native_data.is_symlink(),
            "native data directory absent/linked")
    expected_files = {"declaration-data-" + module + ".bmp" for module in MODULES}
    require({path.name for path in args.native_data.iterdir()} == expected_files,
            "missing/extra native record file")
    raw_records = {}
    records = {}
    for module in MODULES:
        path = args.native_data / ("declaration-data-" + module + ".bmp")
        require(path.is_file() and not path.is_symlink(), "missing/linked native record: " + module)
        raw_records[module] = path.read_bytes()
        records[module] = json.loads(raw_records[module])
    api, manifest = render(records, raw_records, sources, args.source_revision)
    for name, raw in (("API.md", api), ("api-manifest.json", manifest)):
        target = root / "docs" / name
        require(not target.is_symlink(), "linked output refused: " + name)
        if args.check:
            require(target.is_file() and target.read_bytes() == raw,
                    "generated file differs/stale manifest: " + name)
    if not args.check:
        (root / "docs" / "API.md").write_bytes(api)
        (root / "docs" / "api-manifest.json").write_bytes(manifest)
    print(json.dumps(dict(status="matched" if args.check else "generated", production=66,
                          clients_and_local=8, native_instances=0, undocumented=25,
                          api_sha256=digest(api), proof_certification=False,
                          release_acceptance=False)))


if __name__ == "__main__":
    main()
