#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# Copyright (C) 2024-2025 formalsec
# Written by Joao Pereira
"""
Best-effort coverage audit for the OCaml cvc5 bindings.

The script compares public methods from:
    - vendor/cvc5/include/cvc5/cvc5.h
    - vendor/cvc5/include/cvc5/cvc5_parser.h

against the OCaml surface exposed in:
    - cvc5.mli

It is intentionally heuristic:
    - it matches by normalized names, not exact type signatures;
    - it uses a small alias map for API names that were intentionally renamed
        in the OCaml surface;
    - overloaded/defaulted C++ methods may still require manual review.

Use it as a coverage audit, not as a formal proof of parity.
"""


import argparse
import json
import re
from dataclasses import dataclass
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
HEADER_FILES = [
    ROOT / "vendor/cvc5/include/cvc5/cvc5.h",
    ROOT / "vendor/cvc5/include/cvc5/cvc5_parser.h",
]
MLI_FILE = ROOT / "cvc5.mli"


TARGETS = {
    "TermManager": [
        "TermManager",
        "Sort",
        "Term",
        "Op",
        "DatatypeConstructorDecl",
        "DatatypeDecl",
        "Statistics",
    ],
    "Sort": ["Sort", "Datatype"],
    "Op": ["Op"],
    "Term": ["Term"],
    "Result": ["Result"],
    "Grammar": ["Grammar"],
    "SynthResult": ["SynthResult"],
    "DatatypeConstructorDecl": ["DatatypeConstructorDecl"],
    "DatatypeDecl": ["DatatypeDecl"],
    "DatatypeSelector": ["DatatypeSelector"],
    "DatatypeConstructor": ["DatatypeConstructor"],
    "Datatype": ["Datatype"],
    "OptionInfo": ["OptionInfo"],
    "DriverOptions": ["DriverOptions"],
    "Stat": ["Stat"],
    "Statistics": ["Statistics"],
    "Proof": ["Proof"],
    "Plugin": ["Plugin"],
    "Solver": ["Solver"],
    "SymbolManager": ["SymbolManager"],
    "Command": ["Command"],
    "InputParser": ["InputParser"],
}

INCLUDE_DEPRECATED = False


MANUAL_ALIASES = {
    ("TermManager", "getStatistics"): {"of_term_manager"},
    ("TermManager", "mkDatatypeConstructorDecl"): {"mk"},
    ("TermManager", "mkDatatypeDecl"): {"mk"},
    ("Sort", "getBitVectorSize"): {"bv_size"},
    ("Sort", "getDatatype"): {"of_sort"},
    ("Op", "getKind"): {"kind"},
    ("Term", "getId"): {"id"},
    ("Term", "getKind"): {"kind"},
    ("Term", "getSort"): {"sort"},
    ("Result", "getUnknownExplanation"): {"get_unknown_explanation"},
    ("Result", "isSat"): {"is_sat"},
    ("Result", "isUnsat"): {"is_unsat"},
    ("Result", "isUnknown"): {"is_unknown"},
    ("Grammar", "addRule"): {"add_rule"},
    ("Grammar", "addRules"): {"add_rules"},
    ("Grammar", "addAnyConstant"): {"add_any_constant"},
    ("Grammar", "addAnyVariable"): {"add_any_variable"},
    ("DatatypeConstructorDecl", "addSelector"): {"add_selector"},
    ("DatatypeConstructorDecl", "addSelectorSelf"): {"add_selector_self"},
    ("DatatypeConstructorDecl", "addSelectorUnresolved"): {"add_selector_unresolved"},
    ("DatatypeDecl", "addConstructor"): {"add_constructor"},
    ("DatatypeSelector", "getName"): {"get_name"},
    ("DatatypeSelector", "getTerm"): {"get_term"},
    ("DatatypeSelector", "getUpdaterTerm"): {"get_updater_term"},
    ("DatatypeSelector", "getCodomainSort"): {"get_codomain_sort"},
    ("DatatypeConstructor", "getName"): {"get_name"},
    ("DatatypeConstructor", "getTerm"): {"get_term"},
    ("DatatypeConstructor", "getInstantiatedTerm"): {"get_instantiated_term"},
    ("DatatypeConstructor", "getTesterTerm"): {"get_tester_term"},
    ("DatatypeConstructor", "getNumSelectors"): {"get_num_selectors"},
    ("DatatypeConstructor", "getSelector"): {"get_selector"},
    ("Datatype", "getConstructor"): {"get_constructor"},
    ("Datatype", "getSelector"): {"get_selector"},
    ("Datatype", "getName"): {"get_name"},
    ("Datatype", "getNumConstructors"): {"get_num_constructors"},
    ("Datatype", "getParameters"): {"get_parameters"},
    ("OptionInfo", "boolValue"): {"bool_value"},
    ("OptionInfo", "stringValue"): {"string_value"},
    ("OptionInfo", "intValue"): {"int_value"},
    ("OptionInfo", "uintValue"): {"uint_value"},
    ("OptionInfo", "doubleValue"): {"double_value"},
    ("Stat", "getInt"): {"get_int"},
    ("Stat", "getDouble"): {"get_double"},
    ("Stat", "getString"): {"get_string"},
    ("Stat", "getHistogram"): {"get_histogram"},
    ("Statistics", "get"): {"get"},
    ("Proof", "getResult"): {"get_result"},
    ("Proof", "getChildren"): {"get_children"},
    ("Proof", "getArguments"): {"get_arguments"},
    ("Solver", "resetAssertions"): {"reset"},
    ("Solver", "mkGrammar"): {"mk_grammar"},
    ("Solver", "synthFun"): {"synth_fun"},
    ("Solver", "declareSygusVar"): {"declare_sygus_var"},
    ("Solver", "getSynthSolution"): {"get_synth_solution"},
    ("Solver", "getSynthSolutions"): {"get_synth_solutions"},
    ("Solver", "checkSynth"): {"check_synth"},
    ("Solver", "checkSynthNext"): {"check_synth_next"},
    ("Solver", "addSygusConstraint"): {"add_sygus_constraint"},
    ("Solver", "getSygusConstraints"): {"get_sygus_constraints"},
    ("Solver", "addSygusAssume"): {"add_sygus_assume"},
    ("Solver", "getSygusAssumptions"): {"get_sygus_assumptions"},
    ("Solver", "addSygusInvConstraint"): {"add_sygus_inv_constraint"},
    ("Solver", "getQuantifierElimination"): {"get_quantifier_elimination"},
    ("Solver", "getQuantifierEliminationDisjunct"): {"get_quantifier_elimination_disjunct"},
    ("Solver", "declareSepHeap"): {"declare_sep_heap"},
    ("Solver", "getValueSepHeap"): {"get_value_sep_heap"},
    ("Solver", "getValueSepNil"): {"get_value_sep_nil"},
    ("Solver", "declarePool"): {"declare_pool"},
    ("Solver", "blockModel"): {"block_model"},
    ("Solver", "blockModelValues"): {"block_model_values"},
    ("Solver", "getInterpolant"): {"get_interpolant"},
    ("Solver", "getInterpolantNext"): {"get_interpolant_next"},
    ("Solver", "getAbduct"): {"get_abduct"},
    ("Solver", "getAbductNext"): {"get_abduct_next"},
    ("Solver", "getInstantiations"): {"get_instantiations"},
    ("Solver", "getProof"): {"get_proof"},
    ("Solver", "proofToString"): {"proof_to_string"},
    ("Solver", "getLearnedLiterals"): {"get_learned_literals"},
    ("Solver", "getTimeoutCore"): {"get_timeout_core"},
    ("Solver", "getTimeoutCoreAssuming"): {"get_timeout_core_assuming"},
    ("Solver", "getUnsatAssumptions"): {"get_unsat_assumptions"},
    ("Solver", "getUnsatCoreLemmas"): {"get_unsat_core_lemmas"},
    ("Solver", "getOptionNames"): {"get_option_names"},
    ("Solver", "getOptionInfo"): {"get_option_info"},
    ("Solver", "getAssertions"): {"get_assertions"},
    ("Solver", "declareDatatype"): {"declare_datatype"},
    ("Solver", "declareSort"): {"declare_sort"},
    ("Solver", "defineFunRec"): {"define_fun_rec", "define_fun_rec_term"},
    ("Solver", "defineFunsRec"): {"define_funs_rec"},
    ("Solver", "findSynth"): {"find_synth"},
    ("Solver", "getStatistics"): {"get_statistics"},
}


SKIP_METHODS = {
    "begin",
    "end",
    "operator[]",
    "operator==",
    "operator!=",
    "operator<",
    "operator>",
    "operator<=",
    "operator>=",
    "operator++",
    "operator--",
    "operator*",
    "operator->",
}


TOKEN_REPLACEMENTS = {
    "boolean": "bool",
    "integer": "int",
    "function": "fun",
    "predicate": "pred",
    "bit_vector": "bv",
    "floating_point": "fp",
    "rounding_mode": "rm",
    "sequence": "seq",
}


@dataclass(frozen=True)
class Method:
    class_name: str
    name: str
    signature: str


def strip_comments(text):
    text = re.sub(r"/\*.*?\*/", "", text, flags=re.S)
    text = re.sub(r"\[\[.*?\]\]", "", text, flags=re.S)
    lines = []
    for line in text.splitlines():
        line = re.sub(r"//.*", "", line)
        if line.lstrip().startswith("#"):
            continue
        lines.append(line)
    return "\n".join(lines)


def camel_to_snake(name):
    name = re.sub(r"([a-z0-9])([A-Z])", r"\1_\2", name)
    return name.lower()


def abbreviate_tokens(name):
    result = name
    for src, dst in TOKEN_REPLACEMENTS.items():
        result = result.replace(src, dst)
    return result


def candidate_names(class_name, method_name):
    out = set()
    snake = camel_to_snake(method_name)
    out.add(snake)
    out.add(abbreviate_tokens(snake))
    if snake.startswith("get_"):
        tail = snake[4:]
        out.add(tail)
        out.add(abbreviate_tokens(tail))
        if tail.endswith("_sort"):
            out.add("mk_" + tail)
            out.add(abbreviate_tokens("mk_" + tail))
    if snake.startswith("is_"):
        out.add(abbreviate_tokens(snake))
    if snake.startswith("mk_"):
        out.add(abbreviate_tokens(snake))
    out |= MANUAL_ALIASES.get((class_name, method_name), set())
    return {name for name in out if name}


def parse_ocaml_modules(path):
    modules = {}
    current = None
    for raw_line in path.read_text().splitlines():
        line = raw_line.rstrip()
        module_match = re.match(r"module\s+([A-Z][A-Za-z0-9_]*)\s*:\s*sig", line)
        if module_match:
            current = module_match.group(1)
            modules.setdefault(current, set())
            continue
        if current and re.match(r"end\b", line.strip()):
            current = None
            continue
        if current:
            val_match = re.match(r"\s*val\s+([a-zA-Z_][A-Za-z0-9_]*)\b", line)
            if val_match:
                modules[current].add(val_match.group(1))
    return modules


def parse_header_methods(path):
    text = strip_comments(path.read_text())
    lines = text.splitlines()
    classes = {}
    pending_class = None
    current_class = None
    visibility = None
    brace_depth = 0
    buffer = ""

    for raw_line in lines:
        line = raw_line.strip()
        if not current_class:
            class_match = re.match(
                r"(?:class|struct)(?:\s+CVC5_EXPORT)?\s+([A-Za-z_][A-Za-z0-9_]*)\b",
                line,
            )
            if class_match:
                name = class_match.group(1)
                pending_class = name if name in TARGETS else None
            if pending_class and "{" in line:
                current_class = pending_class
                classes.setdefault(current_class, [])
                visibility = None
                brace_depth = line.count("{") - line.count("}")
                pending_class = None
            continue

        if brace_depth == 1 and line in {"public:", "private:", "protected:"}:
            visibility = line[:-1]
            buffer = ""
            brace_depth += line.count("{") - line.count("}")
            if brace_depth == 0:
                current_class = None
                visibility = None
            continue

        if visibility == "public" and brace_depth == 1:
            if (
                line
                and not line.startswith(("class ", "struct ", "enum ", "using ", "typedef "))
                and not line.startswith("template")
                and "friend " not in line
                and "{" not in line
            ):
                buffer = (buffer + " " + line).strip()
                if ";" in line:
                    declaration = buffer.strip()
                    buffer = ""
                    method = extract_method(current_class, declaration)
                    if method:
                        classes[current_class].append(method)

        brace_depth += line.count("{") - line.count("}")
        if brace_depth == 0:
            current_class = None
            visibility = None
            buffer = ""

    return classes


def extract_method(class_name, declaration):
    if "(" not in declaration or ")" not in declaration:
        return None
    declaration = re.sub(r"\s+", " ", declaration).strip()
    if not INCLUDE_DEPRECATED and "deprecated" in declaration:
        return None
    head = declaration.split("(", 1)[0].strip()
    match = re.search(r"([~A-Za-z_][A-Za-z0-9_]*|operator[^\s]+)$", head)
    if not match:
        return None
    name = match.group(1)
    if name in SKIP_METHODS:
        return None
    if name == class_name or name == f"~{class_name}":
        return None
    if name.startswith("operator"):
        return None
    return Method(class_name=class_name, name=name, signature=declaration)


def audit():
    ocaml_modules = parse_ocaml_modules(MLI_FILE)
    all_methods = {}
    for header in HEADER_FILES:
        for class_name, methods in parse_header_methods(header).items():
            all_methods.setdefault(class_name, []).extend(methods)

    report = {}
    for class_name, modules in TARGETS.items():
        methods = all_methods.get(class_name, [])
        exposed_vals = set().union(*(ocaml_modules.get(m, set()) for m in modules))
        implemented = []
        missing = []
        for method in methods:
            names = sorted(candidate_names(class_name, method.name))
            hit = any(name in exposed_vals for name in names)
            item = {
                "method": method.name,
                "signature": method.signature,
                "candidates": names,
            }
            if hit:
                implemented.append(item)
            else:
                missing.append(item)
        report[class_name] = {
            "modules": modules,
            "implemented_count": len(implemented),
            "missing_count": len(missing),
            "implemented": implemented,
            "missing": missing,
        }
    return report


def render_text(report, only_class, show_all):
    lines = []
    classes = [only_class] if only_class else list(TARGETS.keys())
    for class_name in classes:
        entry = report[class_name]
        total = entry["implemented_count"] + entry["missing_count"]
        lines.append(
            f"{class_name}: {entry['implemented_count']}/{total} implemented "
            f"({entry['missing_count']} missing)"
        )
        lines.append(f"  mapped modules: {', '.join(entry['modules'])}")
        bucket = entry["implemented"] if show_all else entry["missing"]
        label = "implemented" if show_all else "missing"
        for item in bucket:
            lines.append(
                f"  - {label}: {item['signature']}  [candidates: {', '.join(item['candidates'])}]"
            )
        if not bucket:
            lines.append(f"  - no {label} entries")
        lines.append("")
    return "\n".join(lines).rstrip() + "\n"


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--json", action="store_true", help="emit JSON")
    parser.add_argument("--class", dest="class_name", help="restrict to one class")
    parser.add_argument(
        "--show-implemented",
        action="store_true",
        help="show implemented entries instead of missing ones in text mode",
    )
    parser.add_argument(
        "--include-deprecated",
        action="store_true",
        help="include deprecated C++ API methods in the audit",
    )
    args = parser.parse_args()

    global INCLUDE_DEPRECATED
    INCLUDE_DEPRECATED = args.include_deprecated

    report = audit()
    if args.class_name and args.class_name not in report:
        raise SystemExit(f"unknown class: {args.class_name}")

    if args.json:
        data = report if not args.class_name else {args.class_name: report[args.class_name]}
        print(json.dumps(data, indent=2, sort_keys=True))
        return

    print(render_text(report, args.class_name, args.show_implemented), end="")


if __name__ == "__main__":
    main()
