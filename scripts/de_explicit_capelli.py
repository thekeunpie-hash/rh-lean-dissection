#!/usr/bin/env python3
"""
Task 1: Batch Auto De-Elaborator (`de_explicit_capelli.py`)
for the 82 Heavy `pp.explicit` Files Identified in Round 1 (75,221 lines).

Architecture:
  - Balanced Lean 4 lexer/expression parser (respects `--` line comments, nested `/- ... -/`
    block comments, string/char literals, attributes `@[...]`, as-patterns `x@⟨...⟩`,
    universe annotations `.{u, v}`, and balanced `(...)` / `[...]` / `{...}` / `⟨...⟩`).
  - Bottom-up AST de-elaboration with two strict safety tiers:
      * Tier 1 (Exact Schema-Driven De-Elaboration): Verified Mathlib/Core binder schemas
        (exact arity + explicit argument indices + infix/notation pretty-printers for
        `Eq`, `Membership.mem`, `LE.le`, `LT.lt`, `HAdd`, `HSub`, `HMul`, `HDiv`, `HPow`,
        `HSMul`, `Neg`, `Inv`, `Norm`, `OfNat`, `Zero`, `One`, `Top`, `Bot`, `ite`,
        `DFunLike.coe`, `HasQuotient.Quotient`) + DuckDB-verified project-local declaration
        binder schemas (only applied when parsed binder arity matches observed arg count!).
      * Tier 2 (Arity-Preserving Instance-Chain Folding): For any uncataloged `@Head` whose
        arguments contain `pp.explicit` synthesized instance chains (`@*.to*`, `@*inst*`,
        canonical Mathlib dictionaries), preserves `@Head`, universe levels `.{...}`, and
        100% of positional argument slots, folding ONLY pure synthesized instance subtrees
        to `_` — guaranteeing ZERO arity corruption and ZERO dropped value/type arguments!
  - Preserves tactic-mode `:= by` blocks untouched unless an expression inside actually
    contains a `pp.explicit` synthesized instance chain (so manual `@lemma` calls in the
    31 non-`pp.explicit` files among the 82 targets are 100% preserved untouched!).
  - Cleans unused auto-generated `[inst_k : T]` binder names to `[T]` ONLY when `inst_k`
    has zero remaining references anywhere inside that declaration.
  - Automatically detects and categorizes Typeclass-Instance Ambiguity / Diamond Risks:
      * HIGH   : Custom/non-global project local instances dropped (e.g. `GlobalTheory.LocalData.complRel`,
                 `isLocalField`, `UpperTheory.Reformulated.B.*.aux*`, `algRes`).
      * MEDIUM : Diamond-prone Mathlib typeclass families (`NormedRing`, `NormedAddCommGroup`,
                 `InnerProductSpace`, `CStarAlgebra`, `ValuativeRel`, `IsNonarchimedeanLocalField`,
                 `Measure`, `TopologicalSpace`, `UniformSpace`, `MeasurableSpace`, `IsAlgClosure`,
                 `CharP`, `Algebra`, `IsScalarTower`, `SMulCommClass`, `CompatibleSMul`).
      * LOW    : Tier-2 wildcard `_` synthesis on uncataloged heads.
  - Verifies EVERY SINGLE output shadow file automatically:
      (a) Exact before/after lines & bytes,
      (b) 100% preservation of all `theorem`/`lemma`/`def`/`structure`/`abbrev`/`instance`/`class`/`inductive` names,
      (c) 0 `sorry`/`axiom`/`admit` introduced,
      (d) Balanced delimiters `()`, `[]`, `{}`, `⟨⟩` (comment- and string-stripped).
"""

from __future__ import annotations

import argparse
import json
import re
import time
from collections import Counter
from dataclasses import dataclass, field
from pathlib import Path

from index_lean import add_path_arguments, resolve_paths
from typing import Callable



# ==============================================================================
# 1. Exact Verified Mathlib / Core Schema Catalog (Tier 1)
# ==============================================================================

@dataclass
class HeadSchema:
    arity: int
    keep: tuple[int, ...]
    inst_pos: tuple[int, ...] = ()
    printer: Callable[[list[str], str], str] | None = None
    preserve_univ: bool = True
    phantom_named: tuple[tuple[int, str], ...] = ()


def _needs_parens(s: str) -> bool:
    s = s.strip()
    if not s:
        return False
    if (s[0] == "(" and s[-1] == ")" and _is_wrapped(s, "(", ")")) or (
        s[0] == "[" and s[-1] == "]" and _is_wrapped(s, "[", "]")
    ) or (s[0] == "{" and s[-1] == "}" and _is_wrapped(s, "{", "}")):
        return False
    if re.fullmatch(r"[\w.'\u2080-\u2089↥↑]+(?:\.\{[^}]*\})?", s):
        return False
    return True


def _is_wrapped(s: str, o: str, c: str) -> bool:
    if not s or s[0] != o or s[-1] != c:
        return False
    d = 0
    for i, ch in enumerate(s):
        if ch == o:
            d += 1
        elif ch == c:
            d -= 1
            if d == 0 and i != len(s) - 1:
                return False
    return d == 0


def _strip_outer_parens(s: str) -> str:
    s = s.strip()
    while len(s) >= 2 and s[0] == "(" and s[-1] == ")" and _is_wrapped(s, "(", ")"):
        inner = s[1:-1].strip()
        # NEVER strip parentheses around type ascriptions `(x : T)` or tuples `(a, b)`!
        if _find_top_level_char(inner, ":") != -1 or _find_top_level_char(inner, ",") != -1:
            break
        s = inner
    return s


def _atom(s: str) -> str:
    s = _strip_outer_parens(s)
    if _needs_parens(s):
        return f"({s})"
    return s


def _pr_infix(op: str, i_l: int, i_r: int) -> Callable[[list[str], str], str]:
    def fn(args: list[str], _u: str) -> str:
        l = _strip_outer_parens(args[i_l])
        r = _strip_outer_parens(args[i_r])
        # Wrap operands containing arrows/quantifiers/binders/low-prec ops
        if any(tok in l for tok in (" → ", " ↔ ", " ∧ ", " ∨ ", "∀ ", "∃ ", "fun ", "↦")):
            l = f"({l})"
        if any(tok in r for tok in (" → ", " ↔ ", " ∧ ", " ∨ ", "∀ ", "∃ ", "fun ", "↦")):
            r = f"({r})"
        return f"{l} {op} {r}"
    return fn


def _pr_bin_tight(op: str, i_l: int, i_r: int) -> Callable[[list[str], str], str]:
    def fn(args: list[str], _u: str) -> str:
        return f"{_atom(args[i_l])} {op} {_atom(args[i_r])}"
    return fn


def _pr_ofnat(args: list[str], _u: str) -> str:
    ty = _strip_outer_parens(args[0])
    lit = _strip_outer_parens(args[1])
    m = re.fullmatch(r"nat_lit\s+(\d+)", lit)
    num = m.group(1) if m else lit
    if ty in ("Nat", "ℕ"):
        return num
    return f"({num} : {ty})"


def _pr_const_typed(sym: str) -> Callable[[list[str], str], str]:
    def fn(args: list[str], _u: str) -> str:
        ty = _strip_outer_parens(args[0])
        return f"({sym} : {ty})"
    return fn


def _pr_dfunlike(args: list[str], _u: str) -> str:
    f = _strip_outer_parens(args[4])
    rest = [_atom(a) for a in args[5:]]
    if not rest:
        return f
    return f"{_atom(f)} {' '.join(rest)}"


def _pr_ite(args: list[str], _u: str) -> str:
    c = _strip_outer_parens(args[1])
    t = _strip_outer_parens(args[3])
    e = _strip_outer_parens(args[4])
    return f"if {c} then {t} else {e}"


def _pr_quotient(args: list[str], _u: str) -> str:
    return f"{_atom(args[0])} ⧸ {_atom(args[3])}"


def _pr_linear_map(args: list[str], _u: str) -> str:
    # {R} {S} [Semiring R] [Semiring S] (σ) (M) (M₂) [AddCommMonoid M] [AddCommMonoid M₂] [Module R M] [Module S M₂]
    r_ty = _strip_outer_parens(args[0])
    s_ty = _strip_outer_parens(args[1])
    sig = _strip_outer_parens(args[4])
    m1 = _strip_outer_parens(args[5])
    m2 = _strip_outer_parens(args[6])
    if r_ty == s_ty and (sig == f"RingHom.id {r_ty}" or sig == f"RingHom.id ({r_ty})"):
        return f"{_atom(m1)} →ₗ[{r_ty}] {_atom(m2)}"
    return f"LinearMap {_atom(sig)} {_atom(m1)} {_atom(m2)}"


def _pr_cont_linear_map(args: list[str], _u: str) -> str:
    # Exact Mathlib4 13-arg order:
    # {R}(0) {S}(1) [Semiring R](2) [Semiring S](3) (σ)(4) (M)(5) [Top M](6) [ACM M](7)
    # (M₂)(8) [Top M₂](9) [ACM M₂](10) [Mod R M](11) [Mod S M₂](12)
    r_ty = _strip_outer_parens(args[0])
    s_ty = _strip_outer_parens(args[1])
    sig = _strip_outer_parens(args[4])
    m1 = _strip_outer_parens(args[5])
    m2 = _strip_outer_parens(args[8])
    if r_ty == s_ty and (sig == f"RingHom.id {r_ty}" or sig == f"RingHom.id ({r_ty})"):
        return f"{_atom(m1)} →L[{r_ty}] {_atom(m2)}"
    return f"ContinuousLinearMap {_atom(sig)} {_atom(m1)} {_atom(m2)}"


def _pr_filter_cofinite(args: list[str], _u: str) -> str:
    ty = _strip_outer_parens(args[0])
    return f"(Filter.cofinite : Filter {_atom(ty)})"


def _pr_singleton(args: list[str], _u: str) -> str:
    a = _strip_outer_parens(args[3])
    return f"{{{a}}}"


def _pr_alg_map(args: list[str], _u: str) -> str:
    return f"algebraMap {_atom(args[0])} {_atom(args[1])}"


def _pr_setlike_coe(args: list[str], _u: str) -> str:
    # {A} {B} [SetLike A B] (s)
    return f"({_strip_outer_parens(args[3])} : Set {_atom(args[1])})"


def _pr_neg(args: list[str], _u: str) -> str:
    return f"-{_atom(args[2])}"


def _pr_inv(args: list[str], _u: str) -> str:
    return f"{_atom(args[2])}⁻¹"


def _pr_norm(args: list[str], _u: str) -> str:
    return f"‖{_strip_outer_parens(args[2])}‖"


def _pr_cast(args: list[str], _u: str) -> str:
    ty = _strip_outer_parens(args[0])
    v = _strip_outer_parens(args[2])
    return f"({v} : {ty})"


MATHLIB_SCHEMAS: dict[str, HeadSchema] = {
    # Number fields, completions, valuations, p-adics
    "NumberField": HeadSchema(2, (0,), (1,)),
    "NumberField.RingOfIntegers": HeadSchema(2, (0,), (1,)),
    "NumberField.RingOfIntegers.val": HeadSchema(3, (2,), (1,)),
    "Padic": HeadSchema(2, (0,), (1,)),
    "PadicInt": HeadSchema(2, (0,), (1,)),
    "PadicAlgCl": HeadSchema(2, (0,), (1,)),
    "PadicComplex": HeadSchema(2, (0,), (1,)),
    "IsDedekindDomain.HeightOneSpectrum": HeadSchema(2, (0,), (1,)),
    "IsDedekindDomain.HeightOneSpectrum.adicCompletion": HeadSchema(8, (3, 7), (1, 2, 4, 5, 6)),
    "IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers": HeadSchema(8, (3, 7), (1, 2, 4, 5, 6)),
    "IsDedekindDomain.FiniteAdeleRing": HeadSchema(7, (0, 3), (1, 2, 4, 5, 6)),
    "ValuativeRel": HeadSchema(2, (0,), (1,)),
    "ValuativeRel.ValueGroupWithZero": HeadSchema(3, (0,), (1, 2)),
    "ValuativeRel.valuation": HeadSchema(3, (0,), (1, 2)),
    "Valuation.integer": HeadSchema(5, (4,), (2, 3)),
    "IsNonarchimedeanLocalField": HeadSchema(4, (0,), (1, 2, 3)),
    "IsLocalRing": HeadSchema(2, (0,), (1,)),
    "IsLocalRing.ResidueField": HeadSchema(3, (0,), (1, 2)),
    "ValuationSubring": HeadSchema(2, (0,), (1,)),
    "ValuationSubring.ValueGroup": HeadSchema(3, (2,), (1,)),
    # Core algebra & modules
    "CharP": HeadSchema(3, (0, 2), (1,)),
    "CharZero": HeadSchema(2, (0,), (1,)),
    "Algebra": HeadSchema(4, (0, 1), (2, 3)),
    "Algebra.algebraMap": HeadSchema(5, (0, 1), (2, 3, 4), _pr_alg_map),
    "Module": HeadSchema(4, (0, 1), (2, 3)),
    "_root_.Module": HeadSchema(4, (0, 1), (2, 3)),
    "Module.Free": HeadSchema(5, (0, 1), (2, 3, 4)),
    "Module.Finite": HeadSchema(5, (0, 1), (2, 3, 4)),
    "Module.IsTorsionFree": HeadSchema(5, (0, 1), (2, 3, 4)),
    "Module.finrank": HeadSchema(5, (0, 1), (2, 3, 4)),
    "Module.End": HeadSchema(5, (0, 1), (2, 3, 4)),
    "Module.Basis": HeadSchema(6, (0, 1, 2), (3, 4, 5)),
    "StrongRankCondition": HeadSchema(2, (0,), (1,)),
    "Normal": HeadSchema(5, (0, 1), (2, 3, 4)),
    "IsAlgClosure": HeadSchema(6, (0, 1), (2, 3, 4, 5)),
    "SMulCommClass": HeadSchema(5, (0, 1, 2), (3, 4)),
    "IsScalarTower": HeadSchema(6, (0, 1, 2), (3, 4, 5)),
    "LinearMap.CompatibleSMul": HeadSchema(11, (0, 1, 4, 5), (2, 3, 6, 7, 8, 9, 10)),
    "StarRing": HeadSchema(2, (0,), (1,)),
    "ZMod.algebra": HeadSchema(4, (0, 2), (1, 3)),
    "IsLocalRing.residue": HeadSchema(3, (0,), (1, 2)),
    "ValuationSubring.decompositionSubgroup": HeadSchema(6, (0, 5), (2, 3, 4)),
    # Morphisms & equivalences
    "RingHom": HeadSchema(4, (0, 1), (2, 3)),
    "RingHom.comp": HeadSchema(8, (6, 7), (3, 4, 5)),
    "RingHom.id": HeadSchema(2, (0,), (1,)),
    "RingHom.toMonoidHom": HeadSchema(5, (4,), (2, 3), lambda a, _u: _strip_outer_parens(a[4]), preserve_univ=False),
    "MonoidHom.toOneHom": HeadSchema(5, (4,), (2, 3), lambda a, _u: _strip_outer_parens(a[4]), preserve_univ=False),
    "OneHom.toFun": HeadSchema(5, (4,), (2, 3), _pr_dfunlike, preserve_univ=False),
    "MonoidHom.comp": HeadSchema(8, (6, 7), (3, 4, 5)),
    "RingEquiv": HeadSchema(6, (0, 1), (2, 3, 4, 5)),
    "AlgHom": HeadSchema(8, (0, 1, 2), (3, 4, 5, 6, 7)),
    "AlgHom.mk": HeadSchema(10, (8, 9), (3, 4, 5, 6, 7)),
    "AlgEquiv": HeadSchema(8, (0, 1, 2), (3, 4, 5, 6, 7)),
    "MonoidHom": HeadSchema(4, (0, 1), (2, 3)),
    "AddEquiv": HeadSchema(4, (0, 1), (2, 3)),
    "LinearMap": HeadSchema(11, (4, 5, 6), (2, 3, 7, 8, 9, 10), _pr_linear_map),
    "ContinuousLinearMap": HeadSchema(13, (4, 5, 8), (2, 3, 6, 7, 9, 10, 11, 12), _pr_cont_linear_map),
    # Subobjects, quotients, groups, rings, matrices, tensors
    "Units": HeadSchema(2, (0,), (1,)),
    "Units.val": HeadSchema(3, (2,), (1,)),
    "Subgroup": HeadSchema(2, (0,), (1,)),
    "AddSubgroup": HeadSchema(2, (0,), (1,)),
    "AddSubgroup.closure": HeadSchema(3, (2,), (1,)),
    "Submonoid": HeadSchema(2, (0,), (1,)),
    "Subring": HeadSchema(2, (0,), (1,)),
    "Submodule": HeadSchema(5, (0, 1), (2, 3, 4)),
    "Subalgebra": HeadSchema(5, (0, 1), (2, 3, 4)),
    "SubringClass": HeadSchema(4, (0, 1), (2, 3)),
    "SubsemiringClass": HeadSchema(4, (0, 1), (2, 3)),
    "Ideal": HeadSchema(2, (0,), (1,)),
    "Ideal.IsPrime": HeadSchema(3, (2,), (1,)),
    "Ideal.LiesOver": HeadSchema(7, (5, 6), (1, 3, 4)),
    "Ideal.span": HeadSchema(3, (2,), (1,)),
    "Ideal.map": HeadSchema(8, (6, 7), (3, 4, 5)),
    "IntermediateField": HeadSchema(5, (0, 1), (2, 3, 4)),
    "IntermediateField.adjoin": HeadSchema(6, (0, 5), (1, 3, 4)),
    "IntermediateField.fixingSubgroup": HeadSchema(6, (5,), (1, 3, 4)),
    "TensorProduct": HeadSchema(8, (0, 2, 3), (1, 4, 5, 6, 7)),
    "TensorProduct.tmul": HeadSchema(10, (0, 8, 9), (1, 4, 5, 6, 7)),
    "Exists.choose": HeadSchema(3, (2,), ()),
    "Representation": HeadSchema(7, (0, 1, 2), (3, 4, 5, 6)),
    "Matrix.GeneralLinearGroup": HeadSchema(5, (0, 1), (2, 3, 4)),
    "Matrix.diagonal": HeadSchema(5, (4,), (2, 3)),
    "Matrix.conjTranspose": HeadSchema(5, (4,), (3,)),
    "Matrix.BlockTriangular": HeadSchema(7, (5, 6), (3, 4)),
    "RestrictedProduct": HeadSchema(4, (0, 1, 2, 3), ()),
    "CommRingCat.of": HeadSchema(2, (0,), (1,)),
    "HasQuotient.Quotient": HeadSchema(4, (0, 3), (2,), _pr_quotient, preserve_univ=False),
    # Core functions & sets
    "Filter.cofinite": HeadSchema(1, (0,), (), _pr_filter_cofinite, preserve_univ=False),
    "Set.range": HeadSchema(3, (2,), ()),
    "Set.ofPred": HeadSchema(2, (1,), ()),
    "SetLike.coe": HeadSchema(4, (3,), (2,), _pr_setlike_coe, preserve_univ=False),
    "Subtype.val": HeadSchema(3, (2,), ()),
    "Sigma": HeadSchema(2, (1,), ()),
    "Sigma.fst": HeadSchema(3, (2,), ()),
    "Equiv.symm": HeadSchema(3, (2,), ()),
    "DFunLike.coe": HeadSchema(5, (4,), (3,), _pr_dfunlike, preserve_univ=False),
    "Singleton.singleton": HeadSchema(4, (3,), (2,), _pr_singleton, preserve_univ=False),
    # Operators & literals
    "Eq": HeadSchema(3, (1, 2), (), _pr_infix("=", 1, 2), preserve_univ=False),
    "Membership.mem": HeadSchema(5, (4, 3), (2,), _pr_infix("∈", 4, 3), preserve_univ=False),
    "LE.le": HeadSchema(4, (2, 3), (1,), _pr_infix("≤", 2, 3), preserve_univ=False),
    "LT.lt": HeadSchema(4, (2, 3), (1,), _pr_infix("<", 2, 3), preserve_univ=False),
    "HAdd.hAdd": HeadSchema(6, (4, 5), (3,), _pr_bin_tight("+", 4, 5), preserve_univ=False),
    "HSub.hSub": HeadSchema(6, (4, 5), (3,), _pr_bin_tight("-", 4, 5), preserve_univ=False),
    "HMul.hMul": HeadSchema(6, (4, 5), (3,), _pr_bin_tight("*", 4, 5), preserve_univ=False),
    "HDiv.hDiv": HeadSchema(6, (4, 5), (3,), _pr_bin_tight("/", 4, 5), preserve_univ=False),
    "HPow.hPow": HeadSchema(6, (4, 5), (3,), _pr_bin_tight("^", 4, 5), preserve_univ=False),
    "HSMul.hSMul": HeadSchema(6, (4, 5), (3,), _pr_bin_tight("•", 4, 5), preserve_univ=False),
    "Neg.neg": HeadSchema(3, (2,), (1,), _pr_neg, preserve_univ=False),
    "Inv.inv": HeadSchema(3, (2,), (1,), _pr_inv, preserve_univ=False),
    "Norm.norm": HeadSchema(3, (2,), (1,), _pr_norm, preserve_univ=False),
    "OfNat.ofNat": HeadSchema(3, (0, 1), (2,), _pr_ofnat, preserve_univ=False),
    "Zero.zero": HeadSchema(2, (0,), (1,), _pr_const_typed("0"), preserve_univ=False),
    "One.one": HeadSchema(2, (0,), (1,), _pr_const_typed("1"), preserve_univ=False),
    "Top.top": HeadSchema(2, (0,), (1,), _pr_const_typed("⊤"), preserve_univ=False),
    "Bot.bot": HeadSchema(2, (0,), (1,), _pr_const_typed("⊥"), preserve_univ=False),
    "Int.cast": HeadSchema(3, (0, 2), (1,), _pr_cast, preserve_univ=False),
    "Nat.cast": HeadSchema(3, (0, 2), (1,), _pr_cast, preserve_univ=False),
    "ite": HeadSchema(5, (1, 3, 4), (2,), _pr_ite, preserve_univ=False),
}

# ==============================================================================
# 2. Pure Instance Expression & Risk Classification
# ==============================================================================

# Known canonical dictionary heads (NEVER type constructors or value terms)
CANONICAL_INST_EXACT = {
    "Rat.commRing", "Rat.commSemiring", "Rat.semiring", "Rat.instField",
    "Int.instCommSemiring", "Int.instSemiring", "Int.instAdd", "Int.instMul",
    "Real.instLE", "Real.instOne", "Real.instZero", "Real.instNormedField",
    "Complex.instSemiring", "Complex.instMul", "Complex.instAddCommMonoid",
    "Complex.instZero", "Complex.instOne", "Complex.instNeg",
    "Complex.instNonUnitalCommRing", "Complex.instStarRing", "Complex.instRCLike",
    "Complex.instNormedAddCommGroup", "Complex.instNormedField",
    "Fin.fintype", "instDecidableEqFin", "instDecidableEqBool", "instAddNat",
    "instOfNatNat", "instOfNat", "instHAdd", "instHMul", "instHSub", "instHDiv",
    "instHPow", "instHSMul", "instIsDomain", "instFieldPadic",
    "Algebra.id", "Algebra.toModule", "Algebra.toSMul", "Algebra.to_smulCommClass",
    "IsScalarTower.right", "IsScalarTower.left",
    "Matrix.semiring", "Matrix.instHMulOfFintypeOfMulOfAddCommMonoid",
    "ULift.semiring", "Pi.monoid", "Pi.addCommMonoid", "Pi.instAdd", "Pi.instSub",
    "Pi.Function.module", "Submodule.setLike", "Submodule.hasQuotient",
    "Subring.toCommRing", "AlgEquiv.aut", "IsLocalRing.ResidueField.field",
    "PadicAlgCl.normedField", "Field.henselian",
    "Module.Flat.isTorsionFree", "Module.FaithfullyFlat.toFlat",
    "Module.Free.of_divisionRing", "IsPrincipalIdealRing.isDedekindDomain",
    "IsDomain.of_isSimpleRing", "IsPrincipalIdealRing.of_isSimpleRing",
}

RE_INST_TAIL = re.compile(
    r"^(?:to[A-Z_]|inst[A-Z0-9_]|commRing|commSemiring|semiring|ring|field|monoid|group|"
    r"addCommMonoid|addCommGroup|normedField|normedRing|normedAddCommGroup|topologicalSpace|"
    r"measurableSpace|fintype|decidableEq|setLike|hasQuotient|module|algebra|starRing)$"
)

# Risk patterns for dropped / folded instance arguments
HIGH_RISK_PATTERNS = [
    ("custom_local_instance_complRel", re.compile(r"\bGlobalTheory\.LocalData\.complRel\b")),
    ("custom_local_instance_isLocalField", re.compile(r"\bGlobalTheory\.LocalData\.isLocalField\b")),
    ("custom_project_instance_helper", re.compile(r"\bUpperTheory\.Reformulated\.B\.[A-Za-z0-9_]+\.(?:aux\d+|algRes|inst[A-Za-z0-9_]*)\b")),
    ("custom_project_instance_other", re.compile(r"\b(?:GlobalTheory|Formalism|Development|ReciprocityTheory|CompanionTheory)\.[A-Za-z0-9_.]*inst[A-Za-z0-9_]*\b")),
]

DIAMOND_RISK_PATTERNS = [
    ("diamond_Normed_or_CStar", re.compile(r"\b(?:NormedRing|NormedAddCommGroup|NormedField|InnerProductSpace|CStarAlgebra|CommCStarAlgebra|SeminormedAddCommGroup)\b")),
    ("diamond_Valuative_or_LocalField", re.compile(r"\b(?:ValuativeRel|IsNonarchimedeanLocalField|IsDiscreteValuationRing|ValuationSubring|PadicAlgCl\.normedField)\b")),
    ("diamond_Topology_or_Measure", re.compile(r"\b(?:TopologicalSpace|UniformSpace|MeasurableSpace|MeasureTheory\.Lp|Measure)\b")),
    ("diamond_Algebra_or_ScalarTower", re.compile(r"\b(?:IsAlgClosure|IsScalarTower|SMulCommClass|CompatibleSMul|DivisionRing\.toRatAlgebra|AlgebraicClosure\.instAlgebra|FiniteAdeleRing\.instAlgebra)\b")),
    ("diamond_CharP_or_Quotient", re.compile(r"\b(?:CharP|HasQuotient|Submodule\.hasQuotient|Ideal\.instHasQuotient)\b")),
]


def is_pure_instance_head(head: str) -> bool:
    h = head.split(".{", 1)[0].rstrip(".")
    if h in CANONICAL_INST_EXACT:
        return True
    tail = h.rsplit(".", 1)[-1]
    if RE_INST_TAIL.match(tail):
        return True
    if ".inst" in h or ".to_" in h:
        return True
    return False


def is_pure_instance_expr(expr: str) -> bool:
    """True iff `expr` is a pure synthesized typeclass dictionary term (safe to fold to `_` in Tier 2)."""
    s = _strip_outer_parens(expr)
    if not s:
        return False
    # Named instance variable like `inst`, `inst_1`, `hl`, `hP`? Only `inst` or `inst_\d+`!
    if re.fullmatch(r"inst(?:_\d+)?", s):
        return True
    if s in CANONICAL_INST_EXACT:
        return True
    # Application rooted at `@Head` or `Head`
    m = re.match(r"^@?([A-Za-z_][A-Za-z0-9_.']*(?:\.\{[^}]*\})?)(?:\s|$)", s)
    if not m:
        return False
    head = m.group(1)
    if not is_pure_instance_head(head):
        return False
    # Extra safety: never treat lambda / forall / arrow types as instance exprs
    if " → " in s and not s.startswith("@"):
        return False
    return True


def classify_inst_risks(raw_inst_text: str, risks: dict[str, Counter]) -> None:
    for label, pat in HIGH_RISK_PATTERNS:
        if pat.search(raw_inst_text):
            risks["HIGH"][label] += 1
    for label, pat in DIAMOND_RISK_PATTERNS:
        if pat.search(raw_inst_text):
            risks["MEDIUM"][label] += 1


# ==============================================================================
# 3. DuckDB Project-Local Binder Schema Loader
# ==============================================================================

def _find_matching(s: str, start: int, o: str, c: str) -> int:
    d = 0
    i = start
    n = len(s)
    while i < n:
        ch = s[i]
        if ch == '"':
            i += 1
            while i < n and s[i] != '"':
                if s[i] == "\\":
                    i += 1
                i += 1
        elif ch == o:
            d += 1
        elif ch == c:
            d -= 1
            if d == 0:
                return i
        i += 1
    return -1


def _find_top_level_char(s: str, target: str) -> int:
    dp = db = dc = da = 0
    i = 0
    n = len(s)
    while i < n:
        ch = s[i]
        if ch == "(":
            dp += 1
        elif ch == ")":
            dp = max(0, dp - 1)
        elif ch == "[":
            db += 1
        elif ch == "]":
            db = max(0, db - 1)
        elif ch == "{":
            dc += 1
        elif ch == "}":
            dc = max(0, dc - 1)
        elif ch == "⟨":
            da += 1
        elif ch == "⟩":
            da = max(0, da - 1)
        elif dp == db == dc == da == 0 and ch == target:
            if target == ":" and i + 1 < n and s[i + 1] == "=":
                i += 2
                continue
            return i
        i += 1
    return -1


def parse_project_binders_from_decl_text(decl_text: str) -> tuple[str, HeadSchema] | None:
    """
    Parse exact UNTRUNCATED binder schema from a full declaration's source text.
    Detects phantom (uninferable) implicit binders `{v : T}` that do NOT appear in
    any explicit argument type or the return type (e.g., `KwF`'s `{E}`, `hcompl`'s `{K}`,
    `IsSplit`'s `{E}`):
      - Named phantom implicit binders are recorded in `phantom_named` so calls preserve `(v := arg)`!
      - Unnamed phantom implicit binders cause safe fallback to Tier 2 (return None).
    """
    assign_pos = find_top_level_assign(decl_text)
    sig = decl_text[:assign_pos].strip() if assign_pos != -1 else decl_text.strip()
    m = re.match(
        r"^(?:@\[[^\]]+\]\s*)*(?:(?:private|protected|noncomputable)\s+)*(?:theorem|lemma|def|abbrev)\s+"
        r"((?:[^\W0-9][\w'\u2080-\u2089]*)(?:\.[^\W0-9][\w'\u2080-\u2089]*)*)(?:\.\{[^}]*\})?\s*(.*)$",
        sig,
        re.DOTALL,
    )
    if not m:
        return None
    nm = m.group(1).rstrip(".")
    if nm.startswith("_root_."):
        nm = nm[7:]
    rest = m.group(2).strip()
    # Each entry: (kind: 'E'|'I'|'C', var_name: str|None, type_text: str)
    binders: list[tuple[str, str | None, str]] = []
    ret_type_text = ""

    def unpack_group(inner: str, kind: str) -> list[tuple[str, str | None, str]]:
        cpos = _find_top_level_char(inner, ":")
        if cpos != -1:
            lhs = inner[:cpos].strip()
            rhs = inner[cpos + 1 :].strip()
            names = lhs.split()
            if names and all(re.fullmatch(r"[^\W0-9][\w'\u2080-\u2089]*", x) for x in names):
                return [(kind, x, rhs) for x in names]
        return [(kind, None, inner)]

    def scan_prefix_binders(txt: str, start: int) -> tuple[list[tuple[str, str | None, str]], int]:
        out: list[tuple[str, str | None, str]] = []
        i = start
        n = len(txt)
        while i < n:
            while i < n and txt[i].isspace():
                i += 1
            if i >= n or txt[i] not in "([{":
                break
            ch = txt[i]
            close = {"(": ")", "[": "]", "{": "}"}[ch]
            j = _find_matching(txt, i, ch, close)
            if j == -1:
                return [], -1
            out.extend(unpack_group(txt[i + 1 : j].strip(), {"(": "E", "{": "I", "[": "C"}[ch]))
            i = j + 1
        return out, i

    if rest.startswith(":"):
        i = 1
        n = len(rest)
        while i < n and rest[i].isspace():
            i += 1
        if rest[i : i + 1] == "∀":
            return None
        while i < n:
            while i < n and rest[i].isspace():
                i += 1
            if i >= n:
                break
            ch = rest[i]
            if ch in "([{":
                close = {"(": ")", "[": "]", "{": "}"}[ch]
                j = _find_matching(rest, i, ch, close)
                if j == -1:
                    return None
                k = j + 1
                while k < n and rest[k].isspace():
                    k += 1
                if rest[k : k + 1] != "→":
                    ret_type_text = rest[i:].strip()
                    break
                binders.extend(unpack_group(rest[i + 1 : j].strip(), {"(": "E", "{": "I", "[": "C"}[ch]))
                i = k + 1
            else:
                apos = _find_top_level_char(rest[i:], "→")
                if apos == -1:
                    ret_type_text = rest[i:].strip()
                    break
                seg = rest[i : i + apos].strip()
                if not seg:
                    break
                binders.append(("E", None, seg))
                i = i + apos + 1
    else:
        b, ni = scan_prefix_binders(rest, 0)
        if ni == -1 or not b:
            return None
        k = ni
        while k < len(rest) and rest[k].isspace():
            k += 1
        if k >= len(rest) or rest[k] != ":":
            return None
        binders.extend(b)
        ret_type_text = rest[k + 1 :].strip()

    if not binders:
        return None

    # Compute inferable variable set via fixpoint starting from explicit param types + return type
    RE_WORD = re.compile(r"(?<![\w'.\u2080-\u2089])([^\W0-9][\w'\u2080-\u2089]*)(?![\w'.\u2080-\u2089])")
    inferable_texts = [ty for kind, _, ty in binders if kind == "E"] + [ret_type_text]
    inferable_vars: set[str] = set()
    for t in inferable_texts:
        inferable_vars.update(RE_WORD.findall(t))
    # Transitive closure through implicit binder types (NOT through `[C]` instances, which
    # cannot be inferred before their carrier types are known!)
    changed = True
    while changed:
        changed = False
        for kind, vname, ty in binders:
            if kind == "I" and vname and vname in inferable_vars:
                new_ids = set(RE_WORD.findall(ty)) - inferable_vars
                if new_ids:
                    inferable_vars.update(new_ids)
                    changed = True

    phantom_named: list[tuple[int, str]] = []
    for idx, (kind, vname, _ty) in enumerate(binders):
        if kind == "I":
            if vname is None:
                # Unnamed implicit binder: unsafe to assume inferability -> fallback to Tier 2
                return None
            if vname not in inferable_vars:
                phantom_named.append((idx, vname))

    keep = tuple(idx for idx, (k, _, _) in enumerate(binders) if k == "E")
    inst_pos = tuple(idx for idx, (k, _, _) in enumerate(binders) if k == "C")
    if len(keep) + len(phantom_named) >= len(binders):
        return None
    return nm, HeadSchema(
        arity=len(binders),
        keep=keep,
        inst_pos=inst_pos,
        phantom_named=tuple(phantom_named),
    )


def load_project_schemas_from_sources(targets: list[dict], src_root: Path) -> dict[str, HeadSchema]:
    """
    Parse exact UNTRUNCATED project-local binder schemas directly from the full source text
    of all target files (never relying on DuckDB's truncated `signature` column!).
    """
    schemas: dict[str, HeadSchema] = {}
    for t in targets:
        raw = (src_root / t["rel_path"]).read_text(encoding="utf-8", errors="replace")
        for is_decl, blk in split_top_level_blocks(raw):
            if not is_decl:
                continue
            parsed = parse_project_binders_from_decl_text(blk)
            if parsed is not None:
                nm, sch = parsed
                if nm not in MATHLIB_SCHEMAS:
                    schemas[nm] = sch
    return schemas


# ==============================================================================
# 4. Balanced Lean 4 Expression Rewriter (Bottom-Up)
# ==============================================================================

STOP_KEYWORDS = {
    "where", "with", "in", "then", "else", "by", "do", "match", "have", "let",
    "letI", "show", "from", "return", "end", "section", "namespace", "theorem",
    "lemma", "def", "abbrev", "structure", "class", "inductive", "instance",
    "private", "protected", "noncomputable", "open", "import", "variable", "universe",
    "attribute", "set_option", "export", "mutual", "axiom", "opaque",
}

STOP_TOKENS = {
    "→", "↦", "=>", ":=", ":", ",", ";", "|", "↔", "∧", "∨", "=", "≠",
    "≤", "<", "≥", ">", "∈", "∉", "+", "-", "*", "/", "^", "•", "∘",
    "∩", "∪", "⊆", "⊂", "⧸", "×", "⊗", "∀", "∃", "fun",
}


def split_code_preserving_comments(text: str) -> list[tuple[str, str]]:
    """Split text into chunks of ('code', s) and ('raw', s) where 'raw' is comments/strings."""
    out: list[tuple[str, str]] = []
    i = 0
    n = len(text)
    buf: list[str] = []

    def flush_code():
        if buf:
            out.append(("code", "".join(buf)))
            buf.clear()

    while i < n:
        # Nested block comment /- ... -/
        if text[i : i + 2] == "/-":
            flush_code()
            start = i
            depth = 1
            i += 2
            while i < n and depth > 0:
                if text[i : i + 2] == "/-":
                    depth += 1
                    i += 2
                elif text[i : i + 2] == "-/":
                    depth -= 1
                    i += 2
                else:
                    i += 1
            out.append(("raw", text[start:i]))
        # Line comment -- ... \n
        elif text[i : i + 2] == "--":
            flush_code()
            nl = text.find("\n", i)
            if nl == -1:
                out.append(("raw", text[i:]))
                i = n
            else:
                out.append(("raw", text[i:nl]))
                i = nl
        # String literal
        elif text[i] == '"':
            flush_code()
            start = i
            i += 1
            while i < n and text[i] != '"':
                if text[i] == "\\" and i + 1 < n:
                    i += 2
                else:
                    i += 1
            if i < n:
                i += 1
            out.append(("raw", text[start:i]))
        else:
            buf.append(text[i])
            i += 1
    flush_code()
    return out


class DeElaborator:
    def __init__(self, project_schemas: dict[str, HeadSchema]):
        self.project_schemas = project_schemas
        self.stats = Counter()
        self.risks: dict[str, Counter] = {"HIGH": Counter(), "MEDIUM": Counter(), "LOW": Counter()}

    def _lookup_schema(self, head_base: str) -> HeadSchema | None:
        if head_base in MATHLIB_SCHEMAS:
            return MATHLIB_SCHEMAS[head_base]
        if head_base in self.project_schemas:
            return self.project_schemas[head_base]
        return None

    def _scan_one_arg(self, s: str, pos: int) -> tuple[str, int] | None:
        """Scan one syntactic Lean argument starting at `pos` (after skipping whitespace)."""
        n = len(s)
        i = pos
        while i < n and s[i].isspace():
            i += 1
        if i >= n:
            return None
        ch = s[i]
        # Closing delimiters stop argument scanning
        if ch in ")]}⟩":
            return None
        # Leading prefix operators `↥`, `↑`, `¬` attached directly to an atom/group
        if ch in "↥↑" and i + 1 < n and not s[i + 1].isspace():
            sub = self._scan_one_arg(s, i + 1)
            if sub is None:
                return None
            return ch + sub[0], sub[1]
        # Balanced delimiters `(...)`, `[...]`, `{...}`, `⟨...⟩`
        if ch in "([{⟨":
            close = {"(": ")", "[": "]", "{": "}", "⟨": "⟩"}[ch]
            j = _find_matching(s, i, ch, close)
            if j == -1:
                return None
            return s[i : j + 1], j + 1
        # Trailing lambda `fun ... ↦ ...` ONLY if explicitly present as an argument!
        if s[i : i + 4] == "fun " or s[i : i + 4] == "fun\n":
            # Scan to the end of the enclosing expression (next unbalanced closing delim or top-level `,` / `;` / `:=`)
            j = self._scan_lambda_extent(s, i)
            return s[i:j].rstrip(), j
        # Check multi-char stop tokens
        for st in (":=", "=>"):
            if s[i : i + len(st)] == st:
                return None
        if ch in STOP_TOKENS:
            return None
        # Identifier / numeral / `_` / `@Head` (note: unparenthesized `@` starts a NEW app, NOT an arg? Wait: in Lean `f @g` is rare; don't consume `@`!)
        if ch == "@":
            return None
        # Identifier or numeral or `_` (FULL Unicode support, NEVER greedily consume trailing `.` before `.{...}`!)
        m = re.match(r"^(?:(?:[^\W0-9][\w'\u2080-\u2089]*)(?:\.[^\W0-9][\w'\u2080-\u2089]*)*(?:\.\{[^}]*\})?|[0-9]+(?:\.[0-9]+)?)", s[i:])
        if not m:
            return None
        tok = m.group(0)
        if tok in STOP_KEYWORDS:
            return None
        return tok, i + len(tok)

    def _scan_lambda_extent(self, s: str, start: int) -> int:
        dp = db = dc = da = 0
        quant_depth = 0
        i = start
        n = len(s)
        while i < n:
            ch = s[i]
            if ch == '"':
                i += 1
                while i < n and s[i] != '"':
                    if s[i] == "\\":
                        i += 1
                    i += 1
            elif ch == "(":
                dp += 1
            elif ch == ")":
                if dp == 0:
                    return i
                dp -= 1
            elif ch == "[":
                db += 1
            elif ch == "]":
                if db == 0:
                    return i
                db -= 1
            elif ch == "{":
                dc += 1
            elif ch == "}":
                if dc == 0:
                    return i
                dc -= 1
            elif ch == "⟨":
                da += 1
            elif ch == "⟩":
                if da == 0:
                    return i
                da -= 1
            elif dp == db == dc == da == 0:
                if ch in "∀∃":
                    quant_depth += 1
                elif ch == ",":
                    if quant_depth > 0:
                        quant_depth -= 1
                    else:
                        return i
                elif s[i : i + 2] == ":=" or ch == ";":
                    return i
            i += 1
        return n

    def _rewrite_at_app(self, head_full: str, args: list[str], in_parens: bool) -> str | None:
        """
        Rewrite `@head_full arg0 arg1 ...`.
        Returns transformed string, or None to keep original unchanged.
        """
        univ = ""
        if ".{" in head_full:
            head_base, rest = head_full.split(".{", 1)
            univ = ".{" + rest
        else:
            head_base = head_full
        head_base_clean = head_base.rstrip(".")

        is_project = head_base_clean not in MATHLIB_SCHEMAS and head_base_clean in self.project_schemas
        schema = self._lookup_schema(head_base_clean)

        # Tier 1: Exact Verified Schema
        if schema is not None and len(args) >= schema.arity:
            # Extra strict guard for project-local schemas: every dropped inst_pos argument
            # must look like an actual instance expr/var (never drop an explicit value arg by mistake!)
            schema_safe = True
            if is_project:
                for idx in schema.inst_pos:
                    a_s = _strip_outer_parens(args[idx])
                    if not (
                        a_s == "_"
                        or is_pure_instance_expr(args[idx])
                        or re.fullmatch(r"(?:inst(?:_\d+)?|hl|hP|h[A-Za-z0-9_]*)", a_s)
                    ):
                        schema_safe = False
                        break
            if schema_safe:
                for idx in schema.inst_pos:
                    if idx < len(args):
                        classify_inst_risks(args[idx], self.risks)

                has_univ_var = bool(univ and re.search(r"[^\W0-9]", univ))
                u_emit = univ if (schema.preserve_univ and has_univ_var) else ""

                if schema.printer is not None:
                    if head_base_clean in ("DFunLike.coe", "OneHom.toFun"):
                        res = schema.printer(args, u_emit)
                        self.stats["tier1_schema_rewrites"] += 1
                        return res
                    core = schema.printer(args[: schema.arity], u_emit)
                    extra = args[schema.arity :]
                    if extra:
                        res = f"({core}) " + " ".join(_atom(e) for e in extra)
                    else:
                        res = core
                    self.stats["tier1_schema_rewrites"] += 1
                    return res
                else:
                    named_phantoms = [
                        f"({vname} := {_strip_outer_parens(args[idx])})"
                        for idx, vname in schema.phantom_named
                    ]
                    if named_phantoms:
                        self.stats["phantom_named_preserved"] += len(named_phantoms)
                    kept = [_atom(args[idx]) for idx in schema.keep]
                    extra = [_atom(a) for a in args[schema.arity :]]
                    emit_head = head_base_clean + u_emit
                    all_kept = named_phantoms + kept + extra
                    res = f"{emit_head} {' '.join(all_kept)}" if all_kept else emit_head
                    self.stats["tier1_schema_rewrites"] += 1
                    return res

        # Tier 2: Arity-Preserving Wildcard Folding for Uncataloged Heads
        # ONLY fold arguments that are PURE synthesized instance chains (NOT bare variables like `inst` unless clearly pp.explicit,
        # and NEVER type constructors or value terms!).
        # Specifically: fold args that start with `(@` or `(` containing a pure instance head (`*.to*`, `*inst*`, canonical dict)
        # AND have length >= 22 chars (so we collapse real instance trees, not tiny tokens).
        new_args = list(args)
        folded_any = False
        for idx, a in enumerate(args):
            a_stripped = _strip_outer_parens(a)
            if len(a_stripped) >= 18 and is_pure_instance_expr(a):
                classify_inst_risks(a, self.risks)
                new_args[idx] = "_"
                folded_any = True
                self.stats["tier2_inst_folded"] += 1
        if folded_any:
            self.risks["LOW"]["tier2_wildcard_synthesis"] += 1
            self.stats["tier2_head_rewrites"] += 1
            return f"@{head_full} " + " ".join(new_args)

        return None

    def transform_expr(self, expr: str, tactic_mode: bool = False) -> str:
        """
        Bottom-up single-pass-to-fixpoint transformation of a Lean expression string.
        Recursively simplifies inside balanced `(...)`, `[...]`, `{...}`, `⟨...⟩` first,
        then rewrites `@Head args...` at the current level.
        """
        if "@" not in expr:
            return expr
        # In tactic_mode, only touch expressions that genuinely have pp.explicit synthesized chains
        if tactic_mode and not (
            "@Semiring.to" in expr
            or "@CommRing.to" in expr
            or "@DivisionRing.to" in expr
            or "@Field.to" in expr
            or "@AddCommGroup.to" in expr
            or "@CommSemiring.to" in expr
            or "@Ring.to" in expr
            or "@DFunLike.coe" in expr
            or "@Membership.mem" in expr
        ):
            return expr

        # Step 1: Recurse inside every top-level balanced delimiter group first (bottom-up!)
        out_parts: list[str] = []
        i = 0
        n = len(expr)
        while i < n:
            ch = expr[i]
            if ch in "([{⟨":
                close = {"(": ")", "[": "]", "{": "}", "⟨": "⟩"}[ch]
                j = _find_matching(expr, i, ch, close)
                if j != -1:
                    inner = expr[i + 1 : j]
                    new_inner = self.transform_expr(inner, tactic_mode=tactic_mode)
                    # If parenthesized group now wraps a simple atom with no spaces or already wrapped, keep parens
                    # (outer rewrite will decide whether parens are needed!)
                    out_parts.append(ch + new_inner + close)
                    i = j + 1
                    continue
            out_parts.append(ch)
            i += 1
        cur = "".join(out_parts)

        # Step 2: Scan `cur` at top level for `@Head args...` applications and rewrite them
        res_parts: list[str] = []
        i = 0
        n = len(cur)
        while i < n:
            ch = cur[i]
            # Skip over balanced groups (already processed in Step 1!)
            if ch in "([{⟨":
                close = {"(": ")", "[": "]", "{": "}", "⟨": "⟩"}[ch]
                j = _find_matching(cur, i, ch, close)
                if j != -1:
                    res_parts.append(cur[i : j + 1])
                    i = j + 1
                    continue
            # Check for `@Head` (NOT preceded by identifier char -> avoids `x@⟨...⟩` as-patterns;
            # NOT followed by `[` -> avoids `@[simp]` attributes)
            if ch == "@" and (i == 0 or not re.match(r"[\w'.\u2080-\u2089]", cur[i - 1])):
                m = re.match(r"^@((?:[^\W0-9][\w'\u2080-\u2089]*)(?:\.[^\W0-9][\w'\u2080-\u2089]*)*(?:\.\{[^}]*\})?)", cur[i:])
                if m:
                    head_full = m.group(1)
                    arg_start = i + len(m.group(0))
                    # Collect consecutive arguments
                    args: list[str] = []
                    cursor = arg_start
                    while True:
                        scanned = self._scan_one_arg(cur, cursor)
                        if scanned is None:
                            break
                        arg_txt, next_pos = scanned
                        args.append(arg_txt)
                        cursor = next_pos
                    if args:
                        rewritten = self._rewrite_at_app(head_full, args, in_parens=False)
                        if rewritten is not None:
                            # Wrap in parens if preceded by an operator/head where precedence could shift,
                            # except if already whole string
                            if i == 0 and cursor == n:
                                res_parts.append(rewritten)
                            else:
                                # Check if rewritten contains spaces/infix and sits inside a larger expr
                                if any(op in rewritten for op in (" = ", " ∈ ", " ≤ ", " < ", "if ")):
                                    # Only wrap if immediate neighbors aren't `:` / `→` / `↦` / `,` / `∀`
                                    prev_nonws = "".join(res_parts).rstrip()[-1:] if res_parts else ""
                                    next_nonws = cur[cursor:].lstrip()[:1]
                                    if prev_nonws in ("", ":", "→", "↦", ",", "∀", "∃", "↔", "∧", "∨") and next_nonws in ("", "→", ",", "↔", "∧", "∨", ":"):
                                        res_parts.append(rewritten)
                                    else:
                                        res_parts.append(f"({rewritten})")
                                else:
                                    res_parts.append(rewritten)
                            i = cursor
                            continue
            res_parts.append(ch)
            i += 1
        return "".join(res_parts)


# ==============================================================================
# 5. Declaration-Level Formatting, Unused Instance Binder Cleanup & Verification
# ==============================================================================

RE_DECL_START = re.compile(
    r"^(?:@\[[^\]]+\]\s*)*(?:(?:private|protected|noncomputable|unsafe|partial|local|scoped)\s+)*"
    r"(theorem|lemma|def|abbrev|structure|class|inductive|instance|axiom|opaque)\s+"
    r"([A-Za-z_][A-Za-z0-9_.']*(?:\.\{[^}]*\})?)?"
)

RE_UNUSED_INST_BINDER = re.compile(r"\[(inst(?:_\d+)?)\s*:\s*([^\[\]]+)\]")


def extract_decls_from_text(text: str) -> list[tuple[str, str]]:
    """Extract (kind, clean_name) of all top-level declarations (comment-stripped)."""
    chunks = split_code_preserving_comments(text)
    code_only = "".join(s if k == "code" else ("\n" * s.count("\n")) for k, s in chunks)
    decls = []
    for ln in code_only.splitlines():
        if not ln or ln[0].isspace():
            continue
        m = RE_DECL_START.match(ln)
        if m:
            kind = m.group(1)
            nm = (m.group(2) or "<anonymous>").split(".{", 1)[0].rstrip(".")
            decls.append((kind, nm))
    return decls


def check_balanced_delimiters(text: str) -> tuple[bool, str]:
    """Verify balanced (), [], {}, ⟨⟩ after stripping comments and string literals."""
    chunks = split_code_preserving_comments(text)
    code_only = "".join(s for k, s in chunks if k == "code")
    # Strip char literals like `'a'` (not primes like `x'`)
    code_only = re.sub(r"'(?:\\.|[^'\\])'", " ", code_only)
    stack: list[str] = []
    pairs = {")": "(", "]": "[", "}": "{", "⟩": "⟨"}
    opens = set(pairs.values())
    for ch in code_only:
        if ch in opens:
            stack.append(ch)
        elif ch in pairs:
            if not stack or stack[-1] != pairs[ch]:
                return False, f"mismatched closing '{ch}' (stack tail={stack[-3:]})"
            stack.pop()
    if stack:
        return False, f"unclosed delimiters remaining: {stack[-5:]}"
    return True, "ok"


RE_NOTATION_INST_LEAK = re.compile(
    r"(?:→L\[[^\]]+\]|→ₗ\[[^\]]+\]|⧸)\s*\(?@(?:UniformSpace|TopologicalSpace|Semiring|CommRing|"
    r"CommSemiring|DivisionRing|DivisionSemiring|Field|AddCommMonoid|AddCommGroup|Module|"
    r"Ideal\.inst|Submodule\.hasQuotient|inst[A-Z])"
)


def check_notation_instance_leaks(text: str) -> list[str]:
    """Regression guard: detect any leaked typeclass instance immediately after `→L[...]`, `→ₗ[...]`, or `⧸`."""
    chunks = split_code_preserving_comments(text)
    code_only = "".join(s for k, s in chunks if k == "code")
    return [m.group(0) for m in RE_NOTATION_INST_LEAK.finditer(code_only)]


def count_forbidden_tokens(text: str) -> dict[str, int]:
    chunks = split_code_preserving_comments(text)
    code_only = "".join(s for k, s in chunks if k == "code")
    return {
        "sorry": len(re.findall(r"\bsorry\b", code_only)),
        "axiom": len(re.findall(r"\baxiom\b", code_only)),
        "admit": len(re.findall(r"\badmit\b", code_only)),
    }


RE_NONDECL_CMD = re.compile(
    r"^(?:attribute|open|namespace|end|section|variable|universe|set_option|noncomputable\s+section|export|import|include|omit)\b"
)


def split_top_level_blocks(text: str) -> list[tuple[bool, str]]:
    """
    Split a Lean file into top-level chunks: `(is_decl, chunk_text)`.
    Every declaration starts at column 0 matching `RE_DECL_START`; top-level commands
    like `attribute [local instance] ...`, `end ...`, `section`, `namespace`, `open`
    ALWAYS start a new non-decl block so they are NEVER swallowed into a preceding def body!
    """
    lines = text.splitlines(keepends=True)
    blocks: list[tuple[bool, list[str]]] = []
    cur_is_decl = False
    cur_lines: list[str] = []
    in_block_comment = 0

    for ln in lines:
        starts_decl = False
        starts_nondecl = False
        if in_block_comment == 0 and ln and not ln[0].isspace() and not ln.startswith("--"):
            if RE_DECL_START.match(ln):
                starts_decl = True
            elif RE_NONDECL_CMD.match(ln):
                starts_nondecl = True
        if starts_decl:
            if cur_lines:
                blocks.append((cur_is_decl, cur_lines))
            cur_is_decl = True
            cur_lines = [ln]
        elif starts_nondecl:
            if cur_lines:
                blocks.append((cur_is_decl, cur_lines))
            cur_is_decl = False
            cur_lines = [ln]
        else:
            cur_lines.append(ln)
        in_block_comment += ln.count("/-") - ln.count("-/")
        if in_block_comment < 0:
            in_block_comment = 0
    if cur_lines:
        blocks.append((cur_is_decl, cur_lines))
    return [(flag, "".join(ls)) for flag, ls in blocks]


def compact_whitespace_in_decl_expr(expr: str) -> str:
    """
    Collapse multi-line indentation bloat left behind after removing huge `@` subtrees,
    producing clean, readable multi-line Lean 4 signatures/definitions (~110-char soft wrap).
    """
    # Normalize runs of whitespace/newlines inside the expression to single spaces first
    s = re.sub(r"[ \t]*\n[ \t]*", " ", expr)
    s = re.sub(r"  +", " ", s).strip()
    # Clean redundant spaces inside parens/brackets
    s = re.sub(r"\(\s+", "(", s)
    s = re.sub(r"\s+\)", ")", s)
    s = re.sub(r"\[\s+", "[", s)
    s = re.sub(r"\s+\]", "]", s)
    # Soft-break long single lines cleanly at top-level `→` or `∀` or `:=` or `,` (optional pretty layout)
    if len(s) <= 120:
        return s
    # Insert line breaks at top-level ` → ` or ` ∧ ` or ` ↔ ` when line length exceeds ~100 chars
    out: list[str] = []
    cur_len = 0
    dp = db = dc = da = 0
    i = 0
    n = len(s)
    while i < n:
        ch = s[i]
        if ch == "(":
            dp += 1
        elif ch == ")":
            dp = max(0, dp - 1)
        elif ch == "[":
            db += 1
        elif ch == "]":
            db = max(0, db - 1)
        elif ch == "{":
            dc += 1
        elif ch == "}":
            dc = max(0, dc - 1)
        elif ch == "⟨":
            da += 1
        elif ch == "⟩":
            da = max(0, da - 1)
        if dp == 0 and db == 0 and dc == 0 and da == 0 and cur_len >= 95:
            if s[i : i + 3] in (" → ", " ∧ ", " ↔ ", " ↦ "):
                out.append(s[i : i + 2] + "\n    ")
                i += 3
                cur_len = 4
                continue
            if ch == " " and i + 1 < n and s[i + 1] in "([{":
                out.append("\n    ")
                i += 1
                cur_len = 4
                continue
        out.append(ch)
        cur_len += 1
        i += 1
    return "".join(out)


def find_top_level_assign(decl_text: str) -> int:
    """Find index of top-level `:=` separating signature from body (outside comments/strings/parens)."""
    chunks = split_code_preserving_comments(decl_text)
    offset = 0
    dp = db = dc = da = 0
    for kind, s in chunks:
        if kind == "raw":
            offset += len(s)
            continue
        i = 0
        n = len(s)
        while i < n:
            ch = s[i]
            if ch == "(":
                dp += 1
            elif ch == ")":
                dp = max(0, dp - 1)
            elif ch == "[":
                db += 1
            elif ch == "]":
                db = max(0, db - 1)
            elif ch == "{":
                dc += 1
            elif ch == "}":
                dc = max(0, dc - 1)
            elif ch == "⟨":
                da += 1
            elif ch == "⟩":
                da = max(0, da - 1)
            elif dp == db == dc == da == 0 and s[i : i + 2] == ":=":
                return offset + i
            i += 1
        offset += len(s)
    return -1


def clean_unused_inst_binders(decl_text: str) -> str:
    """Replace `[inst_k : T]` with `[T]` ONLY if `inst_k` is not referenced anywhere else in `decl_text`."""
    def repl(m: re.Match) -> str:
        var = m.group(1)
        ty = m.group(2).strip()
        # Count occurrences of `var` as whole word in entire declaration
        hits = len(re.findall(rf"\b{re.escape(var)}\b", decl_text))
        if hits == 1:
            return f"[{ty}]"
        return m.group(0)
    return RE_UNUSED_INST_BINDER.sub(repl, decl_text)


def is_pp_explicit_region(s: str) -> bool:
    """True iff region contains genuine `pp.explicit` serialized typeclass/operator bloat."""
    return bool(
        "@Semiring.to" in s
        or "@CommRing.to" in s
        or "@DivisionRing.to" in s
        or "@Field.to" in s
        or "@AddCommGroup.to" in s
        or "@CommSemiring.to" in s
        or "@Ring.to" in s
        or "@NumberField.RingOfIntegers" in s
        or "@NumberField.inst" in s
        or "@Padic " in s
        or "@PadicAlgCl " in s
        or "@DFunLike.coe" in s
        or "@Membership.mem" in s
        or "@OfNat.ofNat" in s
        or "@HAdd.hAdd" in s
        or "@HMul.hMul" in s
        or "@HSMul.hSMul" in s
        or "@Set.ofPred" in s
        or "@SetLike.coe" in s
        or "@Eq " in s
        or "@Eq.{" in s
        or "@Algebra " in s
        or "@RingHom " in s
        or "@Subgroup " in s
        or "@Units " in s
        or "@Ideal " in s
        or "@Submodule " in s
        or "@TensorProduct " in s
        or "@ValuativeRel " in s
        or "@Valuation.integer" in s
        or "@IsLocalRing.ResidueField" in s
        or "@IsNonarchimedeanLocalField " in s
    )


def transform_declaration(decl_text: str, de: DeElaborator) -> tuple[str, bool]:
    """
    Transform a single top-level declaration.
    Returns `(new_text, was_modified)`.
    """
    if not is_pp_explicit_region(decl_text):
        return decl_text, False

    assign_pos = find_top_level_assign(decl_text)
    if assign_pos == -1:
        # Declaration without `:=` (e.g. structure/class/inductive/axiom)
        if not is_pp_explicit_region(decl_text):
            return decl_text, False
        return decl_text, False

    sig_part = decl_text[:assign_pos]
    body_part = decl_text[assign_pos:]  # starts with `:=`

    # Separate header line prefix `theorem Foo.bar.{u} :` from type expression
    # Find top-level `:` in `sig_part`
    colon_pos = _find_top_level_char(sig_part, ":")
    modified = False

    if colon_pos != -1 and is_pp_explicit_region(sig_part):
        header_prefix = sig_part[: colon_pos + 1]
        type_expr = sig_part[colon_pos + 1 :]
        # Transform type_expr (iterating up to 3 passes in case outer wrappers unlock inner ones)
        new_type = type_expr
        for _ in range(3):
            nxt = de.transform_expr(new_type, tactic_mode=False)
            if nxt == new_type:
                break
            new_type = nxt
        if new_type != type_expr:
            new_type = compact_whitespace_in_decl_expr(new_type)
            sig_part = header_prefix.rstrip() + "\n    " + new_type + " "
            modified = True

    # Check body_part: `:= by ...` (tactic) vs `:= <term>` (term-mode def)
    after_assign = body_part[2:].lstrip()
    is_tactic = after_assign.startswith("by") and (len(after_assign) == 2 or after_assign[2].isspace())
    if not is_tactic and is_pp_explicit_region(body_part):
        term_expr = body_part[2:]
        # Preserve trailing blank lines
        trailing_nl = ""
        m_tr = re.search(r"(\n+)$", term_expr)
        if m_tr:
            trailing_nl = m_tr.group(1)
            term_core = term_expr[: -len(trailing_nl)]
        else:
            term_core = term_expr
        new_term = term_core
        for _ in range(3):
            nxt = de.transform_expr(new_term, tactic_mode=False)
            if nxt == new_term:
                break
            new_term = nxt
        if new_term != term_core:
            new_term = compact_whitespace_in_decl_expr(new_term)
            body_part = ":=\n  " + new_term + (trailing_nl if trailing_nl else "\n")
            modified = True

    if not modified:
        return decl_text, False

    combined = sig_part + body_part
    combined = clean_unused_inst_binders(combined)
    # Ensure balanced delimiters — if anything ever became unbalanced, fall back safely to original!
    ok, _ = check_balanced_delimiters(combined)
    if not ok:
        de.stats["safety_rollbacks"] += 1
        return decl_text, False
    return combined, True


def transform_file(text: str, de: DeElaborator) -> tuple[str, int, int]:
    """Transform all `pp.explicit` declarations in a file. Returns (new_text, decls_modified, decls_total)."""
    blocks = split_top_level_blocks(text)
    out_blocks: list[str] = []
    mod_cnt = 0
    decl_cnt = 0
    for is_decl, blk in blocks:
        if is_decl:
            decl_cnt += 1
            new_blk, chg = transform_declaration(blk, de)
            if chg:
                mod_cnt += 1
            out_blocks.append(new_blk)
        else:
            out_blocks.append(blk)
    return "".join(out_blocks), mod_cnt, decl_cnt


# ==============================================================================
# 6. Batch Runner + Automated Verification + Report Generator
# ==============================================================================

def main() -> None:
    parser = argparse.ArgumentParser(description="Rewrite explicit Lean syntax into a separate shadow tree.")
    add_path_arguments(parser, uses_index=False)
    parser.add_argument("--targets", type=Path, help="Targets list (default: OUT_DIR/heavy82_targets.json)")
    args = parser.parse_args()
    src_root, _, out_dir = resolve_paths(args)
    src_root = src_root.resolve()
    target_file = args.targets or out_dir / "heavy82_targets.json"
    shadow_dir = (out_dir / "capelli_shadow").resolve()
    manifest_path = out_dir / "capelli_batch_manifest.json"
    report_path = out_dir / "capelli_batch_report.md"
    if shadow_dir.is_relative_to(src_root) or src_root.is_relative_to(shadow_dir):
        parser.error("shadow tree and Lean source tree must be separate")

    t0 = time.time()
    targets = json.loads(target_file.read_text(encoding="utf-8"))
    if not targets:
        parser.error("target list is empty")
    for target in targets:
        relative = Path(target["rel_path"].replace("\\", "/"))
        if (relative.is_absolute() or relative.drive or ".." in relative.parts or relative.suffix != ".lean"
                or not (src_root / relative).resolve().is_relative_to(src_root)
                or not (shadow_dir / relative).resolve().is_relative_to(shadow_dir)):
            parser.error("target must be a relative .lean path within the source and shadow trees")
        target["rel_path"] = relative.as_posix()

    print(f"Loaded {len(targets)} heavy explicit-@ targets from {target_file.name}")
    project_schemas = load_project_schemas_from_sources(targets, src_root)
    print(f"Loaded {len(project_schemas)} full-source verified project-local binder schemas + {len(MATHLIB_SCHEMAS)} Mathlib schemas")

    shadow_dir.mkdir(parents=True, exist_ok=True)
    RE_AT_LINE = re.compile(r"(?:^|[\s(\[{])@[A-Za-z_]")

    records = []
    tot_before_lines = 0
    tot_after_lines = 0
    tot_before_bytes = 0
    tot_after_bytes = 0
    tot_before_at = 0
    tot_after_at = 0

    cap_before_lines = 0
    cap_after_lines = 0
    cap_before_bytes = 0
    cap_after_bytes = 0
    cap_before_at = 0
    cap_after_at = 0

    all_decls_preserved = True
    all_balanced = True
    zero_forbidden_intro = True
    total_notation_leaks = 0
    agg_risks = {"HIGH": Counter(), "MEDIUM": Counter(), "LOW": Counter()}
    agg_stats = Counter()

    for idx, t in enumerate(targets, 1):
        src_path = src_root / t["rel_path"]
        raw = src_path.read_text(encoding="utf-8", errors="replace")
        before_lines = len(raw.splitlines())
        before_bytes = len(raw.encode("utf-8"))
        before_at = sum(1 for ln in raw.splitlines() if RE_AT_LINE.search(ln.split("--", 1)[0]))
        before_decls = extract_decls_from_text(raw)
        before_forb = count_forbidden_tokens(raw)

        de = DeElaborator(project_schemas)
        transformed, decls_mod, decls_tot = transform_file(raw, de)

        after_lines = len(transformed.splitlines())
        after_bytes = len(transformed.encode("utf-8"))
        after_at = sum(1 for ln in transformed.splitlines() if RE_AT_LINE.search(ln.split("--", 1)[0]))
        after_decls = extract_decls_from_text(transformed)
        after_forb = count_forbidden_tokens(transformed)
        bal_ok, bal_msg = check_balanced_delimiters(transformed)
        leaks = check_notation_instance_leaks(transformed)
        total_notation_leaks += len(leaks)

        decls_ok = before_decls == after_decls
        forb_ok = all(after_forb[k] <= before_forb[k] for k in ("sorry", "axiom", "admit"))

        if not decls_ok:
            all_decls_preserved = False
        if not bal_ok:
            all_balanced = False
        if not forb_ok:
            zero_forbidden_intro = False

        # Write shadow copy preserving relative path under shadow_dir
        shadow_path = shadow_dir / t["rel_path"]
        shadow_path.parent.mkdir(parents=True, exist_ok=True)
        shadow_path.write_text(transformed, encoding="utf-8")

        for lvl in ("HIGH", "MEDIUM", "LOW"):
            agg_risks[lvl].update(de.risks[lvl])
        agg_stats.update(de.stats)

        tot_before_lines += before_lines
        tot_after_lines += after_lines
        tot_before_bytes += before_bytes
        tot_after_bytes += after_bytes
        tot_before_at += before_at
        tot_after_at += after_at

        if t["is_capelli"]:
            cap_before_lines += before_lines
            cap_after_lines += after_lines
            cap_before_bytes += before_bytes
            cap_after_bytes += after_bytes
            cap_before_at += before_at
            cap_after_at += after_at

        records.append({
            "rank": idx,
            "module": t["module"],
            "short_name": t["module"].rsplit(".", 1)[-1],
            "rel_path": t["rel_path"],
            "shadow_path": str(shadow_path),
            "is_capelli": t["is_capelli"],
            "before_lines": before_lines,
            "after_lines": after_lines,
            "saved_lines": before_lines - after_lines,
            "line_reduction_pct": round(100.0 * (before_lines - after_lines) / max(1, before_lines), 2),
            "before_bytes": before_bytes,
            "after_bytes": after_bytes,
            "saved_bytes": before_bytes - after_bytes,
            "byte_reduction_pct": round(100.0 * (before_bytes - after_bytes) / max(1, before_bytes), 2),
            "before_at_lines": before_at,
            "after_at_lines": after_at,
            "decls_total": len(before_decls),
            "decls_modified": decls_mod,
            "decls_preserved": decls_ok,
            "delimiters_balanced": bal_ok,
            "delimiter_msg": bal_msg,
            "notation_instance_leaks": len(leaks),
            "forbidden_introduced": not forb_ok,
            "tier1_rewrites": de.stats["tier1_schema_rewrites"],
            "phantom_named_preserved": de.stats["phantom_named_preserved"],
            "tier2_rewrites": de.stats["tier2_head_rewrites"],
            "safety_rollbacks": de.stats["safety_rollbacks"],
            "risk_high": dict(de.risks["HIGH"]),
            "risk_medium": dict(de.risks["MEDIUM"]),
            "risk_low": dict(de.risks["LOW"]),
        })

    elapsed = round(time.time() - t0, 2)
    modified_files = [r for r in records if r["decls_modified"] > 0]
    untouched_files = [r for r in records if r["decls_modified"] == 0]
    high_risk_files = [r for r in records if r["risk_high"]]
    med_risk_files = [r for r in records if r["risk_medium"]]

    manifest = {
        "summary": {
            "total_files": len(records),
            "capelli_files": sum(1 for r in records if r["is_capelli"]),
            "non_capelli_files": sum(1 for r in records if not r["is_capelli"]),
            "files_modified_pp_explicit": len(modified_files),
            "files_untouched_manual_at": len(untouched_files),
            "elapsed_sec": elapsed,
            "before_lines": tot_before_lines,
            "after_lines": tot_after_lines,
            "saved_lines": tot_before_lines - tot_after_lines,
            "line_reduction_pct": round(100.0 * (tot_before_lines - tot_after_lines) / max(1, tot_before_lines), 2),
            "before_bytes": tot_before_bytes,
            "after_bytes": tot_after_bytes,
            "saved_bytes": tot_before_bytes - tot_after_bytes,
            "byte_reduction_pct": round(100.0 * (tot_before_bytes - tot_after_bytes) / max(1, tot_before_bytes), 2),
            "before_at_lines": tot_before_at,
            "after_at_lines": tot_after_at,
            "capelli_46_subtotal": {
                "files": sum(1 for r in records if r["is_capelli"]),
                "before_lines": cap_before_lines,
                "after_lines": cap_after_lines,
                "saved_lines": cap_before_lines - cap_after_lines,
                "line_reduction_pct": round(100.0 * (cap_before_lines - cap_after_lines) / max(1, cap_before_lines), 2),
                "before_bytes": cap_before_bytes,
                "after_bytes": cap_after_bytes,
                "saved_bytes": cap_before_bytes - cap_after_bytes,
                "byte_reduction_pct": round(100.0 * (cap_before_bytes - cap_after_bytes) / max(1, cap_before_bytes), 2),
                "before_at_lines": cap_before_at,
                "after_at_lines": cap_after_at,
            },
            "pp_explicit_51_subtotal": {
                "files": len(modified_files),
                "before_lines": sum(r["before_lines"] for r in modified_files),
                "after_lines": sum(r["after_lines"] for r in modified_files),
                "saved_lines": sum(r["saved_lines"] for r in modified_files),
                "line_reduction_pct": round(
                    100.0 * sum(r["saved_lines"] for r in modified_files) / max(1, sum(r["before_lines"] for r in modified_files)), 2
                ),
                "before_bytes": sum(r["before_bytes"] for r in modified_files),
                "after_bytes": sum(r["after_bytes"] for r in modified_files),
                "saved_bytes": sum(r["saved_bytes"] for r in modified_files),
                "byte_reduction_pct": round(
                    100.0 * sum(r["saved_bytes"] for r in modified_files) / max(1, sum(r["before_bytes"] for r in modified_files)), 2
                ),
            },
            "verification": {
                "all_decls_preserved_100pct": all_decls_preserved,
                "total_decls_checked": sum(r["decls_total"] for r in records),
                "total_decls_modified": sum(r["decls_modified"] for r in records),
                "all_delimiters_balanced": all_balanced,
                "zero_sorry_axiom_admit_introduced": zero_forbidden_intro,
                "notation_instance_leaks": total_notation_leaks,
                "phantom_named_preserved": agg_stats["phantom_named_preserved"],
                "safety_rollbacks": agg_stats["safety_rollbacks"],
                "tier1_schema_rewrites": agg_stats["tier1_schema_rewrites"],
                "tier2_head_rewrites": agg_stats["tier2_head_rewrites"],
                "tier2_inst_folded": agg_stats["tier2_inst_folded"],
            },
            "risk_summary": {
                "high_risk_file_count": len(high_risk_files),
                "medium_risk_file_count": len(med_risk_files),
                "high_counts": dict(agg_risks["HIGH"]),
                "medium_counts": dict(agg_risks["MEDIUM"]),
                "low_counts": dict(agg_risks["LOW"]),
            },
        },
        "files": records,
    }

    manifest_path.write_text(json.dumps(manifest, indent=2), encoding="utf-8")
    print(f"\n=== Batch De-Elaboration Complete ({elapsed}s) ===")
    s = manifest["summary"]
    print(f"  82-File Corpus Total  : {s['before_lines']:,}L -> {s['after_lines']:,}L  (saved {s['saved_lines']:,}L, -{s['line_reduction_pct']}%)")
    print(f"  82-File Bytes Total   : {s['before_bytes']:,}B -> {s['after_bytes']:,}B  (saved {s['saved_bytes']:,}B, -{s['byte_reduction_pct']}%)")
    print(f"  46 Capelli Subtotal   : {s['capelli_46_subtotal']['before_lines']:,}L -> {s['capelli_46_subtotal']['after_lines']:,}L  (saved {s['capelli_46_subtotal']['saved_lines']:,}L, -{s['capelli_46_subtotal']['line_reduction_pct']}%)")
    print(f"  Modified pp.explicit  : {s['files_modified_pp_explicit']} files ({s['pp_explicit_51_subtotal']['before_lines']:,}L -> {s['pp_explicit_51_subtotal']['after_lines']:,}L, -{s['pp_explicit_51_subtotal']['line_reduction_pct']}%)")
    print(f"  Untouched manual-@    : {s['files_untouched_manual_at']} files")
    print(f"  Decls preserved 100%  : {s['verification']['all_decls_preserved_100pct']} ({s['verification']['total_decls_checked']} decls checked, {s['verification']['total_decls_modified']} modified)")
    print(f"  Delimiters balanced   : {s['verification']['all_delimiters_balanced']}")
    print(f"  Zero sorry/axiom/admit: {s['verification']['zero_sorry_axiom_admit_introduced']}")
    print(f"  Safety rollbacks      : {s['verification']['safety_rollbacks']}")
    print(f"  Tier-1 / Tier-2       : {s['verification']['tier1_schema_rewrites']:,} / {s['verification']['tier2_head_rewrites']:,} ({s['verification']['tier2_inst_folded']:,} inst slots)")
    print(f"  HIGH / MED risk files : {s['risk_summary']['high_risk_file_count']} / {s['risk_summary']['medium_risk_file_count']}")
    print("\nTop 15 largest savings:")
    for r in sorted(records, key=lambda x: -x["saved_lines"])[:15]:
        print(f"  {r['short_name']:36s} {r['before_lines']:5d}L -> {r['after_lines']:4d}L (-{r['line_reduction_pct']:5.1f}%)  at:{r['before_at_lines']:4d}->{r['after_at_lines']:3d}  declsOK={r['decls_preserved']} bal={r['delimiters_balanced']} H={len(r['risk_high'])} M={len(r['risk_medium'])}")


if __name__ == "__main__":
    main()
