/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Codes/TernaryGolayQuotient.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.Janko2.Codes.TernaryGolay
public import Mathlib.LinearAlgebra.Dimension.RankNullity

/-!
# TernaryGolayQuotient

The phase module is the concrete ternary Golay code modulo its constant line.
Rank-nullity gives dimension five.

Source: Gerald Höhn, ATLAS, `Atlas/Codes/TernaryGolayQuotient.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted to CFSG Lean 4.33.0 with public imports and exposed computational definitions.
-/

@[expose] public section


namespace Atlas.Codes

def ternaryOne : ternaryGolay := ⟨fun _ => 1, ternaryGolay_one⟩

def ternaryConstants : Submodule (ZMod 3) ternaryGolay :=
  Submodule.span (ZMod 3) {ternaryOne}

abbrev TernaryPhaseModule := ternaryGolay ⧸ ternaryConstants

theorem ternaryOne_ne_zero : ternaryOne ≠ 0 := by
  intro h
  have he := congrFun (congrArg Subtype.val h) 0
  change (1 : ZMod 3) = 0 at he
  exact one_ne_zero he

theorem ternaryConstants_finrank : Module.finrank (ZMod 3) ternaryConstants = 1 :=
  finrank_span_singleton ternaryOne_ne_zero

theorem ternaryPhaseModule_finrank : Module.finrank (ZMod 3) TernaryPhaseModule = 5 := by
  have h := ternaryConstants.finrank_quotient_add_finrank
  rw [ternaryConstants_finrank, ternaryGolay_finrank] at h
  exact Nat.add_right_cancel (h.trans (by decide : 6 = 5+1))

end Atlas.Codes
