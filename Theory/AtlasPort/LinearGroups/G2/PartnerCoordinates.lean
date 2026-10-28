module

/-
Copyright (c) 2026 Gerald Höhn and the ATLAS contributors. All rights reserved.
Covered by the ATLAS Research and Attribution License 1.0 (LICENSES/ATLAS.txt).
Source: Atlas/LinearGroups/G2/PartnerCoordinates.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917; see LICENSES/ATLAS-CITATION.cff.
Changes: CFSG import paths and Lean 4.33 public module boundaries.
-/

public import Theory.AtlasPort.LinearGroups.G2.Basic
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Tactic.LinearCombination

/-! Singular partners of the first basis vector form an affine five-space: solve trace and norm for the two remaining coordinates. -/

@[expose] public section

namespace Atlas.G2
open Atlas.SplitOctonion
variable (K : Type*) [Field K]

/-- Singular trace-zero partners pairing to one with the first basis vector. -/
abbrev SingularPartners := {y : Carrier K // trace y = 0 ∧ norm y = 0 ∧ y 7 = 1}

/-- The partner quadric chart is an affine five-space, in every characteristic. -/
def singularPartnersEquiv : SingularPartners K ≃ (Fin 5 → K) where
  toFun y := ![y.val 1,y.val 2,y.val 3,y.val 5,y.val 6]
  invFun t := ⟨![(t 2)^2-t 0*t 4-t 1*t 3,t 0,t 1,t 2,-t 2,t 3,t 4,1],by
    refine ⟨by simp [trace],?_,by simp⟩
    simp [norm]; ring⟩
  left_inv y := by
    apply Subtype.ext
    have h4 : y.val 4 = -y.val 3 := eq_neg_of_add_eq_zero_right y.property.1
    have h0 : y.val 0 = (y.val 3)^2-y.val 1*y.val 6-y.val 2*y.val 5 := by
      have hn := y.property.2.1
      simp only [norm,h4,y.property.2.2,mul_one] at hn
      linear_combination hn
    ext i; fin_cases i <;> simp [h0,h4,y.property.2.2]
  right_inv t := by ext i; fin_cases i <;> rfl

theorem card_singularPartners [Finite K] : Nat.card (SingularPartners K) = Nat.card K ^ 5 := by
  rw [Nat.card_congr (singularPartnersEquiv K),Nat.card_fun,Nat.card_fin]

end Atlas.G2
