module

/-
Copyright (c) 2026 Gerald Höhn and the ATLAS contributors. All rights reserved.
Covered by the ATLAS Research and Attribution License 1.0 (LICENSES/ATLAS.txt).
Source: Atlas/LinearGroups/G2/WeylMaps.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917; see LICENSES/ATLAS-CITATION.cff.
Changes: CFSG import paths and Lean 4.33 public module boundaries.
-/

public import Theory.AtlasPort.LinearGroups.G2.RootGroups

/-! Explicit coordinate permutations give Weyl automorphisms preserving octonion multiplication. -/

@[expose] public section

namespace Atlas.G2
open Atlas.SplitOctonion
variable {K : Type*} [Field K]

def weylRApply (x : Carrier K) : Carrier K := ![-x 0,-x 2,-x 1,x 3,x 4,-x 6,-x 5,-x 7]
def weylRLinear : Carrier K →ₗ[K] Carrier K where
  toFun := weylRApply
  map_add' x y := by ext i; fin_cases i <;> simp [weylRApply] <;> ring
  map_smul' r x := by ext i; fin_cases i <;> simp [weylRApply]
def weylREquiv : Carrier K ≃ₗ[K] Carrier K where
  toLinearMap := weylRLinear
  invFun := weylRApply
  left_inv x := by ext i; fin_cases i <;> simp [weylRApply,weylRLinear]
  right_inv x := by ext i; fin_cases i <;> simp [weylRApply,weylRLinear]
theorem weylR_mul (x y : Carrier K) :
    weylREquiv (mul x y) = mul (weylREquiv x) (weylREquiv y) := by
  ext i; fin_cases i <;> simp [weylREquiv,weylRLinear,weylRApply,mul] <;> ring
def weylR : Model K := ⟨weylREquiv,weylR_mul⟩

theorem weylR_sq : (weylR : Model K)^2 = 1 := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  ext i; fin_cases i <;> simp [pow_two,weylR,weylREquiv,weylRLinear,weylRApply]

def weylSApply (x : Carrier K) : Carrier K := ![-x 1,-x 0,-x 5,x 4,x 3,-x 2,-x 7,-x 6]
def weylSLinear : Carrier K →ₗ[K] Carrier K where
  toFun := weylSApply
  map_add' x y := by ext i; fin_cases i <;> simp [weylSApply] <;> ring
  map_smul' r x := by ext i; fin_cases i <;> simp [weylSApply]
def weylSEquiv : Carrier K ≃ₗ[K] Carrier K where
  toLinearMap := weylSLinear
  invFun := weylSApply
  left_inv x := by ext i; fin_cases i <;> simp [weylSApply,weylSLinear]
  right_inv x := by ext i; fin_cases i <;> simp [weylSApply,weylSLinear]
theorem weylS_mul (x y : Carrier K) :
    weylSEquiv (mul x y) = mul (weylSEquiv x) (weylSEquiv y) := by
  ext i; fin_cases i <;> simp [weylSEquiv,weylSLinear,weylSApply,mul] <;> ring
def weylS : Model K := ⟨weylSEquiv,weylS_mul⟩

theorem weylS_sq : (weylS : Model K)^2 = 1 := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  ext i; fin_cases i <;> simp [pow_two,weylS,weylSEquiv,weylSLinear,weylSApply]
end Atlas.G2
