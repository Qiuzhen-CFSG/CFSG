module

/-
Adapted from Atlas/Comparisons/Exceptional/NineCoordinates.lean,
revision 8eabb35afe2b5e45bf913a2d05c53e558d2e2917, by Gerald Höhn
and the ATLAS contributors. ATLAS Research and Attribution License 1.0
applies; see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
Changes: Lean 4.33 module boundaries, narrow imports, and CFSG order APIs.
-/

public import Mathlib.Algebra.QuadraticAlgebra.Basic
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.FieldTheory.Finite.GaloisField
public import Theory.AtlasPort.ExceptionalIsomorphisms.Support
set_option warningAsError false

@[expose] public section

/-!
# Coordinates for the nine-element field

The quadratic algebra over `ZMod 3` with omega squared equal to minus one is
an explicit field with nine elements. Its product coordinates support finite
kernel checks; uniqueness of finite fields transports arbitrary field models.
-/


namespace Atlas.Comparisons.Exceptional.Nine
/-- The existing mathlib quadratic-algebra model supplies coordinates, not new arithmetic. -/
abbrev F := QuadraticAlgebra (ZMod 3) 2 0
instance nineCoordinateIrreducible : Fact (∀ r : ZMod 3, r^2 ≠ 2+0*r) := ⟨by decide⟩
instance nineCoordinateFintype : Fintype F :=
  Fintype.ofEquiv (ZMod 3 × ZMod 3) (QuadraticAlgebra.equivProd 2 0).symm

theorem card : Nat.card F = 9 := by
  rw [Nat.card_eq_fintype_card,Fintype.card_congr (QuadraticAlgebra.equivProd 2 0),Fintype.card_prod]
  norm_num

def omega : F := QuadraticAlgebra.omega
noncomputable def fieldEquiv {K : Type*} [Field K] [Finite K] (h : Nat.card K = 9) : K ≃+* F := by
  let := Fintype.ofFinite K
  exact FiniteField.ringEquivOfCardEq (by simpa only [←Nat.card_eq_fintype_card] using h.trans card.symm)
end Atlas.Comparisons.Exceptional.Nine
