module

public import Mathlib.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup
public import Mathlib.GroupTheory.GroupAction.Defs

/-!
# The split monomial subgroups of SL₃ and PSL₃

The linear subgroup stabilizes the union of the three punctured coordinate
axes under the natural matrix action. Its projective counterpart is its
image under the actual central quotient map. These definitions are shared
by subgroup-placement arguments and local-core calculations; neither
placement nor a core order is asserted here.

Source: the split monomial subgroup construction for three-dimensional
linear groups, used in Aschbacher–Smith, *The Classification of Quasithin
Groups*, proof of Proposition 1.3.4, printed p.511 (PDF p.528).
-/

@[expose] public section

open scoped Pointwise

namespace Matrix.SL3.SplitMonomial

variable (F : Type*) [Field F]

/-- The union of the three coordinate axes, with the zero vector removed. -/
def coordinateVectors : Set (Fin 3 → F) :=
  {v | ∃ i : Fin 3, v i ≠ 0 ∧ ∀ j : Fin 3, j ≠ i → v j = 0}

/-- The split monomial subgroup, defined by its actual natural action. -/
def linear : Subgroup (SpecialLinearGroup (Fin 3) F) :=
  MulAction.stabilizer (SpecialLinearGroup (Fin 3) F) (coordinateVectors F)

/-- The projective image of the split monomial subgroup. -/
def projective : Subgroup (ProjectiveSpecialLinearGroup (Fin 3) F) :=
  (linear F).map (QuotientGroup.mk' (Subgroup.center (SpecialLinearGroup (Fin 3) F)))

/-- Every nonzero multiple of a coordinate vector belongs to the set being
stabilized. -/
theorem single_mem_coordinateVectors (i : Fin 3) {a : F} (ha : a ≠ 0) :
    Pi.single i a ∈ coordinateVectors F := by
  refine ⟨i, by simpa using ha, ?_⟩
  intro j hj
  simp [hj]

end Matrix.SL3.SplitMonomial
