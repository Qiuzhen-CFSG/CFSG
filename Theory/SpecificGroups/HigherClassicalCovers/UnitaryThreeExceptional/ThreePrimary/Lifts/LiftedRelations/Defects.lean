module

public import Theory.SpecificGroups.HigherClassicalCovers.UnitaryThreeExceptional.ThreePrimary.Lifts.LiftedRelations.Commuting
public import Theory.SpecificGroups.HigherClassicalCovers.UnitaryThreeExceptional.ThreePrimary.Lifts.LiftedRelations.CollectionAlgebra

/-!
# The cubic defect of the first collection relation

Every descending swap error lies in the central kernel. In the `(0,2)`
relation, the tail is a product of commuting cubic roots and centralizes the
second root. Collecting its three successive conjugates therefore shows that
the error itself has cube one. This gives the second defect, alongside the
mixed commuting-pair defect already constructed in `Normalized`.

Source: the exceptional three-part calculation for Aschbacher--Smith
I.1.4(5), printed p.408, and GLS3 §6.1. The kernel is not assumed to have
exponent three.
-/

@[expose] public noncomputable section
namespace Theory.SpecificGroups.HigherClassicalCovers.UnitaryThreeExceptional.ThreePrimary.RootLifts
namespace CubicRootLifts
open LiftedRelations

variable {E : Type*} [Group E] {f : E →* S} (L : CubicRootLifts f)

/-- The literal descending error, using the fixed collection tail. -/
def swapError (i j : Fin 6) : E :=
  L.gen j * L.gen i * (L.gen i * L.gen j * swapTail L.gen i j)⁻¹

theorem swapError_mem (i j : Fin 6) (hij : i < j) : L.swapError i j ∈ f.ker := by
  change f (L.gen j * L.gen i * (L.gen i * L.gen j * swapTail L.gen i j)⁻¹) = 1
  simp only [map_mul, map_inv, map_swapTail, L.projects]
  rw [root_swap i j hij, mul_inv_cancel]

/-- The defect in collecting the first short root past the simple long root. -/
def collectionDefect : E := L.swapError 0 2

theorem collectionDefect_mem : L.collectionDefect ∈ f.ker := L.swapError_mem 0 2 (by decide)

theorem collectionDefect_spec (hk : f.ker ≤ Subgroup.center E) :
    L.gen 2 * L.gen 0 =
      L.gen 0 * L.gen 2 * (L.gen 4 ^ 2 * L.gen 5) * L.collectionDefect := by
  have h := Subgroup.mem_center_iff.mp (hk L.collectionDefect_mem)
    (L.gen 0 * L.gen 2 * (L.gen 4 ^ 2 * L.gen 5))
  calc
    L.gen 2 * L.gen 0 =
        L.collectionDefect * (L.gen 0 * L.gen 2 * (L.gen 4 ^ 2 * L.gen 5)) := by
      simp only [collectionDefect, swapError, swapTail, Fin.isValue,
        and_self, ↓reduceIte]
      group
    _ = _ := h.symm

/-- Three successive conjugations annihilate the first collection error. -/
theorem collectionDefect_cube (hf : Function.Surjective f)
    (hk : f.ker ≤ Subgroup.center E) : L.collectionDefect ^ 3 = 1 := by
  apply collection_error_cube (L.gen 0) (L.gen 2) (L.gen 4 ^ 2 * L.gen 5)
    L.collectionDefect (L.cubes 2) _ (hk L.collectionDefect_mem) _ (L.collectionDefect_spec hk)
  · rw [((commute_partial f hf hk L 4 5 (by tauto)).pow_left 2).mul_pow,
      ← pow_mul, Nat.mul_comm 2 3, pow_mul, L.cubes, L.cubes, one_pow, one_mul]
  · exact ((commute_partial f hf hk L 2 4 (by tauto)).pow_right 2).mul_right
      (commute_long f hf hk L)

end CubicRootLifts
end Theory.SpecificGroups.HigherClassicalCovers.UnitaryThreeExceptional.ThreePrimary.RootLifts
