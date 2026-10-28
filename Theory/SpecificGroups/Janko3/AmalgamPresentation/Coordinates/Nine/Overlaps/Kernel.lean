module
public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Coordinates.Nine.Overlaps.Basic
import Mathlib.Tactic.FinCases

/-! Explicit powers retain the complete cubic kernel in both raw overlaps. -/
public section
namespace Sporadic.Janko3.AmalgamPresentation.NineCoordinates
open Subgroup

private def coordinateLift (i : Fin 4) : ComputableModel := ⟨overlapCubic i,overlapMatrix i⟩
private theorem coordinateLift_eq (i : Fin 4) : toCanonical (coordinateLift i) = overlapElement i :=
  (overlapElement_coordinates i).symm

private theorem pure_cubic_of_power (i : Fin 4) (n : Nat)
    (hl : (coordinateLift i ^ n).left = Multiplicative.ofAdd 1)
    (u : Fˣ) (hr : (coordinateLift i ^ n).right = Matrix.GeneralLinearGroup.scalar (Fin 2) u) :
    overlapElement i ^ n = SemidirectProduct.inl (Multiplicative.ofAdd 1 : Z) := by
  rw [←coordinateLift_eq,←map_pow]
  apply SemidirectProduct.ext
  · exact hl
  · change Matrix.ProjGenLinGroup.mk (coordinateLift i ^ n).right = 1
    rw [hr,Matrix.ProjGenLinGroup.mk_scalar]

private theorem pair_cubic : overlapElement 0 ^ 2 =
    SemidirectProduct.inl (Multiplicative.ofAdd 1 : Z) := by
  apply pure_cubic_of_power 0 2 (by decide +kernel) 1
  apply Matrix.GeneralLinearGroup.ext
  intro j k
  fin_cases j <;> fin_cases k <;> decide +kernel

private theorem third_cubic : overlapElement 3 ^ 10 =
    SemidirectProduct.inl (Multiplicative.ofAdd 1 : Z) := by
  apply pure_cubic_of_power 3 10 (by decide +kernel) 1
  apply Matrix.GeneralLinearGroup.ext
  intro j k
  fin_cases j <;> fin_cases k <;> decide +kernel

private theorem kernel_le_of_cubic (H : Subgroup Canonical)
    (hh : SemidirectProduct.inl (Multiplicative.ofAdd 1 : Z) ∈ H) :
    SourceRecognition.CubicNormalizerModel.projection.ker ≤ H := by
  rw [SourceRecognition.CubicNormalizerModel.projection_ker]
  rintro _ ⟨z,rfl⟩
  have h : ∀ z : Z, ∃ n : Fin 3, (Multiplicative.ofAdd 1 : Z) ^ n.val = z := by decide +kernel
  obtain ⟨n,hn⟩ := h z
  rw [←hn,map_pow]
  exact pow_mem hh n.val

/-- The actual order-sixty word subgroup retains the whole cubic kernel. -/
theorem kernel_le_rawPair : SourceRecognition.CubicNormalizerModel.projection.ker ≤ rawPair := by
  apply kernel_le_of_cubic
  rw [←pair_cubic]
  exact pow_mem (subset_closure (Set.mem_insert _ _)) 2

/-- The actual order-180 word subgroup retains the whole cubic kernel. -/
theorem kernel_le_rawThird : SourceRecognition.CubicNormalizerModel.projection.ker ≤ rawThird := by
  apply kernel_le_of_cubic
  rw [←third_cubic]
  exact pow_mem (subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))) 10

end Sporadic.Janko3.AmalgamPresentation.NineCoordinates
