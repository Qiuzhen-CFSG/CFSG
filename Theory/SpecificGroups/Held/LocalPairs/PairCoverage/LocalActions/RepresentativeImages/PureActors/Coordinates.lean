module

public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.LocalActions.RepresentativeImages.PureActors.Support
/-!
# Coordinate formulas for the pure Held actors

The marked axes generate the actual candidate odd subgroup. Their prescribed
images are the quarter-turn and its inverse, both outside the diagonal group.
These small plane identities will be connected to actual ambient conjugation
in PureActors. Source: GLS3 Table 5.3p; quasithin pp.509–511.
-/

@[expose] public section
namespace Held.LocalPairs.PairCoverage.LocalActions.RepresentativeImages.PureActors

def coordinateAction (i : Bool) : MulAut Plane := if i then rotation⁻¹ else rotation

def imageIndex (k : Fin 2) : Fin 2 := if k = 0 then 1 else 0

def imageExponent : Bool → Fin 2 → ℤ
  | false, 0 => 1
  | false, 1 => -1
  | true, 0 => -1
  | true, 1 => 1

def imageElement (i : Bool) (k : Fin 2) : He :=
  basisGenerator i 0 (imageIndex k) ^ imageExponent i k

theorem imageElement_mem (i : Bool) (k : Fin 2) : imageElement i k ∈ candidateOdd i 0 :=
  (candidateOdd i 0).zpow_mem (basisGenerator_mem i 0 (imageIndex k)) _

theorem coordinateAction_vector (i : Bool) (k : Fin 2) :
    coordinateAction i (coordinateVector k) =
      coordinateVector (imageIndex k) ^ imageExponent i k := by
  revert i k
  decide +kernel

theorem candidateOddEquiv_symm_image (i : Bool) (k : Fin 2) :
    ((candidateOddEquiv i 0).symm (coordinateAction i (coordinateVector k)) : He) =
      imageElement i k := by
  rw [coordinateAction_vector, map_zpow]
  change ((candidateOddEquiv i 0).symm (coordinateVector (imageIndex k)) : He) ^
      imageExponent i k = _
  rw [candidateOddEquiv_symm_vector]
  rfl

theorem plane_aut_ext (f g : MulAut Plane)
    (h : ∀ k, f (coordinateVector k) = g (coordinateVector k)) : f = g := by
  have hv : ∀ v : Plane, v = coordinateVector 0 ^ (v.toAdd 0).val *
      coordinateVector 1 ^ (v.toAdd 1).val := by decide +kernel
  apply MulEquiv.ext
  intro v
  rw [hv v, map_mul, map_mul, map_pow, map_pow, map_pow, map_pow, h 0, h 1]

theorem coordinateAction_not_mem_diagonal (i : Bool) : coordinateAction i ∉ diagonal := by
  intro h
  have hx := diagonal_preserves_axis _ h (coordinateVector 0) (by rfl)
  have hn : coordinateAction i (coordinateVector 0) ∉ axis := by
    change (coordinateAction i (coordinateVector 0)).toAdd 1 ≠ 0
    cases i <;> decide +kernel
  exact hn hx
end Held.LocalPairs.PairCoverage.LocalActions.RepresentativeImages.PureActors
namespace Held.LocalPairs.PairCoverage.LocalActions.RepresentativeImages.PureActors
open Subgroup

theorem basis_closure (i : Bool) :
    closure (Set.range (basisGenerator i 0)) = candidateOdd i 0 := by
  apply le_antisymm
  · apply (closure_le _).mpr
    rintro _ ⟨k, rfl⟩
    exact basisGenerator_mem i 0 k
  · apply (closure_le _).mpr
    rintro _ ⟨k, rfl⟩
    cases i <;> fin_cases k
    · exact subset_closure ⟨0, rfl⟩
    · exact subset_closure ⟨1, rfl⟩
    · have he : evalLocalWord true (oddWord true 0 0) =
          basisGenerator true 0 1 * (basisGenerator true 0 0)⁻¹ := by
        change oddGenerator true 0 0 =
          (oddGenerator true 0 0 * oddGenerator true 0 1) * (oddGenerator true 0 1)⁻¹
        group
      change evalLocalWord true (oddWord true 0 0) ∈ _
      rw [he]
      exact mul_mem (subset_closure ⟨1, rfl⟩) (inv_mem (subset_closure ⟨0, rfl⟩))
    · exact subset_closure ⟨0, rfl⟩
end Held.LocalPairs.PairCoverage.LocalActions.RepresentativeImages.PureActors
