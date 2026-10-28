module

public import Theory.SpecificGroups.GL2.FiveLargeTwoScalar
public import Theory.SpecificGroups.GL2.PrimeThreeFiveResidual.Coordinates

/-!
# Squaring in large two-groups acting on the elementary five-plane

Marked plane coordinates transport the central matrix scalar 2I back to
the literal automorphism x ↦ x². It lies in every two-subgroup of the
plane automorphism group of order sixteen or thirty-two.
-/

public noncomputable section
open Subgroup Matrix
namespace IsElementaryAbelian.FivePlaneLargeTwoScalar
open Matrix.GeneralLinearGroup
private instance : Fact (Nat.Prime 5) := ⟨by decide⟩

private theorem scalar_apply (v : Multiplicative (Fin 2 → ZMod 5)) :
    PrimeThreeFiveResidual.planeAction 5 SignedFive.scalar v = v ^ 2 := by
  rw [pow_two]
  apply Multiplicative.ext
  change SignedFive.scalar.val *ᵥ v.toAdd = v.toAdd + v.toAdd
  ext i
  fin_cases i <;>
    simp [SignedFive.scalar,diagonalPair_val,Matrix.mulVec,two_mul] <;> rfl

/-- A large two-subgroup of the actual plane automorphism group contains
its simultaneous squaring automorphism. -/
theorem exists_squaring {E : Type*} [Group E] [Finite E] [IsElementaryAbelian 5 E]
    (hE : Nat.card E = 25) (P : Subgroup (MulAut E)) (hp : IsPGroup 2 P)
    (hc : Nat.card P = 16 ∨ Nat.card P = 32) :
    ∃ α ∈ P, ∀ x : E, α x = x ^ 2 := by
  obtain ⟨c,e,he⟩ := PrimeThreeFiveResidual.exists_plane_coordinates (p := 5) hE
  have hc' : Nat.card (P.map e.toMonoidHom) = 16 ∨
      Nat.card (P.map e.toMonoidHom) = 32 := by
    rwa [card_map_of_injective e.injective]
  obtain ⟨α,hα,hscalar⟩ := FiveLargeTwoScalar.scalar_mem (P.map e.toMonoidHom)
    (hp.map e.toMonoidHom) hc'
  change e α = SignedFive.scalar at hscalar
  refine ⟨α,hα,fun x => c.injective ?_⟩
  rw [←he,hscalar,map_pow,scalar_apply]

end IsElementaryAbelian.FivePlaneLargeTwoScalar
