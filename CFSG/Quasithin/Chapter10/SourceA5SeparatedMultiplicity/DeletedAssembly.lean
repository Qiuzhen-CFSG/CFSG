module

public import CFSG.Quasithin.Chapter10.SourceA5SeparatedMultiplicity.SupportGeometry
public import CFSG.Quasithin.Chapter10.SourceA5SeparatedMultiplicity.DeletedCoordinates
public import Theory.Representation.BinaryPermutation.FiveTensorSquare.Model

/-!
# The deleted separated-support multiplicity theorem

Literal homogeneous coordinates on the canonical supports construct every
geometric field of the marked starred-actor input. The conjugation map is the
one specified by the original pair embedding, and its actual permutation
coordinates govern both support covariance and the displacement estimates.
The resulting multiplicity is at most two (at most one in the swapping case).

Source: Aschbacher--Smith D.3.9 and D.3.21, the separated deleted-module branch.
Only the independent earlier-source coordinate and faithful-conjugation inputs
remain; no displacement or support-invariance premise is left to the consumer.
-/

@[expose] public noncomputable section
open Subgroup Representation
open Representation.NormalPairSupport Representation.NormalPairHomogeneous
open Representation.AlternatingFive
open Theory.SpecificGroups.SymmetricFive.ProjectedElementaryRank
namespace CFSG.Quasithin.Chapter10.SourceA5SeparatedMultiplicity

variable {A Q V : Type*} [Group A] [Finite A] [IsElementaryAbelian 2 A]
  [Group Q] [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  (ρ : Representation (ZMod 2) Q V) (i : Alt × Alt →* Q)

/-- Build the complete actor input from deleted homogeneous coordinates on the
actual canonical supports and the faithful marked conjugation action. -/
def deletedActorData (j : A →* Q) (c : A →* MulAut (Alt × Alt))
    (hc : ∀ a z, j a * i z * (j a)⁻¹ = i (c a z)) (hfaith : Function.Injective c)
    (hcomp : IsCompl (left ρ i) (right ρ i))
    (d : NormalPairHomogeneous.Coordinates ρ i BinaryPermutation.FiveTensorSquare.δ) :
    SeparatedActorData (ρ.comp j) d.multiplicity where
  conjugation := c
  faithful := hfaith
  preserved hb := by
    let e₁ : AmplifiedDeleted.Coordinates (ι := Fin d.multiplicity) (leftAction ρ i) := {
      equiv := d.leftEquiv
      intertwines := d.left_intertwines }
    let e₂ : AmplifiedDeleted.Coordinates (ι := Fin d.multiplicity) (rightAction ρ i) := {
      equiv := d.rightEquiv
      intertwines := d.right_intertwines }
    exact ⟨PreservedBlocks.of_deleted (ρ.comp j) (markedWreath c) d.multiplicity hb
      (firstBlock ρ i j c hc hb) (secondBlock ρ i j c hc hb)
      (Submodule.prodEquivOfIsCompl _ _ hcomp).symm
      (support_coordinates_intertwine ρ i j c hc hb hcomp)
      (leftAction ρ i) (rightAction ρ i) e₁ e₂
      (firstBlock_covariance ρ i j c hc hb)
      (secondBlock_covariance ρ i j c hc hb)⟩
  exchanged a ha := by
    refine ⟨left ρ i, ?_, swapping_support_disjoint ρ i j c hc hcomp.disjoint a ha⟩
    rw [d.leftEquiv.finrank_eq, Module.finrank_pi_fintype]
    simp [BinaryPermutation.finrank_core, Nat.mul_comm]

variable [Finite Q]

/-- The actual starred cubic actor has multiplicity at most two on the deleted
homogeneous supports. All four amplified estimates and support geometry have
been discharged from the literal coordinates. -/
theorem deleted_multiplicity_le_two_of_starred_actor {E : Subgroup Q}
    (hE : E ∈ ChapterD.QhatStar ρ)
    (c : E →* MulAut (Alt × Alt))
    (hc : ∀ a z, a.val * i z * a.val⁻¹ = i (c a z)) (hfaith : Function.Injective c)
    (hcomp : IsCompl (left ρ i) (right ρ i))
    (d : NormalPairHomogeneous.Coordinates ρ i BinaryPermutation.FiveTensorSquare.δ) :
    d.multiplicity ≤ 2 := by
  let : IsElementaryAbelian 2 E := hE.1.2.1.2
  exact source_separated_multiplicity_le_two_of_starred_actor ρ hE d.multiplicity
    (deletedActorData ρ i E.subtype c hc hfaith hcomp d)

end CFSG.Quasithin.Chapter10.SourceA5SeparatedMultiplicity
