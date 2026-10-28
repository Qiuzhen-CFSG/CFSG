module

public import CFSG.Quasithin.Chapter10.SourceA5SeparatedMultiplicity.SupportGeometry
public import CFSG.Quasithin.Chapter10.SourceA5SeparatedMultiplicity.NaturalCoordinates
public import Theory.Representation.SL2.BinarySmallModels

/-!
# The natural separated-support multiplicity theorem

Canonical supports marked by equally many natural A₅ copies supply every
geometric field of the starred-actor record. The original factor marking is
used when transferring normalizing automorphisms to SL₂(F₄), so arbitrary
multiplicity mixing is retained throughout. The cubic bound gives at most
two copies in each support.

Source: Aschbacher--Smith D.3.9 and D.3.21, the separated natural-module branch.
-/

@[expose] public noncomputable section
open Subgroup Representation
open Representation.NormalPairSupport Representation.NormalPairHomogeneous
open Representation.AlternatingFive Representation.BinaryOffender.NaturalTensor
open Theory.SpecificGroups.SymmetricFive.ProjectedElementaryRank
namespace CFSG.Quasithin.Chapter10.SourceA5SeparatedMultiplicity

variable (F : Type*) [Field F] [Finite F] [CharP F 2]
local instance : Algebra (ZMod 2) F := ZMod.algebra F 2
variable {A Q V : Type*} [Group A] [Finite A] [IsElementaryAbelian 2 A]
  [Group Q] [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  (ρ : Representation (ZMod 2) Q V) (i : Alt × Alt →* Q)

/-- Complete the actual actor record from canonical natural support coordinates. -/
def naturalActorData (hF : Nat.card F = 4)
    (j : A →* Q) (c : A →* MulAut (Alt × Alt))
    (hc : ∀ a z, j a * i z * (j a)⁻¹ = i (c a z)) (hfaith : Function.Injective c)
    (hcomp : IsCompl (left ρ i) (right ρ i))
    (f : Alt ≃* Matrix.SpecialLinearGroup (Fin 2) F)
    (d : NormalPairHomogeneous.Coordinates ρ i (SL2.BinarySmall.natural.comp f.toMonoidHom)) :
    SeparatedActorData (ρ.comp j) d.multiplicity where
  conjugation := c
  faithful := hfaith
  preserved hb := by
    let e₁ : AmplifiedNatural.Coordinates F (ι := Fin d.multiplicity) (leftAction ρ i) := {
      marking := f
      equiv := d.leftEquiv
      intertwines := d.left_intertwines }
    let e₂ : AmplifiedNatural.Coordinates F (ι := Fin d.multiplicity) (rightAction ρ i) := {
      marking := f
      equiv := d.rightEquiv
      intertwines := d.right_intertwines }
    exact ⟨PreservedBlocks.of_natural F hF (ρ.comp j) (markedWreath c) d.multiplicity hb
      (firstBlock ρ i j c hc hb) (secondBlock ρ i j c hc hb)
      (Submodule.prodEquivOfIsCompl _ _ hcomp).symm
      (support_coordinates_intertwine ρ i j c hc hb hcomp)
      (leftAction ρ i) (rightAction ρ i) e₁ e₂
      (firstBlock_covariance ρ i j c hc hb)
      (secondBlock_covariance ρ i j c hc hb)⟩
  exchanged a ha := by
    refine ⟨left ρ i, ?_, swapping_support_disjoint ρ i j c hc hcomp.disjoint a ha⟩
    rw [d.leftEquiv.finrank_eq, Module.finrank_pi_fintype]
    have hd : Module.finrank (ZMod 2) (NaturalSpace F) = 4 :=
      finrank_natural F (n := 2) hF
    simp only [hd, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul,
      Nat.mul_comm d.multiplicity 4]

variable [Finite Q]

/-- The natural coordinates of the full quotient have multiplicity at most two,
using its actual starred actor and faithful marked conjugation. -/
theorem natural_multiplicity_le_two_of_starred_actor (hF : Nat.card F = 4)
    {E : Subgroup Q} (hE : E ∈ ChapterD.QhatStar ρ)
    (c : E →* MulAut (Alt × Alt))
    (hc : ∀ a z, a.val * i z * a.val⁻¹ = i (c a z)) (hfaith : Function.Injective c)
    (hcomp : IsCompl (left ρ i) (right ρ i))
    (f : Alt ≃* Matrix.SpecialLinearGroup (Fin 2) F)
    (d : NormalPairHomogeneous.Coordinates ρ i (SL2.BinarySmall.natural.comp f.toMonoidHom)) :
    d.multiplicity ≤ 2 := by
  let : IsElementaryAbelian 2 E := hE.1.2.1.2
  exact source_separated_multiplicity_le_two_of_starred_actor ρ hE d.multiplicity
    (naturalActorData F ρ i hF E.subtype c hc hfaith hcomp f d)

end CFSG.Quasithin.Chapter10.SourceA5SeparatedMultiplicity
