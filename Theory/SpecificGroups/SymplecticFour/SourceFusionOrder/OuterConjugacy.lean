module
public import Theory.SpecificGroups.SymplecticFour.SourceFusionOrder.FixedFlag
public import Theory.FieldTheory.QuadraticFrobenius

/-!
# Borel conjugacy of outer involutions over the four-element field

Borel cocycle descent expresses each outer flag involution as a Borel-inner
conjugate of a field involution. The unique involution of the quadratic
field is Frobenius, so two such automorphisms are conjugate through the
same native Borel. This explicit conjugator can be pulled back along the
whole-middle map of an original marked pair.

Source: Aschbacher--Smith F.4.29(2) and the Sp4(4) exception in F.4.37,
printed pp.289,293 of refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup
namespace Theory.SpecificGroups.SymplecticFour.SourceFusionOrder
open DiagramAutomorphisms
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

/-- Every outer flag involution over field order four is a Borel-inner
conjugate of the actual Frobenius automorphism. -/
theorem outer_flag_involution_frobenius (hF : Nat.card F=4)
    (a : MulAut (Sp F)) (hao : orderOf a=2)
    (ha : a ∈ SourceNormalizerExtension.flagAutomorphisms F)
    (hi : a ∉ MulAut.innerSubgroup (Sp F)) :
    ∃ c : borel (F := F),
      a = MulAut.conj c.val * fieldAutomorphism (frobeniusEquiv F 2) *
        (MulAut.conj c.val)⁻¹ := by
  obtain ⟨σ,hσ,c,hc⟩ := outer_flag_involution_normal_form
    (show Nat.card F=2^2 from hF) (by decide) a hao ha hi
  rw [FiniteField.involution_eq_frobenius_of_card_square
    (show Nat.card F=2^2 from hF) σ hσ] at hc
  exact ⟨c,hc⟩

/-- Two outer flag involutions over field order four have an explicit
conjugator in the original native Borel. -/
theorem outer_flag_involutions_borel_conjugate (hF : Nat.card F=4)
    (a b : MulAut (Sp F)) (hao : orderOf a=2) (hbo : orderOf b=2)
    (ha : a ∈ SourceNormalizerExtension.flagAutomorphisms F)
    (hb : b ∈ SourceNormalizerExtension.flagAutomorphisms F)
    (hai : a ∉ MulAut.innerSubgroup (Sp F))
    (hbi : b ∉ MulAut.innerSubgroup (Sp F)) :
    ∃ c : borel (F := F),
      MulAut.conj c.val * a * (MulAut.conj c.val)⁻¹ = b := by
  obtain ⟨x,hx⟩ := outer_flag_involution_frobenius hF a hao ha hai
  obtain ⟨y,hy⟩ := outer_flag_involution_frobenius hF b hbo hb hbi
  refine ⟨y*x⁻¹,?_⟩
  simp only [Subgroup.coe_mul,Subgroup.coe_inv,map_mul,map_inv]
  rw [hx,hy]
  group
end Theory.SpecificGroups.SymplecticFour.SourceFusionOrder
