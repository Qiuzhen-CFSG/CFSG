module
public import Theory.Representation.BinaryConjugationSection.ImageDimensions
public import Theory.Representation.BinaryOffender.DualFixedSupplement

/-!
# Dual offenders from literal commutator bounds

If the full commutator of an actor on a binary section lies in C, the
actor's dual fixed codimension is at most the dimension of C's image.
The original denominator computes that image order. Comparison with the
literal actor image therefore proves the dual offender inequality.
A second commutator bound into the denominator gives quadraticity on the
same section. Neither assertion assumes a faithful action.

Source application: Aschbacher--Smith 8.3.12, printed p.726,
with U/⟨z⟩, the original V-image and C=V₅.
-/

public section
namespace Representation.BinaryConjugationSection
open Subgroup BinaryOffender
variable {G E : Type*} [Group G] [Finite G] [Group E] [Finite E]
  {H U Z : Subgroup G} {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]

/-- A bound on the entire commutator image gives an offender on the literal dual. -/
theorem dual_offender_of_commutator_index
    (σ : Representation (ZMod 2) E W) (π : H →* E)
    (c : BinaryConjugationSection H U Z (σ.comp π))
    (A C : Subgroup G) (hC : C ≤ U)
    (hcomm : ⁅A,U⁆ ≤ C)
    (hEA : IsElementaryTwo ((A.subgroupOf H).map π))
    (hi : Z.relIndex C ≤ Nat.card ((A.subgroupOf H).map π)) :
    IsOffender σ.dual ((A.subgroupOf H).map π) := by
  let : Finite W := Finite.of_surjective (fun u : U => (c.coordinates u).toAdd)
    (Multiplicative.toAdd.surjective.comp c.onto)
  have hm : subspaceCommutator σ ⊤ ((A.subgroupOf H).map π) ≤ c.imageSpace C := by
    apply Submodule.span_le.mpr
    rintro _ ⟨a,⟨x,hx,rfl⟩,v,_,rfl⟩
    exact c.displacement_range_le_imageSpace_of_commutator_le A C hcomm x hx ⟨v,rfl⟩
  have hcard : Nat.card (c.imageSpace C) ≤ Nat.card ((A.subgroupOf H).map π) := by
    rw [c.imageSpace_card_eq_relIndex C hC]
    exact hi
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod,
    hEA.card_eq_two_pow_rank] at hcard
  refine ⟨hEA,?_⟩
  rw [fixedCodim_dual_eq_moved_finrank]
  exact (Submodule.finrank_mono hm).trans
    ((Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hcard)

omit [Finite G] [Finite E] in
/-- Two successive commutator bounds give quadraticity on the same actor image. -/
theorem quadratic_of_commutator_bounds
    (σ : Representation (ZMod 2) E W) (π : H →* E)
    (c : BinaryConjugationSection H U Z (σ.comp π))
    (A C : Subgroup G) (hcomm : ⁅A,U⁆ ≤ C) (hfixed : ⁅A,C⁆ ≤ Z) :
    IsQuadratic σ ((A.subgroupOf H).map π) := by
  rintro a ⟨x,hx,rfl⟩ b ⟨y,hy,rfl⟩ v
  exact c.fixed_on_imageSpace_of_commutator_le A C hfixed x hx _
    (c.displacement_range_le_imageSpace_of_commutator_le A C hcomm y hy ⟨v,rfl⟩)

end Representation.BinaryConjugationSection
