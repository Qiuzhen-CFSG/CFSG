module

public import Theory.SpecificGroups.PSL3Four.CentralCover.NormalizerComparison

/-! Restrict a four-cover and its actual normalizer action to the core
inside that normalizer. The literal subgroup coordinates are retained. -/

public noncomputable section
open Subgroup
namespace Matrix.PSL3Four

private def pullbackCover {E E' : Type*} [Group E] [Group E']
    (c : FourCover E) (e : E' ≃* E) : FourCover E' := by
  let := c.isPerfect
  let := c.center_isKleinFour
  have hk : (c.toMonoidHom.comp e.toMonoidHom).ker = center E' := by
    ext x
    change c.toMonoidHom (e x) = 1 ↔ x ∈ center E'
    rw [←MonoidHom.mem_ker,c.ker_eq_center]
    constructor
    · intro hx
      apply mem_center_iff.mpr
      intro y
      apply e.injective
      simpa only [map_mul] using mem_center_iff.mp hx (e y)
    · intro hx
      apply mem_center_iff.mpr
      intro y
      obtain ⟨z,rfl⟩ := e.surjective y
      simpa only [map_mul] using congrArg e (mem_center_iff.mp hx z)
  exact {
    toMonoidHom := c.toMonoidHom.comp e.toMonoidHom
    surjective := c.surjective.comp e.surjective
    isPerfect := Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
    ker_le_center := hk.le
    ker_eq_center := hk
    center_isKleinFour := {
      card_four := (Nat.card_congr (centerCongr e).toEquiv).trans IsKleinFour.card_four
      exponent_two := (centerCongr e).monoidExponent_eq.trans IsKleinFour.exponent_two } }

/-- The actual cover in normalizer-subgroup coordinates has exactly the
original descended actor homomorphism. -/
theorem FourCover.exists_normalizer_coordinates
    {G : Type*} [Group G] (B : Subgroup G) (c : FourCover B) :
    ∃ cN : FourCover (B.subgroupOf (normalizer (B : Set G))),
      (∀ b, cN.toMonoidHom b = c.toMonoidHom (subgroupOfEquivOfLe B.le_normalizer b)) ∧
      (cN.toCover.autMap cN.ker_eq_center).comp MulAut.conjNormal =
        (c.toCover.autMap c.ker_eq_center).comp B.normalizerMonoidHom := by
  let e := subgroupOfEquivOfLe B.le_normalizer
  let cN := pullbackCover c e
  refine ⟨cN,fun _ => rfl,?_⟩
  ext n x
  obtain ⟨b,rfl⟩ := cN.surjective x
  rw [MonoidHom.comp_apply,MonoidHom.comp_apply,cN.toCover.autMap_apply]
  change c.toMonoidHom (e (MulAut.conjNormal n b)) =
    c.toCover.autMap c.ker_eq_center (B.normalizerMonoidHom n) (c.toMonoidHom (e b))
  rw [c.toCover.autMap_apply]
  rfl

end Matrix.PSL3Four
