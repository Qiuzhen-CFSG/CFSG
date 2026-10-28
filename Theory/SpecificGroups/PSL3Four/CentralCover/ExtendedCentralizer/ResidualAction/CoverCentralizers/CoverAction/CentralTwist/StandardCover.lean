module

public import Theory.SpecificGroups.PSL3Four.CentralCover.ExtendedCentralizer.ResidualAction.CoverCentralizers.CoverAction.CentralTwist.Normalization
public import Theory.SpecificGroups.PSL3Four.CentralCover.ExtendedCentralizer.ResidualAction.CoverCentralizers.CoverAction.CentralTwist.StandardCover.RootPresentation
public import Theory.SpecificGroups.PSL3Four.CentralCover.InnerFamilyNormalizer.DoubleCover.NontrivialDisplacement.UnitaryCoordinates
public import Theory.GroupTheory.Commutator.CentralSylowTransfer

/-!
# A central twist for the standard graph-field lift on the four-cover

Involution lifting through the elementary central kernel makes the two lifted
unitary root planes elementary abelian. The resulting class-two Sylow
presentation has four cross commutators with explicitly computed images.
If every projectively fixed element were fixed upstairs, the three diagonal
commutators would coincide and the derived subgroup would inject into PSL₃(4).
Central Sylow transfer contradicts this: perfectness places the nontrivial
covering center in that derived subgroup.

Thus some y satisfies a(y) = z*y with z a nonidentity central element. The
stronger `graphField_lift_twist` uses just the perfect four-cover and the
compatible graph-field action. `standard_cover_twist` retains all four inputs
of the marked-action interface, including its E₉ residual equivalence.
No centralizer order, nontrivial defect, or concrete-cover comparison is an
additional premise. The original marked-action assembly remains in the parent.

Source: Aschbacher--Smith 15.3.38, printed pp.1136--1137, and I.2.2(3b)
with its transfer observation (i), printed pp.409--410, combined manuscript
of 1 March 2004. The root-commutator implication reuses the checked
`DoubleCover.NontrivialDisplacement.RootPair` calculation.
-/

public section

open Subgroup
open scoped commutatorElement
namespace Matrix.PSL3Four.ExtendedCentralizer.CoverCentralizers.CentralTwist
open ProjectiveFixer
open InnerFamilyNormalizer.DoubleCover.NontrivialDisplacement

private theorem graphField_lift_square {E : Type*} [Group E]
    (c : FourCover E) (a : MulAut E)
    (ha : ∀ x, c.toMonoidHom (a x) = graphField (c.toMonoidHom x)) : a ^ 2 = 1 := by
  apply c.toCover.autMap_injective c.ker_eq_center
  have hdesc : c.toCover.autMap c.ker_eq_center a = graphField := by
    ext x
    obtain ⟨y, rfl⟩ := c.surjective x
    rw [c.toCover.autMap_apply, ha]
  rw [map_pow, map_one, hdesc, graphField_sq]

/-- Every compatible graph-field lift to a perfect four-cover has a nontrivial central twist. -/
theorem graphField_lift_twist {E : Type*} [Group E] [Finite E]
    (c : FourCover E) (a : MulAut E)
    (ha : ∀ x, c.toMonoidHom (a x) = graphField (c.toMonoidHom x)) :
    ∃ y : E, ∃ z : center E, z ≠ 1 ∧ a y = (z : E) * y := by
  classical
  let := c.isPerfect
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have ha2 := graphField_lift_square c a ha
  obtain ⟨d⟩ := fourCover_liftedRootPair c a ha2 ha unitarySylowModel
  by_contra hn
  have hfixed (x : E) (hx : c.toMonoidHom (a x) = c.toMonoidHom x) : a x = x := by
    have hz : a x * x⁻¹ ∈ center E := c.ker_le_center (by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hx, mul_inv_cancel])
    let z : center E := ⟨a x * x⁻¹, hz⟩
    by_cases he : z = 1
    · exact mul_inv_eq_one.mp (congrArg Subtype.val he)
    · exact (hn ⟨x, z, he, by dsimp [z]; rw [inv_mul_cancel_right]⟩).elim
  have hb : d.action ^ 2 = 1 := by
    ext x
    simpa only [pow_two, MulAut.mul_apply, MulAut.one_apply, d.compatible] using
      involutive_apply a ha2 (x : E)
  let f : d.sylow →* PSL := c.toMonoidHom.comp (d.sylow : Subgroup E).subtype
  have hbot : f.ker ⊓ _root_.commutator d.sylow = ⊥ :=
    d.roots.kernel_inf_derived_eq_bot f d.action hb (by
      intro x hx
      apply Subtype.ext
      exact (d.compatible x).trans (hfixed x (by
        simpa only [f, MonoidHom.comp_apply, Subgroup.subtype_apply, d.compatible] using hx)))
  let : Nontrivial (center E) := Finite.one_lt_card_iff_nontrivial.mp (by
    rw [c.center_isKleinFour.card_four]; decide)
  obtain ⟨z, hz⟩ := exists_ne (1 : center E)
  have hp : IsPGroup 2 (center E) :=
    IsPGroup.of_card (p := 2) (n := 2) c.center_isKleinFour.card_four
  have hzS : (z : E) ∈ (d.sylow : Subgroup E) := hp.le_sylow_of_normal d.sylow z.property
  have hzD : (z : E) ∈ ⁅(d.sylow : Subgroup E), (d.sylow : Subgroup E)⁆ :=
    center_inf_commutator_inf_sylow_le_commutator d.sylow
      ⟨⟨z.property, by rw [Group.IsPerfect.commutator_eq_top]; exact mem_top _⟩, hzS⟩
  rw [← map_subtype_commutator] at hzD
  obtain ⟨w, hw, hwz⟩ := hzD
  change (w : E) = z at hwz
  have hwker : w ∈ f.ker := by
    change c.toMonoidHom (w : E) = 1
    rw [hwz]
    exact (c.ker_eq_center.symm ▸ z.property : (z : E) ∈ c.toMonoidHom.ker)
  have hwone : w = 1 := mem_bot.mp
    (hbot ▸ (show w ∈ f.ker ⊓ _root_.commutator d.sylow from ⟨hwker, hw⟩))
  apply hz
  apply Subtype.ext
  exact hwz.symm.trans (congrArg Subtype.val hwone)

/-- The standard-cover contract with all inputs retained for the marked-action assembly. -/
theorem standard_cover_twist {E : Type*} [Group E] [Finite E]
    (c : FourCover E) (a : MulAut E)
    (_hlift : PSL3.OuterSolvable.standard F ≤ (c.toCover.autMap c.ker_eq_center).range)
    (hcompat : ∀ x : E, c.toMonoidHom (a x) = graphField (c.toMonoidHom x))
    (_hcenter : ∀ z : center E, a (z : E) = z)
    (_e : pResidual 2 a.fixedSubgroup ≃* ElementaryNine) :
    ∃ y : E, ∃ z : center E, z ≠ 1 ∧ a y = (z : E) * y :=
  graphField_lift_twist c a hcompat

end Matrix.PSL3Four.ExtendedCentralizer.CoverCentralizers.CentralTwist
