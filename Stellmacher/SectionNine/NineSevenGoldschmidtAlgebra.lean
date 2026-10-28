module

public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic
public import Mathlib.Tactic

open scoped commutatorElement

namespace Stellmacher.SectionNine

variable {G : Type*} [Group G]

public theorem involution_conjugate_commutator_fourth_power
    (left right : G) (hleft : left ^ 2 = 1) (hright : right ^ 2 = 1) :
    ⁅left, right * left * right⁻¹⁆ = (left * right) ^ 4 := by
  have hleftInv : left⁻¹ = left := inv_eq_of_mul_eq_one_right (by
    simpa only [pow_two] using hleft)
  have hrightInv : right⁻¹ = right := inv_eq_of_mul_eq_one_right (by
    simpa only [pow_two] using hright)
  simp only [commutatorElement_def, mul_inv_rev, hleftInv, hrightInv]
  simp only [pow_succ, pow_zero, one_mul, mul_assoc]

public theorem involution_conjugate_commutators_inverse
    (left right : G) (hleft : left ^ 2 = 1) (hright : right ^ 2 = 1) :
    ⁅left, right * left * right⁻¹⁆⁻¹ = ⁅right, left * right * left⁻¹⁆ := by
  rw [involution_conjugate_commutator_fourth_power left right hleft hright,
    involution_conjugate_commutator_fourth_power right left hright hleft,
    ← inv_pow, mul_inv_rev]
  have hleftInv : left⁻¹ = left := inv_eq_of_mul_eq_one_right (by
    simpa only [pow_two] using hleft)
  have hrightInv : right⁻¹ = right := inv_eq_of_mul_eq_one_right (by
    simpa only [pow_two] using hright)
  rw [hleftInv, hrightInv]

public theorem involution_conjugate_commutators_eq_one
    (left right : G) (hleft : left ^ 2 = 1) (hright : right ^ 2 = 1)
    (firstCenter secondCenter : Subgroup G)
    (hfirst : ⁅left, right * left * right⁻¹⁆ ∈ firstCenter)
    (hsecond : ⁅right, left * right * left⁻¹⁆ ∈ secondCenter)
    (hdisjoint : firstCenter ⊓ secondCenter = ⊥) :
    ⁅left, right * left * right⁻¹⁆ = 1 ∧
      ⁅right, left * right * left⁻¹⁆ = 1 := by
  have hinverse := involution_conjugate_commutators_inverse left right hleft hright
  have hboth : ⁅left, right * left * right⁻¹⁆ ∈ firstCenter ⊓ secondCenter :=
    ⟨hfirst, secondCenter.inv_mem_iff.mp (hinverse.symm ▸ hsecond)⟩
  rw [hdisjoint, Subgroup.mem_bot] at hboth
  exact ⟨hboth, by rw [← hinverse, hboth, inv_one]⟩

public theorem commutator_conjugate_eq_bot_of_generator
    (moduleSubgroup factor : Subgroup G) (actor generator : G)
    (hgenerate : moduleSubgroup = factor ⊔ Subgroup.zpowers generator)
    (hleft : ⁅factor, moduleSubgroup.map (MulAut.conj actor).toMonoidHom⁆ = ⊥)
    (hright : ⁅moduleSubgroup, factor.map (MulAut.conj actor).toMonoidHom⁆ = ⊥)
    (hdiagonal : ⁅generator, actor * generator * actor⁻¹⁆ = 1) :
    ⁅moduleSubgroup, moduleSubgroup.map (MulAut.conj actor).toMonoidHom⁆ = ⊥ := by
  have hgenerator : generator ∈ moduleSubgroup := by
    rw [hgenerate]
    exact (show Subgroup.zpowers generator ≤ factor ⊔ Subgroup.zpowers generator from
      le_sup_right) (Subgroup.mem_zpowers generator)
  apply Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
  calc
    moduleSubgroup = factor ⊔ Subgroup.zpowers generator := hgenerate
    _ ≤ Subgroup.centralizer
        (moduleSubgroup.map (MulAut.conj actor).toMonoidHom : Set G) := by
      apply sup_le (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hleft)
      apply Subgroup.le_centralizer_iff.mpr
      rw [hgenerate, Subgroup.map_sup]
      apply sup_le
      · apply Subgroup.le_centralizer_iff.mp
        exact Subgroup.zpowers_le.mpr
          ((Subgroup.commutator_eq_bot_iff_le_centralizer.mp hright) hgenerator)
      · rw [MonoidHom.map_zpowers]
        apply Subgroup.zpowers_le.mpr
        apply Subgroup.mem_centralizer_iff.mpr
        intro element helement
        have hcommute : Commute generator (actor * generator * actor⁻¹) :=
          commutatorElement_eq_one_iff_commute.mp hdiagonal
        obtain ⟨power, rfl⟩ := helement
        exact (hcommute.zpow_left power).eq

public theorem goldschmidt_commutator_collapse
    (moduleSubgroup factor firstCenter secondCenter : Subgroup G)
    (actor generator : G) (hactor : actor ^ 2 = 1) (hgenerator : generator ^ 2 = 1)
    (hgenerate : moduleSubgroup = factor ⊔ Subgroup.zpowers generator)
    (hleft : ⁅factor, moduleSubgroup.map (MulAut.conj actor).toMonoidHom⁆ = ⊥)
    (hright : ⁅moduleSubgroup, factor.map (MulAut.conj actor).toMonoidHom⁆ = ⊥)
    (hfirst : ⁅actor, generator * actor * generator⁻¹⁆ ∈ firstCenter)
    (hsecond : ⁅generator, actor * generator * actor⁻¹⁆ ∈ secondCenter)
    (hdisjoint : firstCenter ⊓ secondCenter = ⊥) :
    ⁅moduleSubgroup, moduleSubgroup.map (MulAut.conj actor).toMonoidHom⁆ = ⊥ := by
  exact commutator_conjugate_eq_bot_of_generator moduleSubgroup factor actor generator
    hgenerate hleft hright
    (involution_conjugate_commutators_eq_one actor generator hactor hgenerator
      firstCenter secondCenter hfirst hsecond hdisjoint).2

end Stellmacher.SectionNine

