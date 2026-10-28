module
public import Theory.Representation.BinaryTensorThree.SylowMarking
public import Theory.Representation.BinaryOffender.RestrictionComparison

/-!
# Involution displacement in the full binary tensor action

Sylow conjugacy transfers an elementary actor to the checked dihedral
wreath-square action. A nonidentity element there already has displacement
at least three, so every nontrivial elementary actor in the full tensor
group has at least this fixed codimension. The swapping involution attains
three in the companion Group module.

The original Chapter 10 automizer coordinates apply this bound to compute
its actual parameter m, then use E.6.3 to establish r ≥ 3 and s = 3.
Source: Aschbacher--Smith H.4.8 and 8.3.2, printed pp.383,723.
-/

public noncomputable section
open Subgroup Representation.BinaryOffender
namespace BinaryTensorThree

/-- Every nontrivial elementary two-subgroup of the full tensor group has
fixed codimension at least three. Sylow transport reuses the checked model. -/
theorem elementary_fixedCodim_ge_three (A : Subgroup Group) (hA : IsElementaryTwo A) :
    3 ≤ fixedCodim action A := by
  obtain ⟨B,hB,_,hc⟩ := elementary_geometry_of_sylow_range
    Small.actionSmall action Small.toTensorHom Small.toTensorHom_injective
    (LinearEquiv.refl (ZMod 2) Space) (fun _ _ => rfl)
    Small.tensorSylow Small.tensorSylow_coe.le A hA
  let : IsElementaryAbelian 2 B := hB.2
  obtain ⟨b,hb,hb1⟩ := B.bot_or_exists_ne_one.resolve_left hB.1
  have ht : orderOf b = 2 := orderOf_eq_prime
    (elemPow_eq_one_of_isElementaryAbelian b hb) hb1
  have hmin := Small.involution_fixedCodim b ht
  have hdim := Submodule.finrank_mono (fixedSpace_antitone Small.actionSmall (zpowers_le.mpr hb))
  have hd1 := fixedCodim_add_finrank Small.actionSmall B
  have hd2 := fixedCodim_add_finrank Small.actionSmall (zpowers b)
  omega

/-- The full tensor action has involution displacement at least three. -/
theorem involution_fixedCodim_ge_three (t : Group) (ht : orderOf t = 2) :
    3 ≤ fixedCodim action (zpowers t) := by
  have ht2 : t ^ 2 = 1 := by simpa only [ht] using pow_orderOf_eq_one t
  apply elementary_fixedCodim_ge_three
  refine ⟨?_,IsElementaryAbelian.zpowers_of_pow_eq_one ht2⟩
  intro he
  have h1 : t = 1 := by
    have hh := mem_zpowers t
    rwa [he,mem_bot] at hh
  rw [h1,orderOf_one] at ht
  exact (by decide : (1 : ℕ) ≠ 2) ht

end BinaryTensorThree
