module
public import Theory.SpecificGroups.PSL3Four.RootNormalizerModel.InvariantSubgroups.CentralCover
public import Theory.SpecificGroups.PSL3.LinearThreeSylow.CubicRootGeometry

/-!
# The three-primary kernel of the actual Sylow restriction

An automorphism fixing the actual Sylow two-subgroup of PSL₃(F₄) is
conjugation by an element of its center. This is a two-element. Consequently
restricting an action to the Sylow and identifying that Sylow with UT₃(F₄)
adds no three-torsion to the action kernel. The constructed action retains
its literal compatibility with the original projective action.

Source application: the common-normalizer E₉ in Aschbacher--Smith 2.5.7,
printed p.556. The original normalizer action supplies the earlier kernel
bound; no faithfulness of the restricted action is assumed.
-/
public section

open Subgroup
open scoped MatrixGroups
namespace Matrix.PSL3Four.RootNormalizerModel
variable {A : Type*} [Group A] [Finite A]

private noncomputable def sylowRestriction (α : A →* MulAut PSL) (P : Sylow 2 PSL)
    (hP : ∀ a : A, (P : Subgroup PSL).map (α a).toMonoidHom = P) : A →* MulAut P where
  toFun a := ((α a).subgroupMap (P : Subgroup PSL)).trans (MulEquiv.subgroupCongr (hP a))
  map_one' := by
    ext u
    change α 1 (u : PSL) = (u : PSL)
    rw [map_one, MulAut.one_apply]
  map_mul' a b := by
    ext u
    change α (a * b) (u : PSL) = α a (α b (u : PSL))
    rw [map_mul, MulAut.mul_apply]

/-- Restriction to an actual Sylow two-subgroup retains a three-prime kernel.
The only possible additional fixer is conjugation by a central Sylow element,
which has two-power order. -/
private theorem sylowRestriction_kernel_coprime (α : A →* MulAut PSL)
    (P : Sylow 2 PSL)
    (hP : ∀ a : A, (P : Subgroup PSL).map (α a).toMonoidHom = P)
    (hk : Nat.Coprime 3 (Nat.card α.ker)) :
    Nat.Coprime 3 (Nat.card (sylowRestriction α P hP).ker) := by
  apply Nat.prime_three.coprime_iff_not_dvd.mpr
  intro hd
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' 3 hd
  have hfix : ∀ p ∈ (P : Subgroup PSL), α (a : A) p = p := by
    intro p hp
    have hh := DFunLike.congr_fun a.property (⟨p, hp⟩ : P)
    exact congrArg Subtype.val hh
  obtain ⟨z, hz, he⟩ := Matrix.PSL3.LinearThree.exists_sylow_center_conj_of_equiv F
    (by decide : 0 < 2) (by simpa using card_F) (MulEquiv.refl _) P (α (a : A)) hfix
  obtain ⟨m, hm⟩ := P.isPGroup'.exists_card_eq
  have hzP : z ∈ (P : Subgroup PSL) := map_subtype_le _ hz
  have hzpow : z ^ (2 ^ m) = 1 := by
    have hh : (⟨z, hzP⟩ : (P : Subgroup PSL)) ^ Nat.card (P : Subgroup PSL) = 1 :=
      pow_card_eq_one'
    rw [hm] at hh
    exact congrArg Subtype.val hh
  have hapow : α (a : A) ^ 3 = 1 := by
    rw [← map_pow]
    have hh := pow_orderOf_eq_one a
    rw [ha] at hh
    have hA : (a : A) ^ 3 = 1 := congrArg Subtype.val hh
    rw [hA, map_one]
  have hapow2 : α (a : A) ^ (2 ^ m) = 1 := by
    rw [he, ← map_pow, hzpow, map_one]
  have hone : α (a : A) = 1 := by
    apply orderOf_eq_one_iff.mp
    apply Nat.dvd_one.mp
    have hh := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hapow)
      (orderOf_dvd_of_pow_eq_one hapow2)
    simpa only [((by decide : Nat.Coprime 3 2).pow_right m).gcd_eq_one] using hh
  have hc : 3 ∣ Nat.card α.ker := by
    have hh := orderOf_dvd_natCard (⟨(a : A), hone⟩ : α.ker)
    rw [← Subgroup.orderOf_coe (⟨(a : A), hone⟩ : α.ker), Subgroup.orderOf_coe a, ha] at hh
    exact hh
  exact Nat.prime_three.coprime_iff_not_dvd.mp hk hc

/-- The literal Sylow supplies a root-coordinate action with no three-primary
kernel added by restriction. -/
theorem exists_root_action (α : A →* MulAut PSL) (P : Sylow 2 PSL)
    (hP : ∀ a : A, (P : Subgroup PSL).map (α a).toMonoidHom = P)
    (hk : Nat.Coprime 3 (Nat.card α.ker)) :
    ∃ e : Root ≃* P, ∃ β : A →* MulAut Root,
      (∀ a u, (e (β a u) : PSL) = α a (e u)) ∧
      Nat.Coprime 3 (Nat.card β.ker) := by
  obtain ⟨e₀⟩ := Matrix.PSL3.LinearThree.four_sylow_coordinates F card_F P
  let e : Root ≃* P := evenRootEquiv.symm.trans e₀
  let r := sylowRestriction α P hP
  let β : A →* MulAut Root := (MulAut.congr e.symm).toMonoidHom.comp r
  refine ⟨e, β, ?_, ?_⟩
  · intro a u
    change (e (e.symm (r a (e u))) : PSL) = _
    rw [e.apply_symm_apply]
    rfl
  · rw [MonoidHom.ker_comp_of_injective _ _ (MulAut.congr e.symm).injective]
    exact sylowRestriction_kernel_coprime α P hP hk
end Matrix.PSL3Four.RootNormalizerModel
