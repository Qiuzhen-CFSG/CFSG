module
public import Theory.GroupAction.NormalComplement
public import Mathlib.GroupTheory.GroupAction.FixingSubgroup
public import Mathlib.GroupTheory.PGroup
public import Theory.GroupTheory.NormalizingInvolutionCard

/-!
# An index-two fixed subgroup and Burnside transfer

The pointwise fixer of a subgroup of index two in a finite two-group is a
two-group: displacement embeds it into the group of functions with values
in the fixed subgroup. If an abelian Sylow subgroup has such a pointwise
fixed subgroup under its normalizer, the normalizer action is both a
two-group and of odd order, hence trivial. Burnside transfer supplies the
normal two-complement.

Source application: Parrott (1972), printed p.683, the abelian centralizer
Sylow subgroup of order at most sixteen and its fixed subgroup of order
at least eight. No solvability assumption is used.
-/

open Subgroup
open scoped IsMulCommutative
namespace Subgroup
variable {G : Type*} [Group G]

private theorem fixed_index_two_displacement_mem (C : Subgroup G) (hi : C.index = 2)
    (a : fixingSubgroup (MulAut G) (C : Set G)) (x : G) : x⁻¹ * (a : MulAut G) x ∈ C := by
  have hf : ∀ y ∈ C, (a : MulAut G) y = y := (mem_fixingSubgroup_iff (MulAut G)).mp a.property
  have hm : (a : MulAut G) x ∈ C ↔ x ∈ C := by
    constructor
    · intro hx
      have heq : (a : MulAut G) x = x := (a : MulAut G).injective (hf _ hx)
      exact heq ▸ hx
    · intro hx
      exact (hf _ hx).symm ▸ hx
  rw [C.mul_mem_iff_of_index_two hi, inv_mem_iff, hm]

private def fixedIndexTwoDisplacement (C : Subgroup G) (hi : C.index = 2) :
    fixingSubgroup (MulAut G) (C : Set G) →* (G → C) where
  toFun a x := ⟨x⁻¹ * (a : MulAut G) x, fixed_index_two_displacement_mem C hi a x⟩
  map_one' := by funext x; apply Subtype.ext; simp
  map_mul' a b := by
    funext x
    apply Subtype.ext
    change x⁻¹ * (a : MulAut G) ((b : MulAut G) x) =
      (x⁻¹ * (a : MulAut G) x) * (x⁻¹ * (b : MulAut G) x)
    have hf := (mem_fixingSubgroup_iff (MulAut G)).mp a.property _ (fixed_index_two_displacement_mem C hi b x)
    change (a : MulAut G) (x⁻¹ * (b : MulAut G) x) = x⁻¹ * (b : MulAut G) x at hf
    rw [map_mul, map_inv] at hf
    calc
      _ = x⁻¹ * ((a : MulAut G) x * ((a : MulAut G) x)⁻¹ * (a : MulAut G) ((b : MulAut G) x)) := by simp
      _ = _ := by rw [mul_assoc ((a : MulAut G) x), hf, mul_assoc]

public theorem isPGroup_fixingSubgroup_of_index_two [Finite G]
    (C : Subgroup G) (hi : C.index = 2) (hp : IsPGroup 2 C) :
    IsPGroup 2 (fixingSubgroup (MulAut G) (C : Set G)) := by
  have hfunc : IsPGroup 2 (G → C) := by
    obtain ⟨n, hn⟩ := hp.exists_card_dvd_pow
    intro f
    refine ⟨n, ?_⟩
    funext x
    exact orderOf_dvd_iff_pow_eq_one.mp ((_root_.orderOf_dvd_natCard (f x)).trans hn)
  apply hfunc.of_injective (fixedIndexTwoDisplacement C hi)
  intro a b hab
  apply Subtype.ext
  apply MulEquiv.ext
  intro x
  exact mul_left_cancel (congrArg Subtype.val (congrFun hab x))

end Subgroup

namespace Sylow
variable {G : Type*} [Group G] [Finite G]
public theorem normalizer_le_centralizer_of_fixed_index_le_two
    (P : Sylow 2 G) [IsMulCommutative P] (A : Subgroup P)
    (hi : A.index ≤ 2)
    (hf : ∀ n : normalizer (P : Set G), ∀ a ∈ A,
      (P : Subgroup G).normalizerMonoidHom n a = a) :
    normalizer (P : Set G) ≤ centralizer (P : Set G) := by
  let f := (P : Subgroup G).normalizerMonoidHom
  have hr : f.range ≤ fixingSubgroup (MulAut P) (A : Set P) := by
    rintro _ ⟨n, rfl⟩
    exact (mem_fixingSubgroup_iff (MulAut P)).mpr (hf n)
  have hfix : IsPGroup 2 (fixingSubgroup (MulAut P) (A : Set P)) := by
    have hpos : A.index ≠ 0 := Nat.card_pos.ne'
    interval_cases hidx : A.index
    · omega
    · have hA : A = ⊤ := index_eq_one.mp hidx
      subst A
      have heq : fixingSubgroup (MulAut P) ((⊤ : Subgroup P) : Set P) = ⊥ := by
        apply eq_bot_iff.mpr
        intro a ha
        apply MulEquiv.ext
        intro x
        exact (mem_fixingSubgroup_iff (MulAut P)).mp ha x (mem_top x)
      rw [heq]
      exact IsPGroup.of_bot
    · exact A.isPGroup_fixingSubgroup_of_index_two hidx (P.isPGroup'.to_subgroup A)
  have hp := hfix.to_le hr
  obtain ⟨n, hn⟩ := hp.exists_card_eq
  have hcard : (centralizer (P : Set G)).relIndex (normalizer (P : Set G)) = 2 ^ n := by
    rw [← hn, ← index_ker, normalizerMonoidHom_ker]
    rfl
  have hPc : (P : Subgroup G) ≤ centralizer (P : Set G) := by
    intro x hx y hy
    exact (congrArg Subtype.val (mul_comm (⟨y,hy⟩ : P) ⟨x,hx⟩))
  have hd : (centralizer (P : Set G)).relIndex (normalizer (P : Set G)) ∣
      (P : Subgroup G).index :=
    (relIndex_dvd_of_le_left _ hPc).trans (relIndex_dvd_index_of_le P.le_normalizer)
  have heq : (centralizer (P : Set G)).relIndex (normalizer (P : Set G)) = 1 := by
    rw [hcard] at hd ⊢
    by_cases hzero : n = 0
    · simp [hzero]
    · exact False.elim (P.not_dvd_index ((dvd_pow_self 2 hzero).trans hd))
  exact relIndex_eq_one.mp heq
end Sylow

namespace Sylow
variable {G : Type*} [Group G] [Finite G]
public theorem hasNormalTwoComplement_of_fixed_index_le_two
    (P : Sylow 2 G) [IsMulCommutative P] (A : Subgroup P)
    (hi : A.index ≤ 2)
    (hf : ∀ n : normalizer (P : Set G), ∀ a ∈ A,
      (P : Subgroup G).normalizerMonoidHom n a = a) :
    HasNormalPComplement 2 G := by
  let hn := P.normalizer_le_centralizer_of_fixed_index_le_two A hi hf
  let O := (MonoidHom.transferSylow P hn).ker
  have hcomp := MonoidHom.ker_transferSylow_isComplement' P hn
  refine ⟨O, inferInstance, Nat.prime_two.coprime_iff_not_dvd.mpr
    (MonoidHom.not_dvd_card_ker_transferSylow P hn), ?_⟩
  exact P.isPGroup'.of_equiv hcomp.symm.QuotientMulEquiv.symm
end Sylow

namespace Sylow
variable {G : Type*} [Group G] [Finite G]

public theorem hasNormalTwoComplement_of_order_le_sixteen
    (P : Sylow 2 G) [IsMulCommutative P] (hP : Nat.card P ≤ 16)
    (E : Subgroup G) (hEP : E ≤ P) (hEcard : Nat.card E = 4)
    (hEN : normalizer (P : Set G) ≤ centralizer (E : Set G))
    (k : G) (hkP : k ∈ (P : Subgroup G)) (hk : k ∈ center G)
    (hk2 : orderOf k = 2) (hkE : k ∉ E) : HasNormalPComplement 2 G := by
  let B := E ⊔ zpowers k
  have hBP : B ≤ P := sup_le hEP (zpowers_le.mpr hkP)
  let A := B.subgroupOf P
  have hBcard : Nat.card B = 8 := by
    rw [card_sup_zpowers_of_normalizing_involution E k
      (by simpa [hk2] using pow_orderOf_eq_one k) hkE
      (centralizer_le_normalizer _ (fun x _ => mem_center_iff.mp hk x)), hEcard]
  have hAcard : Nat.card A = 8 :=
    (Nat.card_congr (subgroupOfEquivOfLe hBP).toEquiv).trans hBcard
  have hAi : A.index ≤ 2 := by
    have hh := A.card_mul_index
    rw [hAcard] at hh
    change 8 * A.index = Nat.card P at hh
    omega
  apply P.hasNormalTwoComplement_of_fixed_index_le_two A hAi
  intro n a ha
  apply Subtype.ext
  change (n : G) * (a : G) * (n : G)⁻¹ = (a : G)
  apply mul_inv_eq_iff_eq_mul.mpr
  have hB : B ≤ centralizer ({(n : G)} : Set G) := by
    apply sup_le
    · intro e he
      exact mem_centralizer_singleton_iff.mpr ((hEN n.property) e he)
    · exact zpowers_le.mpr (mem_centralizer_singleton_iff.mpr (mem_center_iff.mp hk n).symm)
  exact (mem_centralizer_singleton_iff.mp (hB ha)).symm
end Sylow
