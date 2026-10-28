module

public import Theory.GroupTheory.PCoreQuotientJoinAction
public import Theory.GroupTheory.Commutator.PerfectCoreKernel
public import Theory.GroupTheory.AutomorphismOvergroupCore

/-!
# A cubic action controls a perfect subgroup through a two-core quotient

Suppose a three-group A normalizes J, and J/O₂(J) is centerless with
a two-group outer automorphism group and order not divisible by nine.
The action image has order at most three. A subgroup B of order three
inside both A and a perfect K ≤ J accounts for that entire image.
If O₂(J) normalizes K, then A normalizes K: the action kernel centralizes
J/O₂(J), so the perfect-subgroup core lemma makes it normalize K.

The kernel and diagonal subgroup retain their literal ambient embeddings.
Source application: Aschbacher–Smith, Proposition 9.3.1, printed p.732,
the rank-one overcomponent reduction; the PSL₂(25) case is instantiated
in Theory.SpecificGroups.PSL2.TwentyFiveCartanNormalizer.
-/

public section
open Subgroup Theory.GroupTheory
namespace Subgroup.CubicCoreQuotientNormalizer
theorem cubic_action_image_card_le_three {E X : Type*} [Group E] [Group X] [Finite X]
    (a : E →* MulAut X) (hA : IsPGroup 3 E)
    (hz : center X = ⊥) (hout : IsPGroup 2 (MulAut.Outer X))
    (hcard : ¬ 9 ∣ Nat.card X) : Nat.card a.range ≤ 3 := by
  let q := QuotientGroup.mk' (MulAut.innerSubgroup X)
  have h3 : IsPGroup 3 (a.range.map q) := (hA.of_surjective a.rangeRestrict a.rangeRestrict_surjective).map q
  have h2 : IsPGroup 2 (a.range.map q) := hout.to_subgroup _
  have hb : a.range.map q = ⊥ := by
    apply disjoint_self.mp
    exact h3.disjoint_of_coprime h2 (by decide)
  have hi : a.range ≤ MulAut.innerSubgroup X := by
    simpa only [q,QuotientGroup.ker_mk'] using (Subgroup.map_eq_bot_iff a.range).mp hb
  let ec : X ≃* MulAut.innerSubgroup X :=
    MonoidHom.ofInjective (conj_injective_of_center_eq_bot hz)
  have hd : Nat.card a.range ∣ Nat.card X := by
    rw [Nat.card_congr ec.toEquiv]
    exact Subgroup.card_dvd_of_le hi
  obtain ⟨k,hk⟩ := (hA.of_surjective a.rangeRestrict a.rangeRestrict_surjective).exists_card_eq
  rw [hk] at hd ⊢
  have hk1 : k ≤ 1 := by
    by_contra hn
    exact hcard ((pow_dvd_pow 3 (by omega : 2 ≤ k)).trans hd)
  exact (Nat.pow_le_pow_right (by decide) hk1)

variable {G : Type*} [Group G] [Finite G]
variable (K J A B : Subgroup G) [Group.IsPerfect K]
variable (hKJ : K ≤ J) (hAJ : A ≤ normalizer (J : Set G))
variable (hBA : B ≤ A) (hBK : B ≤ K)

@[expose] def action : A →* MulAut (J ⧸ pCore 2 J) :=
  (pCoreJoinAction 2 hAJ).comp (inclusion le_sup_right)

omit [Finite G] [Group.IsPerfect K] in
private theorem action_inner (b : B) :
    action J A hAJ (inclusion hBA b) =
      MulAut.conj (QuotientGroup.mk' (pCore 2 J) (inclusion (hBK.trans hKJ) b)) := by
  change pCoreJoinAction 2 hAJ (inclusion le_sup_right (inclusion hBA b)) = _
  have he : inclusion le_sup_right (inclusion hBA b) =
      inclusion le_sup_left (inclusion (hBK.trans hKJ) b) := by rfl
  rw [he,pCoreJoinAction_on_component]

include hKJ hBK in
omit [Finite G] [Group.IsPerfect K] in
private theorem action_B_injective (hB : IsPGroup 3 B)
    (hz : center (J ⧸ pCore 2 J) = ⊥) :
    Function.Injective ((action J A hAJ).comp (inclusion hBA)) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply eq_bot_iff.mpr
  intro b hb
  have hi := action_inner K J A B hKJ hAJ hBA hBK b
  have ha : action J A hAJ (inclusion hBA b) = 1 := hb
  rw [hi] at ha
  have hq : QuotientGroup.mk' (pCore 2 J) (inclusion (hBK.trans hKJ) b) = 1 := by
    apply conj_injective_of_center_eq_bot hz
    simpa only [map_one] using ha
  have hbc : (b : G) ∈ J.pCoreIn 2 :=
    ⟨inclusion (hBK.trans hKJ) b,(QuotientGroup.eq_one_iff _).mp hq,rfl⟩
  have hd : Disjoint B (J.pCoreIn 2) :=
    hB.disjoint_of_coprime (isPGroup_pCoreIn 2 J) (by decide)
  have hb1 : (b : G) = 1 := mem_bot.mp ((disjoint_iff.mp hd).le ⟨b.property,hbc⟩)
  exact Subtype.ext hb1

include hKJ in
theorem action_kernel_normalizes
    (hQK : J.pCoreIn 2 ≤ normalizer (K : Set G)) :
    ((action J A hAJ).ker.map A.subtype) ≤ normalizer (K : Set G) := by
  let C := (action J A hAJ).ker.map A.subtype
  have hJC : ⁅J,C⁆ ≤ J.pCoreIn 2 := by
    rw [commutator_comm]
    apply commutator_le.mpr
    intro c hc j hj
    obtain ⟨c,hc,rfl⟩ := hc
    let j' : J := ⟨j,hj⟩
    let cj := J.normalizerMonoidHom (inclusion hAJ c) j'
    have hc' : action J A hAJ c = 1 := hc
    have ha := MulEquiv.congr_fun hc' (QuotientGroup.mk' (pCore 2 J) j')
    change pCoreJoinAction 2 hAJ (inclusion le_sup_right c)
      (QuotientGroup.mk' (pCore 2 J) j') = _ at ha
    rw [pCoreJoinAction_mk] at ha
    change QuotientGroup.mk' (pCore 2 J) cj = QuotientGroup.mk' (pCore 2 J) j' at ha
    refine ⟨cj * j'⁻¹, ?_, rfl⟩
    apply (QuotientGroup.eq_one_iff _).mp
    change QuotientGroup.mk' (pCore 2 J) (cj * j'⁻¹) = 1
    rw [map_mul,map_inv,ha,mul_inv_cancel]
  exact le_normalizer_iff_commutator_le_left.mpr
    ((perfect_subgroup_core_commutator K J C hKJ hQK hJC).trans (pCoreIn_le 2 K))

include hKJ hBK hBA in
theorem normalizes_of_small_image
    (hQK : J.pCoreIn 2 ≤ normalizer (K : Set G))
    (hB : Nat.card B = 3) (hz : center (J ⧸ pCore 2 J) = ⊥)
    (hsmall : Nat.card (action J A hAJ).range ≤ 3) :
    A ≤ normalizer (K : Set G) := by
  let f := action J A hAJ
  let g := f.comp (inclusion hBA)
  have hBp : IsPGroup 3 B := IsPGroup.of_card (n := 1) (by simpa using hB)
  have hgi : Function.Injective g := action_B_injective K J A B hKJ hAJ hBA hBK hBp hz
  have hgc : Nat.card g.range = 3 :=
    (Nat.card_congr (MonoidHom.ofInjective hgi).toEquiv).symm.trans hB
  have hr : g.range = f.range := eq_of_le_of_card_ge
    (by rintro _ ⟨b,rfl⟩; exact ⟨inclusion hBA b,rfl⟩) (by rw [hgc]; exact hsmall)
  have hker := action_kernel_normalizes K J A hKJ hAJ hQK
  intro a ha
  let a' : A := ⟨a,ha⟩
  obtain ⟨b,hb⟩ : f a' ∈ g.range := hr.symm ▸ ⟨a',rfl⟩
  have hx : a' * (inclusion hBA b)⁻¹ ∈ f.ker := by
    change f (a' * (inclusion hBA b)⁻¹) = 1
    rw [map_mul,map_inv,←hb]
    exact mul_inv_cancel _
  have hn := (normalizer (K : Set G)).mul_mem
    (hker ⟨_,hx,rfl⟩) (K.le_normalizer (hBK b.property))
  change (a * (b : G)⁻¹) * (b : G) ∈ normalizer (K : Set G) at hn
  simpa only [inv_mul_cancel_right] using hn
end Subgroup.CubicCoreQuotientNormalizer
