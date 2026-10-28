module

public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Blocks.Setup
public import Theory.GroupTheory.PrimeRankFixedJoin
public import Theory.GroupTheory.PGroup.NormalSubgroups
public import Stellmacher.OmegaOneCenterMap

/-!
# The elementary exclusions in the corank-one block case

A normal subgroup whose order is divisible by p cannot be disjoint from a
full-rank elementary p-subgroup: intersect with a Sylow group, choose a central
subgroup of order p in the normal intersection, and adjoin it to the elementary
subgroup. Applied in N_G(W), this excludes a faithful E₉ action as soon as
3 divides |C_G(U)| and W ≤ U. Faithfulness here is injectivity of the literal
conjugation homomorphism.

For the omega-center conclusion a nonidentity normal two-subgroup of N_T(U)
disjoint from U supplies a central involution outside U. The construction of
this subgroup from alternating blocks remains a separate obligation.
It must use U(L) = [O₂(L),L]: the printed proof's use of O₂(L) as a
fixed-point-free module does not cover the central extension allowed by
C.1.13(c).

Source: Aschbacher–Smith, combined manuscript (1 March 2004), the proof of
E.6.10(3–4), printed p.249 (PDF p.260).
-/

public section

namespace CFSG.Quasithin.ChapterE.Section06
open Subgroup
variable {G : Type*} [Group G] [Finite G]

private theorem rank_ge_of_disjoint_normal {p n : ℕ} [Fact p.Prime]
    (N A : Subgroup G) [N.Normal] [IsElementaryAbelian p A]
    (hN : p ∣ Nat.card N) (hA : Nat.card A = p ^ n) (hd : Disjoint A N) :
    n + 1 ≤ primeRank p G := by
  obtain ⟨P, hAP⟩ := (IsElementaryAbelian.isPGroup p A).exists_le_sylow
  obtain ⟨R, hR⟩ := P.exists_subgroupOf_eq_of_normal N
  have hRne := R.ne_bot_of_dvd_card hN
  have hNP : N.subgroupOf (P : Subgroup G) ≠ ⊥ := by
    intro he
    apply hRne
    rw [hR]
    apply eq_bot_iff.mpr
    intro x hx
    have hh : (⟨x, hx⟩ : P) ∈ N.subgroupOf (P : Subgroup G) := x.property
    rw [he] at hh
    have hx1 : (x : G) = 1 := congrArg Subtype.val (mem_bot.mp hh)
    exact mem_bot.mpr (Subtype.ext hx1)
  let _ : Fact (IsPGroup p P) := ⟨P.isPGroup'⟩
  obtain ⟨Z, _, hZN, hZc, hZcent⟩ :=
    exists_central_subgroup_card_eq_prime_in_normal (p := p) (N.subgroupOf (P : Subgroup G))
      ((nontrivial_iff_ne_bot _).mpr hNP)
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := Z) p (by rw [hZc])
  have hzG : orderOf ((z : P) : G) = p := by
    rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hz]
  have hzN : ((z : P) : G) ∈ N := hZN z.property
  have hzA : ((z : P) : G) ∉ A := by
    intro ha
    have he : ((z : P) : G) = 1 := hd.le_bot ⟨ha, hzN⟩
    have hp := (Fact.out : p.Prime).one_lt
    rw [he, orderOf_one] at hzG
    omega
  have hfix : A ≤ centralizer ({((z : P) : G)} : Set G) := by
    intro a ha
    apply mem_centralizer_singleton_iff.mpr
    exact congrArg Subtype.val ((mem_center_iff.mp (hZcent z.property)) ⟨a, hAP ha⟩)
  exact IsElementaryAbelian.primeRank_ge_of_fixed_join A ((z : P) : G) hzG hzA hfix hA

/-- The group-theoretic part of E.6.10(3). Its only remaining block input is
the divisibility of the escaping centralizer's order by three. -/
theorem HypothesisE61.no_faithful_nine_of_three_dvd
    {𝒦 : GroupClass} {T : Sylow 2 G} {M V U : Subgroup G}
    (h : HypothesisE61 𝒦 T M V) (hUV : U ≤ V)
    (hthree : 3 ∣ Nat.card (centralizer (U : Set G)))
    (W : Subgroup G) (hWU : W ≤ U)
    (A : Subgroup G) [IsElementaryAbelian 3 A] (hA : Nat.card A = 9)
    (hAN : A ≤ normalizer (W : Set G)) :
    ¬ Function.Injective (W.normalizerMonoidHom.comp (inclusion hAN)) := by
  intro hf
  have hdis : Disjoint A (centralizer (W : Set G)) := by
    apply disjoint_iff.mpr
    apply eq_bot_iff.mpr
    intro x hx
    have hker : inclusion hAN ⟨x, hx.1⟩ ∈ W.normalizerMonoidHom.ker := by
      rw [normalizerMonoidHom_ker]
      exact hx.2
    have he : (⟨x, hx.1⟩ : A) = 1 := hf (by
      change W.normalizerMonoidHom (inclusion hAN ⟨x, hx.1⟩) = _
      simp only [MonoidHom.mem_ker.mp hker, map_one])
    exact mem_bot.mpr (congrArg Subtype.val he)
  have hWne : W ≠ ⊥ := by
    intro he
    have hAt : A = ⊥ := by
      apply le_bot_iff.mp
      intro a ha
      exact hdis.le_bot ⟨ha, by
        rw [he]
        intro x hx
        rw [show x = 1 from mem_bot.mp hx, one_mul, mul_one]⟩
    rw [hAt, card_bot] at hA
    omega
  let N := normalizer (W : Set G)
  let C := (centralizer (W : Set G)).subgroupOf N
  let E := A.subgroupOf N
  let _ : IsElementaryAbelian 3 E :=
    IsElementaryAbelian.subgroupOf hAN
  have hC : 3 ∣ Nat.card C := by
    rw [Nat.card_congr (subgroupOfEquivOfLe (centralizer_le_normalizer (W : Set G))).toEquiv]
    exact hthree.trans (card_dvd_of_le (Subgroup.centralizer_le hWU))
  have hE : Nat.card E = 3 ^ 2 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hAN).toEquiv, hA]
    decide
  have hd : Disjoint E C := by
    apply disjoint_iff.mpr
    apply eq_bot_iff.mpr
    intro x hx
    exact mem_bot.mpr (Subtype.ext (hdis.le_bot ⟨hx.1, hx.2⟩))
  have hr := rank_ge_of_disjoint_normal C E hC hE hd
  let _ := h.elementary
  have hw : IsPGroup 2 W := (IsElementaryAbelian.isPGroup 2 V).to_le (hWU.trans hUV)
  have hb := isQuasithin_iff_twoLocal.mp h.simpleQTKE.quasithin N
    ⟨W, hWne, hw, rfl⟩ 3 (by decide) (by decide)
  omega

/-- The central-involution step of E.6.10(4), for the actual subgroup N_T(U).
The block argument must construct D and prove relative normality and disjointness. -/
theorem omega_center_not_le_of_normal_disjoint
    (T U D : Subgroup G) (hT : IsPGroup 2 T)
    (hDS : D ≤ T ⊓ normalizer (U : Set G))
    (hDn : (D.subgroupOf (T ⊓ normalizer (U : Set G))).Normal)
    (hDne : D ≠ ⊥) (hDU : Disjoint D U) :
    ¬ Stellmacher.omegaOneCenterAmbient (T ⊓ normalizer (U : Set G)) ≤ U := by
  let S := T ⊓ normalizer (U : Set G)
  let _ := hDn
  let _ : Fact (IsPGroup 2 S) := ⟨hT.to_le inf_le_left⟩
  have hD : Nontrivial (D.subgroupOf S) := by
    apply (nontrivial_iff_ne_bot _).mpr
    intro he
    apply hDne
    have hh := congrArg (fun B : Subgroup S => B.map S.subtype) he
    simpa only [map_subgroupOf_eq_of_le (show D ≤ S from hDS), Subgroup.map_bot] using hh
  obtain ⟨Z, _, hZD, hZc, hZcent⟩ :=
    exists_central_subgroup_card_eq_prime_in_normal (p := 2) (D.subgroupOf S) hD
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := Z) 2 (hZc ▸ dvd_rfl)
  have hzG : orderOf ((z : S) : G) = 2 := by
    rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hz]
  have hzO : ((z : S) : G) ∈ Stellmacher.omegaOneCenterAmbient S := by
    apply (Stellmacher.mem_omegaOneCenterAmbient_iff _ _).mpr
    refine ⟨(z : S).property, hzG ▸ pow_orderOf_eq_one _, ?_⟩
    intro x hx
    exact congrArg Subtype.val ((mem_center_iff.mp (hZcent z.property)) ⟨x, hx⟩)
  intro hOU
  have he : ((z : S) : G) = 1 := hDU.le_bot ⟨hZD z.property, hOU hzO⟩
  rw [he, orderOf_one] at hzG
  omega

end CFSG.Quasithin.ChapterE.Section06
