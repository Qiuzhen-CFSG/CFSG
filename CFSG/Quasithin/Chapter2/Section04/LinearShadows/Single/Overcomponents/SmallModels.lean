module
public import Theory.GroupTheory.CenterQuotientOrder
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.SL2CoverOrders
public import Theory.SpecificGroups.PSL3Four.FieldExtension.Basic
public import Theory.Mathieu.M22.Properties.TwoRank
public import Mathlib.GroupTheory.SpecificGroups.Alternating

/-!
# Low-rank overcomponents of the original natural block

The central-quotient order excludes A₆ and restricts PSL₃(4) to degree two.
The binary M₂₂ residue of the actual 2.3.9 catalogue has two-rank at most
five, whereas the source block with nontrivial center has an elementary
core of rank at least six. No cover-classification premise is added.
Source: Aschbacher–Smith 2.4.11, printed p.532.
-/
public section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.ChapterC
namespace CFSG.Quasithin.Chapter2.LinearShadows.Single.Overcomponents
variable {L K : Type*} [Group L] [Group K] [Finite L] [Finite K]
lemma no_alternating_six {n : ℕ} (h : IsL2EvenBlock L n)
    (hc : pCore 2 L = blockU L) (f : L →* K) (hf : Function.Injective f)
    (e : (K ⧸ center K) ≃* alternatingGroup (Fin 6)) : False := by
  have hd := Theory.GroupTheory.card_quotient_center_dvd_of_injective f hf
  rw [h.center_quotient_card hc, Nat.card_congr e.toEquiv,
    nat_card_alternatingGroup, Nat.card_fin] at hd
  norm_num at hd
  have hlow : 2^n ≥ 4 := Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) h.1
  have hpow : 2^(3*n) ≥ 64 := Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) (by have := h.1; omega : 6 ≤ 3*n)
  have hsq : (2^n)^2 - 1 ≥ 15 := Nat.sub_le_sub_right (Nat.pow_le_pow_left hlow 2) 1
  have hb := Nat.le_of_dvd (by decide : 0 < 360) hd
  have hh := Nat.mul_le_mul hpow hsq
  omega

lemma degree_two_of_psl_three_four {n : ℕ} (h : IsL2EvenBlock L n)
    (hc : pCore 2 L = blockU L) (f : L →* K) (hf : Function.Injective f)
    (e : (K ⧸ center K) ≃* Matrix.PSL3Four.PSL) : n = 2 := by
  have hd := Theory.GroupTheory.card_quotient_center_dvd_of_injective f hf
  rw [h.center_quotient_card hc, Nat.card_congr e.toEquiv, Matrix.PSL3Four.card_PSL] at hd
  by_contra hn
  have hn3 : 3 ≤ n := by have := h.1; omega
  have hlow : 2^n ≥ 8 := Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) hn3
  have hpow : 2^(3*n) ≥ 512 := Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) (by omega : 9 ≤ 3*n)
  have hsq : (2^n)^2 - 1 ≥ 63 := Nat.sub_le_sub_right (Nat.pow_le_pow_left hlow 2) 1
  have hb := Nat.le_of_dvd (by decide : 0 < 20160) hd
  have hh := Nat.mul_le_mul hpow hsq
  omega

private lemma m22_small_kernel_rank (f : K →* Sporadic.Mathieu.M22)
    (hc : Nat.card f.ker ≤ 2) : primeRank 2 K ≤ 5 := by
  have hk : primeRank 2 f.ker ≤ 1 := by
    apply (primeRank_le_iff_elementary_card_le f.ker).mpr
    intro A _
    simpa using (Nat.le_of_dvd (Nat.card_pos (α := f.ker)) A.card_subgroup_dvd_card).trans hc
  have hb := Theory.GroupTheory.primeRank_le_ker_add (p := 2) f
  have hm := Sporadic.Mathieu.m22_twoRank_le_four
  omega

lemma no_binary_m22 {n : ℕ} (h : IsL2EvenBlock L n)
    (hc : pCore 2 L = blockU L) (hz : Nat.card (center L) = 2^n)
    (f : L →* K) (hf : Function.Injective f)
    (q : K →* Sporadic.Mathieu.M22) (hq : Nat.card q.ker ≤ 2) : False := by
  let := h.2.1.elementary
  have hU : Nat.card (blockU L) = 2^(3*n) := by
    have hfixed : Nat.card (blockFixed L) = Nat.card (center L) :=
      Nat.card_congr (subgroupOfEquivOfLe (h.center_le_module hc)).toEquiv
    rw [card_eq_card_quotient_mul_card_subgroup (blockFixed L), hfixed, hz]
    rw [show Nat.card (blockU L ⧸ blockFixed L) = 2^(n*2) from h.module_card]
    rw [← pow_add, show n*2+n=3*n by omega]
  have hk := m22_small_kernel_rank q hq
  have hLrank := (primeRank_le_of_injective 2 f hf).trans hk
  have he := (primeRank_le_iff_elementary_card_le L).mp hLrank (blockU L) inferInstance
  rw [hU] at he
  have hpow : 2^(3*n) ≥ 64 := Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) (by have := h.1; omega : 6 ≤ 3*n)
  norm_num at he
  omega
end CFSG.Quasithin.Chapter2.LinearShadows.Single.Overcomponents
