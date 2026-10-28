module
public import Theory.GroupTheory.SmallNonabelianTwoGroupAutomorphismOrderCoarse
public import Theory.GroupTheory.PerfectPairOrder
public import Theory.PGroupCore
public import Theory.GroupTheory.PrimeRankOrderBound
public import Theory.ElementaryAbelian.Quotient

/-!
# Elementary subgroup and automorphism rank bounds

An elementary two-subgroup embeds in the central quotient when the ambient
two-core is trivial. Its order is therefore bounded by that quotient's
two-rank. An elementary group of order at most 128 has automorphism
prime-rank at most one outside three and seven, by the finite linear-group
order formula and squarefree divisibility.

These bounds retain the full central cover and do not require it to split.
Source application: Aschbacher--Smith 4.4.12, printed p.622.
-/

public section
open Subgroup
namespace Theory.GroupTheory

theorem elementary_card_le_of_twoCore_eq_bot
    {K : Type*} [Group K] [Finite K] (W : Subgroup K)
    (hW : IsElementaryAbelian 2 W) (hc : pCore 2 K = ⊥)
    {d : ℕ} (hr : primeRank 2 (K ⧸ center K) ≤ d) : Nat.card W ≤ 2 ^ d := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let := hW
  let C := W ⊓ center K
  have hn : C.Normal := by
    refine ⟨fun x hx g => ?_⟩
    have he := mem_center_iff.mp (show x ∈ center K from hx.2) g
    rw [he,mul_inv_cancel_right]
    exact hx
  have hC : C ≤ pCore 2 K := le_sSup ⟨hn, (IsElementaryAbelian.isPGroup 2 W).to_le inf_le_left⟩
  have hb : C = ⊥ := bot_unique (hC.trans_eq hc)
  let q := QuotientGroup.mk' (center K)
  let f := q.comp W.subtype
  have hf : Function.Injective f := by
    apply (MonoidHom.ker_eq_bot_iff f).mp
    apply bot_unique
    intro w hw
    have hz : (w : K) ∈ center K := (QuotientGroup.eq_one_iff _).mp hw
    exact Subtype.ext (show (w : K) = 1 from hb.le ⟨w.property,hz⟩)
  let : IsElementaryAbelian 2 f.range :=
    IsElementaryAbelian.of_surjective f.rangeRestrict f.rangeRestrict_surjective
  rw [Nat.card_congr (MonoidHom.ofInjective hf).toEquiv]
  exact (primeRank_le_iff_elementary_card_le (K ⧸ center K)).mp hr f.range inferInstance


theorem primeRank_mulAut_le_one_of_card_le_two_pow_seven
    (E : Type*) [Group E] [Finite E] [IsElementaryAbelian 2 E]
    (hc : Nat.card E ≤ 2 ^ 7)
    {p : ℕ} [Fact p.Prime] (ho : Odd p) (hp3 : p ≠ 3) (hp7 : p ≠ 7) :
    primeRank p (MulAut E) ≤ 1 := by
  have hcard : Nat.card (MulAut E) ∣ 2 ^ 21 * 3 ^ 4 * (5 * 7 ^ 2 * 31 * 127) := by
    obtain ⟨d,hd⟩ := (IsElementaryAbelian.isPGroup 2 E).exists_card_eq
    have hdim : d ≤ 7 := by
      rw [hd] at hc
      exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hc
    rw [SmallNonabelianTwoGroup.card_mulAut_elementary_two_pow E d hd]
    interval_cases d <;> norm_num [Fin.prod_univ_succ]
  apply primeRank_le_one_of_square_not_dvd
  intro hs
  have hp : p.Prime := Fact.out
  have h2 : Nat.Coprime p 2 := hp.coprime_iff_not_dvd.mpr (by
    intro hd
    have he := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hd
    subst p
    exact ho.not_two_dvd_nat (dvd_refl 2))
  have h3 : Nat.Coprime p 3 := hp.coprime_iff_not_dvd.mpr
    (fun hd => hp3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp hd))
  have h7 : Nat.Coprime p 7 := hp.coprime_iff_not_dvd.mpr
    (fun hd => hp7 ((Nat.prime_dvd_prime_iff_eq hp (by decide)).mp hd))
  have hco : Nat.Coprime (p ^ 2) (2 ^ 21 * 3 ^ 4 * 7 ^ 2) :=
    (((h2.pow_right 21).mul_right (h3.pow_right 4)).mul_right (h7.pow_right 2)).pow_left 2
  have hd : p ^ 2 ∣ 2 ^ 21 * 3 ^ 4 * 7 ^ 2 * (5 * 31 * 127) := by
    exact hs.trans (hcard.trans (by decide))
  have hsquare : Squarefree (5 * 31 * 127 : ℕ) := by
    apply (Nat.squarefree_mul (by decide : Nat.Coprime (5 * 31) 127)).mpr
    refine ⟨?_, (Nat.prime_iff.mp (by decide : Nat.Prime 127)).squarefree⟩
    exact (Nat.squarefree_mul (by decide : Nat.Coprime 5 31)).mpr
      ⟨(Nat.prime_iff.mp (by decide : Nat.Prime 5)).squarefree,
        (Nat.prime_iff.mp (by decide : Nat.Prime 31)).squarefree⟩
  exact (Nat.squarefree_iff_prime_squarefree.mp hsquare p hp)
    (by simpa only [pow_two] using hco.dvd_mul_left.mp hd)

end Theory.GroupTheory
