module

public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.TwoQuotient
public import Theory.Mathieu.M12.A5Fixer.Automorphisms.OuterIndex
public import Theory.Mathieu.M12.SylowOvergroups.RankTwoCoverage
public import Theory.GroupTheory.SubgroupProductCard
public import Theory.GroupTheory.PResidual.SubnormalSupplement
public import Mathlib.GroupTheory.Perm.Centralizer

/-!
# The Cartan restriction for the actual M₁₂ automorphism groups

For a Cartan witness, the odd abelian group and its permuting Sylow generate
a proper subgroup: otherwise an eleven-element forces the abelian group
into a permutation centralizer of order eleven. The native proper-Sylow-
overgroup bound then makes the cyclic Cartan order divide 192, so the
exponent is at most two. The checked outer-index bound and the normal-kernel
transport include every automorphism subgroup containing the inner group.

Source: Aschbacher--Smith, Definition E.3.37 and the M₁₂ row in Tables
7.2.1 and 7.3.4, printed pp.239 and 698--699.
-/

public section
namespace CFSG.Quasithin.Chapter7.NormalizedSource.MathieuGeneration.Models
open Subgroup
open scoped Pointwise IsMulCommutative
open CFSG.Quasithin.ChapterE.Section06.FixedPointBounds
open Sporadic.Mathieu

private theorem abelian_card_dvd_eleven (B : Subgroup M12)
    [IsMulCommutative B] (h11 : 11 ∣ Nat.card B) : Nat.card B ∣ 11 := by
  classical
  let : Fact (Nat.Prime 11) := ⟨by decide⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := B) 11 h11
  let p : Equiv.Perm (Fin 12) := x.val.val
  have hp : orderOf p = 11 := by
    simpa only [p, Subgroup.orderOf_coe] using hx
  have hc : p.IsCycle := Equiv.Perm.isCycle_of_prime_order' (by rw [hp]; norm_num)
    (by rw [hp]; norm_num)
  have htype : p.cycleType = {11} := by
    rw [hc.cycleType, ← hc.orderOf, hp]
  have hcentral : Nat.card (centralizer ({p} : Set (Equiv.Perm (Fin 12)))) = 11 := by
    rw [Equiv.Perm.nat_card_centralizer, htype]
    norm_num
  let f : B →* centralizer ({p} : Set (Equiv.Perm (Fin 12))) :=
    (M12.subtype.comp B.subtype).codRestrict _ (by
      intro b
      rw [mem_centralizer_singleton_iff]
      change b.val.val * x.val.val = x.val.val * b.val.val
      exact congrArg (fun a : B => a.val.val) (mul_comm b x))
  have hf : Function.Injective f := by
    intro a b h
    exact Subtype.ext (Subtype.ext (congrArg (fun z => z.val) h))
  simpa only [hcentral] using card_dvd_of_injective f hf

private theorem sylow_card (S : Sylow 2 M12) : Nat.card S = 64 := by
  rw [Sylow.card_eq_multiplicity, m12_order]
  decide +kernel

private theorem sup_ne_top {c : ℕ} (w : NPrimeWitness M12 c) :
    w.abelianGroup ⊔ (w.sylow : Subgroup M12) ≠ ⊤ := by
  intro htop
  have hs := sylow_card w.sylow
  have hd : Disjoint w.abelianGroup (w.sylow : Subgroup M12) := by
    apply disjoint_of_coprime_natCard
    rw [hs]
    exact (Nat.coprime_two_right.mpr w.odd).pow_right 6
  have hprod := card_set_mul_mul_card_inf w.abelianGroup (w.sylow : Subgroup M12)
  rw [hd.eq_bot, Subgroup.card_bot, mul_one,
    ← coe_sup_of_set_mul_comm _ _ w.permutes, htop] at hprod
  have htopcard : Nat.card (⊤ : Subgroup M12) = Nat.card M12 := Nat.card_congr Subgroup.topEquiv.toEquiv
  change Nat.card (⊤ : Subgroup M12) = _ at hprod
  rw [htopcard, m12_order, hs] at hprod
  have hB : Nat.card w.abelianGroup = 1485 := by omega
  let := w.abelian
  have he := abelian_card_dvd_eleven w.abelianGroup (by rw [hB]; norm_num)
  norm_num [hB] at he

theorem m12_nPrime_le_two : nPrime M12 ≤ 2 := by
  apply nPrime_le_iff.mpr
  intro c w
  have hd := M12SmallPair.SylowOvergroups.card_dvd_192_of_ne_top
    (w.abelianGroup ⊔ (w.sylow : Subgroup M12)) (sup_ne_top w) ⟨w.sylow, le_sup_right⟩
  have hcy : 2 ^ c - 1 ∣ 192 := by
    rw [← w.card]
    exact (card_dvd_of_le (w.cyclic_le.trans le_sup_left)).trans hd
  have hc : c < 8 := by
    by_contra h
    have hpow : 2 ^ 8 ≤ 2 ^ c := Nat.pow_le_pow_right (by decide) (by omega)
    have hle := Nat.le_of_dvd (by norm_num : 0 < 192) hcy
    norm_num at hpow
    omega
  interval_cases c <;> omega

private theorem conjugation_injective :
    Function.Injective (MulAut.conj : M12 →* MulAut M12) := by
  apply (injective_iff_map_eq_one _).mpr
  intro g hg
  have hc : g ∈ center M12 := by
    rw [mem_center_iff]
    intro x
    have hx := congrArg (fun a : MulAut M12 => a x) hg
    change g * x * g⁻¹ = x at hx
    exact (mul_inv_eq_iff_eq_mul.mp hx).symm
  simpa only [m12_center_eq_bot, mem_bot] using hc

private theorem outer_two_group : IsPGroup 2 (MulAut.Outer M12) := by
  have hle : Nat.card (MulAut.Outer M12) ≤ 2 := by
    rw [← index_eq_card]
    exact M12A5Fixer.Automorphisms.outerIndexBound
  have hpos : 0 < Nat.card (MulAut.Outer M12) := Nat.card_pos
  have hc : Nat.card (MulAut.Outer M12) = 1 ∨ Nat.card (MulAut.Outer M12) = 2 := by omega
  rcases hc with h | h
  · exact IsPGroup.of_card (n := 0) (by simpa using h)
  · exact IsPGroup.of_card (n := 1) (by simpa using h)

theorem m12_aut_nPrime_le (A : Subgroup (MulAut M12))
    (hA : MulAut.innerSubgroup M12 ≤ A) : nPrime A ≤ nPrime M12 :=
  automorphism_subgroup_nPrime_le conjugation_injective outer_two_group A hA

/-- The literal inner-containing automorphism-group bound for M₁₂. -/
theorem m12_cartanRestriction (A : Subgroup (MulAut M12))
    (hA : MulAut.innerSubgroup M12 ≤ A) : nPrime A ≤ 2 :=
  (m12_aut_nPrime_le A hA).trans m12_nPrime_le_two

end CFSG.Quasithin.Chapter7.NormalizedSource.MathieuGeneration.Models
