module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.Swapped.ParameterObstruction
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.Basic
public import Theory.SpecificGroups.SymplecticFour.Sylow.AmbientOrder

/-!
# Comparing the exchanged quotient with the block models

The order formula for the actual projective special linear group determines
an even-field rank-one parameter uniquely. Its only overlap with an odd-prime
rank-one model has field orders four and five. Thus a surviving natural block
retains the parity and congruence restrictions on its own field parameter.

The alternating, triple-cover, binary-linear and symplectic alternatives are
excluded using their actual quotient equivalences and orders. These are model
comparisons for the C.2.7 sieve; they do not assert that C.2.7 has been applied,
or exclude its SL₃ alternative.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), C.2.7(3),
printed pp.145–147; 15.4.20, printed p.1164. The imported order formulas
retain their original ATLAS attribution and license.
-/

@[expose] public section

open Subgroup
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.CoreElimination.BlockSieve.ExchangedCases
variable {Q : Type*} [Group Q]

theorem psl_order {q : ℕ} (h : ClassicalGroup.IsPSL Q 2 q) :
    1 < q ∧ Nat.card Q * Nat.gcd 2 (q - 1) = q * (q ^ 2 - 1) := by
  obtain ⟨F, _, _, hq, ⟨e⟩⟩ := h
  have hc := BenderSuzuki.External.huppert614_card_psl_mul_center (K := F)
  rw [← Nat.card_congr e.toEquiv, Atlas.ExceptionalSupport.card_sl_center,
    Fintype.card_fin, hq] at hc
  exact ⟨hq ▸ Finite.one_lt_card (α := F), hc⟩

private theorem orderPoly_strict {a b : ℕ} (ha : 1 < a) (hab : a < b) :
    a * (a ^ 2 - 1) < b * (b ^ 2 - 1) := by
  calc
    a * (a ^ 2 - 1) < b * (a ^ 2 - 1) :=
      Nat.mul_lt_mul_of_pos_right hab (Nat.sub_pos_of_lt (by nlinarith))
    _ ≤ b * (b ^ 2 - 1) :=
      Nat.mul_le_mul_left _ (Nat.sub_le_sub_right (Nat.pow_le_pow_left hab.le 2) 1)

private theorem gcd_two_pred_of_even {q : ℕ} (hq : 1 < q) (he : Even q) :
    Nat.gcd 2 (q - 1) = 1 := by
  apply Nat.Coprime.gcd_eq_one
  apply Nat.coprime_two_left.mpr
  rw [Nat.odd_iff]
  rw [even_iff_two_dvd, Nat.dvd_iff_mod_eq_zero] at he
  omega

theorem even_psl_order {n : ℕ} (h : ClassicalGroup.IsPSL Q 2 (2 ^ n)) :
    Nat.card Q = 2 ^ n * ((2 ^ n) ^ 2 - 1) := by
  obtain ⟨hq, hc⟩ := psl_order h
  have hn : n ≠ 0 := by rintro rfl; norm_num at hq
  rwa [gcd_two_pred_of_even hq ((by decide : Even 2).pow_of_ne_zero hn), mul_one] at hc

theorem even_psl_parameter_unique {m n : ℕ}
    (hm : ClassicalGroup.IsPSL Q 2 (2 ^ m))
    (hn : ClassicalGroup.IsPSL Q 2 (2 ^ n)) : m = n := by
  have he := (even_psl_order hm).symm.trans (even_psl_order hn)
  have hpow : 2 ^ m = 2 ^ n := by
    rcases lt_trichotomy (2 ^ m) (2 ^ n) with h | h | h
    · exact False.elim ((ne_of_lt (orderPoly_strict (psl_order hm).1 h)) he)
    · exact h
    · exact False.elim ((ne_of_lt (orderPoly_strict (psl_order hn).1 h)) he.symm)
  exact Nat.pow_right_injective (by decide) hpow

/-- The only even-field/odd-prime PSL₂ overlap has field orders four and five. -/
theorem even_psl_odd_prime_overlap {n p : ℕ}
    (h : ClassicalGroup.IsPSL Q 2 (2 ^ n))
    (hp : p.Prime) (ho : Odd p) (hodd : ClassicalGroup.IsPSL Q 2 p) :
    n = 2 ∧ p = 5 := by
  let q := 2 ^ n
  have hq : 1 < q := (psl_order h).1
  have hn : n ≠ 0 := by rintro rfl; norm_num [q] at hq
  have hc := (psl_order hodd).2
  have hg : Nat.gcd 2 (p - 1) = 2 := by
    apply Nat.gcd_eq_left_iff_dvd.mpr
    rw [Nat.dvd_iff_mod_eq_zero]
    rw [Nat.odd_iff] at ho
    omega
  rw [hg, even_psl_order h] at hc
  change q * (q ^ 2 - 1) * 2 = p * (p ^ 2 - 1) at hc
  have hpn2 : p ≠ 2 := by rintro rfl; norm_num at ho
  have hp2 : ¬ p ∣ 2 := by
    intro hd
    exact hpn2 (Nat.le_antisymm (Nat.le_of_dvd (by decide) hd) hp.two_le)
  have hpq : ¬ p ∣ q := fun hd => hp2 (hp.dvd_of_dvd_pow hd)
  have hd : p ∣ q * (q ^ 2 - 1) * 2 := by rw [hc]; exact dvd_mul_right _ _
  have hd' : p ∣ q ^ 2 - 1 :=
    ((hp.dvd_mul.mp ((hp.dvd_mul.mp hd).resolve_right hp2))).resolve_left hpq
  have hsquare : q ^ 2 - 1 = (q - 1) * (q + 1) := by
    zify [show 1 ≤ q by omega, show 1 ≤ q ^ 2 by nlinarith]
    ring
  rw [hsquare] at hd'
  have hple : p ≤ q + 1 := by
    rcases hp.dvd_mul.mp hd' with h₁ | h₂
    · exact (Nat.le_of_dvd (by omega) h₁).trans (by omega)
    · exact Nat.le_of_dvd (by omega) h₂
  have hplt : q < p := by
    by_contra hnlt
    have hpq' : p ≤ q := by omega
    have hm : p * (p ^ 2 - 1) ≤ q * (q ^ 2 - 1) :=
      Nat.mul_le_mul hpq' (Nat.sub_le_sub_right (Nat.pow_le_pow_left hpq' 2) 1)
    have hpos : 0 < q * (q ^ 2 - 1) := Nat.mul_pos (by omega) (Nat.sub_pos_of_lt (by nlinarith))
    omega
  have hpeq : p = q + 1 := by omega
  rw [hpeq] at hc
  have hq4 : q = 4 := by
    zify [show 1 ≤ q ^ 2 by nlinarith, show 1 ≤ (q + 1) ^ 2 by nlinarith] at hc
    have hqpos : (0 : ℤ) < q := by omega
    have hcancel : (q : ℤ) * ((q - 4) * (q + 1)) = 0 := by nlinarith only [hc]
    have hz := (mul_eq_zero.mp hcancel).resolve_left (ne_of_gt hqpos)
    have hz' := (mul_eq_zero.mp hz).resolve_right (by omega)
    omega
  have hn2 : n = 2 := Nat.pow_right_injective (by decide) hq4
  exact ⟨hn2, by omega⟩

/-- A surviving natural rank-one block keeps its own field parameter. -/
theorem l2Block_parameter {L : Type*} [Group L] {n : ℕ}
    (hblock : CFSG.Quasithin.ChapterC.IsL2EvenBlock L n)
    (hswap : CFSG.Quasithin.Chapter1.XiEmbedding.SwappedModel 3 (L ⧸ pCore 2 L)) :
    Even n ∧ Nat.ModEq 3 (2 ^ n) 1 := by
  obtain ⟨_, _, F, _, _, hF, hmodel, _⟩ := hblock
  rcases hswap with ⟨m, hm, hmod, he⟩ | ⟨p, hp, ho, he⟩
  · obtain rfl := even_psl_parameter_unique hmodel he
    exact ⟨hm, hmod⟩
  · obtain ⟨rfl, _⟩ := even_psl_odd_prime_overlap hmodel hp ho he
    decide

private theorem psl_parameter_bounds {q c a b : ℕ}
    (hc : c * Nat.gcd 2 (q - 1) = q * (q ^ 2 - 1))
    (hlo : (a - 1) * ((a - 1) ^ 2 - 1) < c)
    (hhi : 2 * c < (b + 1) * ((b + 1) ^ 2 - 1)) : a ≤ q ∧ q ≤ b := by
  have hgpos : 1 ≤ Nat.gcd 2 (q - 1) := Nat.gcd_pos_of_pos_left _ (by decide)
  have hgle : Nat.gcd 2 (q - 1) ≤ 2 := Nat.gcd_le_left _ (by decide)
  have hl : c ≤ q * (q ^ 2 - 1) := by nlinarith only [hgpos, hc]
  have hh : q * (q ^ 2 - 1) ≤ 2 * c := by nlinarith only [hgle, hc]
  constructor
  · by_contra h
    have he : q ≤ a - 1 := by omega
    have hm := Nat.mul_le_mul he (Nat.sub_le_sub_right (Nat.pow_le_pow_left he 2) 1)
    omega
  · by_contra h
    have he : b + 1 ≤ q := by omega
    have hm := Nat.mul_le_mul he (Nat.sub_le_sub_right (Nat.pow_le_pow_left he 2) 1)
    omega

/-- Order 360 forces the field order nine, before using the prime restriction. -/
theorem psl_parameter_of_card_360 {q : ℕ} (hc : Nat.card Q = 360)
    (h : ClassicalGroup.IsPSL Q 2 q) : q = 9 := by
  have ho := (psl_order h).2
  rw [hc] at ho
  obtain ⟨hl, hu⟩ := psl_parameter_bounds (a := 8) (b := 9) ho (by decide) (by decide)
  interval_cases q <;> norm_num at *

/-- None of the remaining exceptional orders is a PSL₂ order. -/
theorem not_psl_of_exceptional_order {q : ℕ}
    (hc : Nat.card Q = 1080 ∨ Nat.card Q = 2520 ∨ Nat.card Q = 6048 ∨
      Nat.card Q = 20160 ∨ Nat.card Q = 979200 ∨ Nat.card Q = 9999360) :
    ¬ ClassicalGroup.IsPSL Q 2 q := by
  intro h
  have ho := (psl_order h).2
  rcases hc with hc | hc | hc | hc | hc | hc
  · rw [hc] at ho
    obtain ⟨hl, hu⟩ := psl_parameter_bounds (a := 11) (b := 12) ho (by decide) (by decide)
    interval_cases q <;> norm_num at ho
  · rw [hc] at ho
    obtain ⟨hl, hu⟩ := psl_parameter_bounds (a := 14) (b := 17) ho (by decide) (by decide)
    interval_cases q <;> norm_num at ho
  · rw [hc] at ho
    obtain ⟨hl, hu⟩ := psl_parameter_bounds (a := 19) (b := 22) ho (by decide) (by decide)
    interval_cases q <;> norm_num at ho
  · rw [hc] at ho
    obtain ⟨hl, hu⟩ := psl_parameter_bounds (a := 28) (b := 34) ho (by decide) (by decide)
    interval_cases q <;> norm_num at ho
  · rw [hc] at ho
    obtain ⟨hl, hu⟩ := psl_parameter_bounds (a := 100) (b := 125) ho (by decide) (by decide)
    interval_cases q <;> norm_num at ho
  · rw [hc] at ho
    obtain ⟨hl, hu⟩ := psl_parameter_bounds (a := 216) (b := 271) ho (by decide) (by decide)
    interval_cases q <;> norm_num at ho

/-- The composite odd field order nine is excluded by both swapped alternatives. -/
theorem not_swapped_of_card_360 (hc : Nat.card Q = 360) :
    ¬ Chapter1.XiEmbedding.SwappedModel 3 Q := by
  rintro (⟨n, _, _, he⟩ | ⟨p, hp, _, he⟩)
  · have hn := psl_parameter_of_card_360 hc he
    have hn0 : n ≠ 0 := by rintro rfl; norm_num at hn
    have hev := (by decide : Even 2).pow_of_ne_zero hn0
    rw [hn] at hev
    norm_num at hev
  · have heq := psl_parameter_of_card_360 hc he
    norm_num [heq] at hp

/-- Order exclusions apply to the actual quotient in the swapped embedding. -/
theorem not_swapped_of_exceptional_order
    (hc : Nat.card Q = 1080 ∨ Nat.card Q = 2520 ∨ Nat.card Q = 6048 ∨
      Nat.card Q = 20160 ∨ Nat.card Q = 979200 ∨ Nat.card Q = 9999360) :
    ¬ Chapter1.XiEmbedding.SwappedModel 3 Q := by
  rintro (⟨_, _, _, he⟩ | ⟨_, _, _, he⟩)
  · exact not_psl_of_exceptional_order hc he
  · exact not_psl_of_exceptional_order hc he

/-- Among the four alternating quotients in C.2.7(3)(b), only A₅ survives. -/
theorem alternating_degree {n : ℕ} (hn : 5 ≤ n) (hn' : n ≤ 8)
    (he : Nonempty (Q ≃* alternatingGroup (Fin n)))
    (hs : Chapter1.XiEmbedding.SwappedModel 3 Q) : n = 5 := by
  obtain ⟨e⟩ := he
  have hc : Nat.card Q = n.factorial / 2 := by
    let : NeZero n := ⟨by omega⟩
    have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr (by omega)
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
  interval_cases n
  · rfl
  · exact False.elim (not_swapped_of_card_360 (by norm_num at hc ⊢; exact hc) hs)
  · exact False.elim (not_swapped_of_exceptional_order (Or.inr (Or.inl
      (by norm_num at hc ⊢; exact hc))) hs)
  · exact False.elim (not_swapped_of_exceptional_order (Or.inr (Or.inr (Or.inr
      (Or.inl (by norm_num at hc ⊢; exact hc))))) hs)

/-- All ordinary alternating block alternatives are checked on their actual quotient. -/
theorem alternatingBlock_degree {L : Type*} [Group L] {n : ℕ}
    (hn : 5 ≤ n) (hn' : n ≤ 8) (hb : ChapterC.IsAlternatingBlock L n)
    (hs : Chapter1.XiEmbedding.SwappedModel 3 (L ⧸ pCore 2 L)) : n = 5 :=
  alternating_degree hn hn' hb.2.2.quotient_iso hs

/-- The exceptional four-dimensional A₇ module still has the excluded A₇ quotient. -/
theorem not_exceptionalA7Block {L : Type*} [Group L]
    (hs : Chapter1.XiEmbedding.SwappedModel 3 (L ⧸ pCore 2 L)) :
    ¬ ChapterC.IsExceptionalA7Block L := by
  intro hb
  have he := alternating_degree (by decide) (by decide) hb.2.1 hs
  norm_num at he

/-- The full triple cover, rather than A₆ itself, has order 1080. -/
theorem not_exceptionalAhat6Block {L : Type*} [Group L]
    (hs : Chapter1.XiEmbedding.SwappedModel 3 (L ⧸ pCore 2 L)) :
    ¬ ChapterC.IsExceptionalAhat6Block L := by
  intro hb
  obtain ⟨e⟩ := hb.2.2.2.1
  have hc := Subgroup.card_eq_card_quotient_mul_card_subgroup
    (Subgroup.center (L ⧸ pCore 2 L))
  rw [Nat.card_congr e.toEquiv, hb.2.2.1, nat_card_alternatingGroup,
    Nat.card_fin] at hc
  exact not_swapped_of_exceptional_order (Or.inl (by norm_num at hc ⊢; exact hc)) hs

/-- Both binary-linear alternatives use their actual projective matrix models. -/
theorem not_binaryLinear_quotient {n : ℕ} (hn : n = 4 ∨ n = 5)
    (hs : Chapter1.XiEmbedding.SwappedModel 3 Q) : ¬ ClassicalGroup.IsPSL Q n 2 := by
  rintro ⟨F, _, _, hF, ⟨e⟩⟩
  rcases hn with rfl | rfl
  · have hc := Atlas.ExceptionalSupport.card_psl_mul (F := F) 4
    rw [← Nat.card_congr e.toEquiv, hF] at hc
    norm_num [Fin.prod_univ_succ] at hc
    exact not_swapped_of_exceptional_order (Or.inr (Or.inr (Or.inr (Or.inl hc)))) hs
  · have hc := Atlas.ExceptionalSupport.card_psl_mul (F := F) 5
    rw [← Nat.card_congr e.toEquiv, hF] at hc
    norm_num [Fin.prod_univ_succ] at hc
    exact not_swapped_of_exceptional_order (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hc))))) hs

/-- The full Sp₄(4) natural block is excluded, without replacing its model by a tag. -/
theorem not_sp4FourBlock {L : Type*} [Group L]
    (hs : Chapter1.XiEmbedding.SwappedModel 3 (L ⧸ pCore 2 L)) :
    ¬ ChapterC.IsSp4FourBlock L := by
  rintro ⟨_, F, _, _, hF, rho, ⟨model⟩, _⟩
  have hc : Nat.card (L ⧸ pCore 2 L) = 979200 := by
    rw [Nat.card_congr model.quotientIso.toEquiv,
      Theory.SpecificGroups.SymplecticFour.card_sp F, hF]
    norm_num
  exact not_swapped_of_exceptional_order (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hc))))) hs
end CFSG.Quasithin.Chapter15.Section04.LocalSetup.CoreElimination.BlockSieve.ExchangedCases
