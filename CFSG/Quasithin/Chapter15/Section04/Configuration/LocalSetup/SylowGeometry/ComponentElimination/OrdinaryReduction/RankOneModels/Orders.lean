module

public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.ComponentElimination.OrdinaryReduction.Inputs
public import Theory.AtlasPort.ExceptionalIsomorphisms.Support

/-!
# Small-order exclusions for the ordinary rank-one comparison

The actual projective matrix model gives |PSL₂(q)| gcd(2,q−1) = q(q²−1).
Bounding this increasing numerator leaves finite arithmetic checks for the
orders of A₆, A₇, PSL₃(3), and PSL₃(4). Order 360 forces q = 9, which
is neither an odd prime nor a power of two. These are exclusions, not
recognition of an abstract group from its order.

Source: Aschbacher–Smith, proof of 15.4.20, printed p.1164, comparing
1.1.5(3), pp.501–503. The matrix order formula and its ATLAS attribution
are in `Theory.AtlasPort.ExceptionalIsomorphisms.Support`.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.ComponentElimination.OrdinaryReduction.RankOneModels
variable {L : Type*} [Group L]

/-- The fraction-free order identity for the given projective model. -/
theorem psl_two_card_mul {q : ℕ} (h : ClassicalGroup.IsPSL L 2 q) :
    Nat.card L * Nat.gcd 2 (q - 1) = q * (q ^ 2 - 1) := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := h
  have hq : 1 < q := hF ▸ (Finite.one_lt_card (α := F))
  have hc := Atlas.ExceptionalSupport.card_psl_mul (F := F) 2
  rw [← Nat.card_congr e.toEquiv, hF] at hc
  simp only [Fin.prod_univ_two, Fin.val_zero, Fin.val_one, pow_zero, pow_one] at hc
  have hsub : q ^ 2 - q = q * (q - 1) := by
    rw [Nat.mul_sub_left_distrib, mul_one, pow_two]
  rw [hsub] at hc
  apply Nat.eq_of_mul_eq_mul_right (show 0 < q - 1 by omega)
  calc
    _ = (q ^ 2 - 1) * (q * (q - 1)) := hc
    _ = _ := by ring

private theorem parameter_lt_of_card {q c N : ℕ}
    (hm : ClassicalGroup.IsPSL L 2 q) (hc : Nat.card L = c)
    (hN : 2 * c < N * (N ^ 2 - 1)) : q < N := by
  have h := psl_two_card_mul hm
  rw [hc] at h
  have hbound : q * (q ^ 2 - 1) ≤ 2 * c := by
    rw [← h, mul_comm 2 c]
    exact Nat.mul_le_mul_left c (Nat.gcd_le_left _ (by decide))
  by_contra hq
  have hNq : N ≤ q := by omega
  have hmono := Nat.mul_le_mul hNq
    (Nat.sub_le_sub_right (Nat.pow_le_pow_left hNq 2) 1)
  omega

/-- Order 360 in the rank-two projective family forces field order nine. -/
theorem parameter_nine_of_card_360 {q : ℕ} (hm : ClassicalGroup.IsPSL L 2 q)
    (hc : Nat.card L = 360) : q = 9 := by
  have hq := parameter_lt_of_card hm hc (N := 10) (by decide)
  have h := psl_two_card_mul hm
  rw [hc] at h
  interval_cases q <;> norm_num at *

/-- No degree-two projective group has the order of A₇. -/
theorem psl_two_card_ne_2520 {q : ℕ} (hm : ClassicalGroup.IsPSL L 2 q) :
    Nat.card L ≠ 2520 := by
  intro hc
  have hq := parameter_lt_of_card hm hc (N := 18) (by decide)
  have h := psl_two_card_mul hm
  rw [hc] at h
  interval_cases q <;> norm_num at h

/-- No degree-two projective group has the order of PSL₃(3). -/
theorem psl_two_card_ne_5616 {q : ℕ} (hm : ClassicalGroup.IsPSL L 2 q) :
    Nat.card L ≠ 5616 := by
  intro hc
  have hq := parameter_lt_of_card hm hc (N := 23) (by decide)
  have h := psl_two_card_mul hm
  rw [hc] at h
  interval_cases q <;> norm_num at h

/-- No degree-two projective group has the order of PSL₃(4). -/
theorem psl_two_card_ne_20160 {q : ℕ} (hm : ClassicalGroup.IsPSL L 2 q) :
    Nat.card L ≠ 20160 := by
  intro hc
  have hq := parameter_lt_of_card hm hc (N := 35) (by decide)
  have h := psl_two_card_mul hm
  rw [hc] at h
  interval_cases q <;> norm_num at h

/-- The source rank-one quotient cannot have the order of A₆. -/
theorem quotient_card_ne_360 (hm : RankOneQuotientModel L) :
    Nat.card (L ⧸ pCore 2 L) ≠ 360 := by
  intro hc
  rcases hm with ⟨n, _, hm⟩ | ⟨p, hp, _, hm⟩
  · have hn := parameter_nine_of_card_360 hm hc
    have hn0 : n ≠ 0 := by intro he; simp [he] at hn
    have hd : 2 ∣ 2 ^ n := dvd_pow_self 2 hn0
    rw [hn] at hd
    norm_num at hd
  · have hp9 := parameter_nine_of_card_360 hm hc
    rw [hp9] at hp
    norm_num at hp

/-- The source rank-one quotient cannot have the order of A₇. -/
theorem quotient_card_ne_2520 (hm : RankOneQuotientModel L) :
    Nat.card (L ⧸ pCore 2 L) ≠ 2520 := by
  rcases hm with ⟨_, _, hm⟩ | ⟨_, _, _, hm⟩
  · exact psl_two_card_ne_2520 hm
  · exact psl_two_card_ne_2520 hm

/-- A card exclusion using the two possible denominators in the PSL₂ order formula. -/
theorem psl_two_card_ne_of_gaps {q c a b : ℕ} (hm : ClassicalGroup.IsPSL L 2 q)
    (ha : a * (a ^ 2 - 1) < c) (ha' : c < (a+1)*((a+1)^2-1))
    (hb : b * (b ^ 2 - 1) < 2*c) (hb' : 2*c < (b+1)*((b+1)^2-1)) :
    Nat.card L ≠ c := by
  intro hc
  have h := psl_two_card_mul hm
  rw [hc] at h
  have he : Nat.gcd 2 (q-1) = 1 ∨ Nat.gcd 2 (q-1) = 2 := by
    have hp := Nat.gcd_pos_of_pos_left (q-1) (by decide : 0 < 2)
    have hl := Nat.gcd_le_left (q-1) (by decide : 0 < 2)
    omega
  have gap (a c : ℕ) (hlo : a*(a^2-1) < c) (hhi : c < (a+1)*((a+1)^2-1)) :
      q*(q^2-1) ≠ c := by
    intro heq
    by_cases hqa : q ≤ a
    · have hh := Nat.mul_le_mul hqa
        (Nat.sub_le_sub_right (Nat.pow_le_pow_left hqa 2) 1)
      omega
    · have hqa : a+1 ≤ q := by omega
      have hh := Nat.mul_le_mul hqa
        (Nat.sub_le_sub_right (Nat.pow_le_pow_left hqa 2) 1)
      omega
  rcases he with he | he
  · rw [he, mul_one] at h
    exact gap a c ha ha' h.symm
  · rw [he, mul_comm c 2] at h
    exact gap b (2*c) hb hb' h.symm

/-- Two odd field parameters on the same actual PSL₂ model are equal. -/
theorem odd_parameter_unique {p q : ℕ} (hp : Odd p) (hq : Odd q)
    (hmp : ClassicalGroup.IsPSL L 2 p) (hmq : ClassicalGroup.IsPSL L 2 q) : p = q := by
  have hp1 : 1 < p := by obtain ⟨F,_,_,hF,_⟩ := hmp; exact hF ▸ Finite.one_lt_card
  have hq1 : 1 < q := by obtain ⟨F,_,_,hF,_⟩ := hmq; exact hF ▸ Finite.one_lt_card
  have hg (p : ℕ) (hp : Odd p) : Nat.gcd 2 (p-1) = 2 :=
    Nat.gcd_eq_left (even_iff_two_dvd.mp (hp.tsub_odd odd_one))
  have he : p*(p^2-1) = q*(q^2-1) := by
    rw [← psl_two_card_mul hmp, ← psl_two_card_mul hmq, hg p hp, hg q hq]
  have ps : p^2 - 1 + 1 = p^2 := Nat.sub_add_cancel (by nlinarith)
  have qs : q^2 - 1 + 1 = q^2 := Nat.sub_add_cancel (by nlinarith)
  rcases lt_trichotomy p q with hl | hl | hl
  · have hh := Nat.mul_lt_mul_of_lt_of_lt hl
      (show p^2-1 < q^2-1 by nlinarith)
    omega
  · exact hl
  · have hh := Nat.mul_lt_mul_of_lt_of_lt hl
      (show q^2-1 < p^2-1 by nlinarith)
    omega


end CFSG.Quasithin.Chapter15.Section04.LocalSetup.ComponentElimination.OrdinaryReduction.RankOneModels
