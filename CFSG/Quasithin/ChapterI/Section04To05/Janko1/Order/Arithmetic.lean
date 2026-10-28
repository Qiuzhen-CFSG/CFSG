module
public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Order.CountingData

/-!
# The final arithmetic of Bender's J₁ order calculation

The source inequalities and congruence leave `(d,m) = (1,2), (3,0), (3,5)`.
The already proved class-size identity gives candidate group orders 61320,
74760, and 175560. In the first two cases the number of Sylow 73- or
89-subgroups divides 840 and is one modulo that prime, hence equals one.
Their normality contradicts ambient simplicity. This uses the original
I.4.9 simplicity hypothesis to shorten Bender's final exclusions.

`card_eq_of_bender_counts` remains explicitly conditional on (4.4)–(4.6).
Its premise must be constructed by the coset-distribution branch.
Source: Bender, *Finite groups with large subgroups* (1974), pp.227–228.
-/

open Subgroup
namespace CFSG.Quasithin.Janko1CentralizerData

private theorem simple_card_ne_prime_multiple
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (p : ℕ) (hp : p.Prime) (hcop : p.Coprime 840)
    (harith : ∀ n ∈ (840 : ℕ).divisors, n % p = 1 → n = 1) :
    Nat.card G ≠ 840 * p := by
  intro hcard
  let _ : Fact p.Prime := ⟨hp⟩
  let P : Sylow p G := Classical.choice inferInstance
  have hpd : p ∣ Nat.card G := by rw [hcard]; exact dvd_mul_left p 840
  have hpc : p ∣ Nat.card P := P.dvd_card_of_dvd_card hpd
  have hP : Nat.card P = p := by
    obtain ⟨k, hk⟩ := P.isPGroup'.exists_card_eq
    have hcop' : (Nat.card P).Coprime 840 := hk ▸ hcop.pow_left k
    have hd := (P : Subgroup G).card_subgroup_dvd_card
    rw [hcard] at hd
    exact Nat.dvd_antisymm (hcop'.dvd_of_dvd_mul_left hd) hpc
  have hi : (P : Subgroup G).index = 840 := by
    have he := (P : Subgroup G).card_mul_index
    rw [hP, hcard, Nat.mul_comm 840 p] at he
    exact Nat.eq_of_mul_eq_mul_left hp.pos he
  have hn : Nat.card (Sylow p G) = 1 := by
    apply harith
    · exact Nat.mem_divisors.mpr ⟨hi ▸ P.card_dvd_index, by decide⟩
    · have hm := card_sylow_modEq_one p G
      change Nat.card (Sylow p G) % p = 1 % p at hm
      rwa [Nat.mod_eq_of_lt hp.one_lt] at hm
  let _ : Subsingleton (Sylow p G) := (Nat.card_eq_one_iff_unique.mp hn).1
  have hnormal : (P : Subgroup G).Normal := P.normal_of_subsingleton
  rcases hnormal.eq_bot_or_eq_top with hb | ht
  · have he : Nat.card P = 1 := by rw [hb, card_bot]
    have := hp.two_le
    omega
  · have he : Nat.card P = Nat.card G := by rw [ht, card_top]
    rw [hP, hcard] at he
    have := hp.pos
    omega

/-- Sylow counting excludes the first unwanted order in a finite simple group. -/
public theorem simple_card_ne_61320
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G] : Nat.card G ≠ 61320 := by
  exact simple_card_ne_prime_multiple 73 (by decide) (by decide) (by decide +kernel)

/-- Sylow counting excludes the second unwanted order in a finite simple group. -/
public theorem simple_card_ne_74760
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G] : Nat.card G ≠ 74760 := by
  exact simple_card_ne_prime_multiple 89 (by decide) (by decide) (by decide +kernel)

/-- The remaining order assembly, conditional on the explicit source count. -/
public theorem card_eq_of_bender_counts
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (h : Janko1CentralizerData G) {d : ℕ} (hd : d = 1 ∨ d = 3)
    (c : BenderCountData G d) : Nat.card G = 175560 := by
  have hb := c.m_le
  have he := c.e_le_one
  have hc := c.congruence
  have hcount := c.involutions
  have horder := h.card_eq_involution_count_mul
  have hcases : (d = 1 ∧ c.m = 2) ∨ (d = 3 ∧ c.m = 0) ∨ (d = 3 ∧ c.m = 5) := by
    rcases hd with hd | hd <;> omega
  rcases hcases with ⟨rfl, hm⟩ | ⟨rfl, hm⟩ | ⟨rfl, hm⟩
  · rw [hm] at hcount
    norm_num at hcount
    rw [hcount] at horder
    exact (simple_card_ne_61320 (G := G) horder).elim
  · rw [hm] at hcount
    norm_num at hcount
    rw [hcount] at horder
    exact (simple_card_ne_74760 (G := G) horder).elim
  · rw [hm] at hcount
    norm_num at hcount
    simpa only [hcount] using horder

end CFSG.Quasithin.Janko1CentralizerData
