module

public import Mathlib.GroupTheory.Sylow

/-!
# Prime-order centralizers and Sylow subgroups

If `p²` divides a finite group order, it divides the centralizer order of
every element of order `p`. Indeed, a centralizer of order at most `p` in
a Sylow subgroup would equal its nontrivial center, forcing that Sylow
subgroup itself to have order `p`.

Consequently, one element with centralizer order indivisible by `p²`
forces every Sylow `p`-subgroup to have order `p`. Sylow conjugacy then
moves every element of order `p` into any subgroup containing one such
element. This supplies the Sylow and localization steps in Bender,
*Finite groups with large subgroups* (1974), (4.1)–(4.2).
-/

namespace Subgroup

variable {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

/-- A prime-order element has a centralizer divisible by `p²` whenever
the ambient group order is divisible by `p²`. -/
public theorem prime_sq_dvd_card_centralizer
    (hG : p ^ 2 ∣ Nat.card G) (x : G) (hx : orderOf x = p) :
    p ^ 2 ∣ Nat.card (centralizer ({x} : Set G)) := by
  by_contra hsmall
  have hp := Fact.out (p := p.Prime)
  have hcyc : IsPGroup p (zpowers x) := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers, hx, pow_one])
  obtain ⟨Q, hQ⟩ := hcyc.exists_le_sylow
  let q : Q := ⟨x, hQ (mem_zpowers x)⟩
  let D := centralizer ({q} : Set Q)
  have hD : Nat.card D ∣ p := by
    have hmap : D.map (Q : Subgroup G).subtype ≤ centralizer ({x} : Set G) := by
      rintro a ⟨b, hb, rfl⟩
      exact mem_centralizer_singleton_iff.mpr
        (congrArg Subtype.val (mem_centralizer_singleton_iff.mp hb))
    have hd := card_dvd_of_le hmap
    rw [card_map_of_injective (Q : Subgroup G).subtype_injective] at hd
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp (Q.isPGroup'.to_subgroup D)
    have hnlt : n < 2 := by
      by_contra hnlt
      apply hsmall
      apply dvd_trans _ hd
      rw [hn]
      exact Nat.pow_dvd_pow p (by omega : 2 ≤ n)
    rw [hn]
    simpa using Nat.pow_dvd_pow p (by omega : n ≤ 1)
  have hpQ : p ^ 2 ∣ Nat.card Q := Q.pow_dvd_card_of_pow_dvd_card hG
  have hp2 : 1 < p ^ 2 := one_lt_pow₀ hp.one_lt (by decide)
  let : Nontrivial Q := Finite.one_lt_card_iff_nontrivial.mp
    (hp2.trans_le (Nat.le_of_dvd Nat.card_pos hpQ))
  let : Nontrivial (center Q) := Q.isPGroup'.center_nontrivial
  have hZD : center Q ≤ D := by
    intro a ha
    exact mem_centralizer_singleton_iff.mpr (mem_center_iff.mp ha q).symm
  have hZcard : Nat.card (center Q) = p := by
    rcases hp.eq_one_or_self_of_dvd _ ((card_dvd_of_le hZD).trans hD) with h | h
    · have := Finite.one_lt_card (α := center Q)
      omega
    · exact h
  have hZD' : center Q = D := eq_of_le_of_card_ge hZD (by
    rw [hZcard]
    exact Nat.le_of_dvd hp.pos hD)
  have hqZ : q ∈ center Q := hZD' ▸ mem_centralizer_singleton_iff.mpr rfl
  have hDtop : D = ⊤ := by
    apply top_unique
    intro a _
    exact mem_centralizer_singleton_iff.mpr (mem_center_iff.mp hqZ a)
  rw [hDtop, card_top] at hD
  have hle := Nat.le_of_dvd hp.pos (hpQ.trans hD)
  nlinarith [hp.two_le]

/-- One prime-order element whose centralizer has only one factor of `p`
determines the order of every ambient Sylow `p`-subgroup. -/
public theorem sylow_card_eq_prime_of_centralizer
    (x : G) (hx : orderOf x = p)
    (hC : ¬ p ^ 2 ∣ Nat.card (centralizer ({x} : Set G)))
    (P : Sylow p G) : Nat.card P = p := by
  have hp := Fact.out (p := p.Prime)
  have hG : ¬ p ^ 2 ∣ Nat.card G :=
    fun hG => hC (prime_sq_dvd_card_centralizer hG x hx)
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp P.isPGroup'
  have hnlt : n < 2 := by
    by_contra hnlt
    apply hG
    apply dvd_trans _ (P : Subgroup G).card_subgroup_dvd_card
    rw [hn]
    exact Nat.pow_dvd_pow p (by omega)
  have hpP : p ∣ Nat.card P := by
    simpa only [pow_one] using P.pow_dvd_card_of_pow_dvd_card (n := 1)
      (by simpa only [pow_one, ← hx] using _root_.orderOf_dvd_natCard x)
  have hn0 : n ≠ 0 := by
    intro hz
    rw [hn, hz, pow_zero] at hpP
    exact hp.not_dvd_one hpP
  have hn1 : n = 1 := by omega
  simpa only [hn1, pow_one] using hn

/-- When the Sylow subgroups have prime order, every element of that order
is conjugate into any subgroup containing one element of that order. -/
public theorem exists_conj_mem_of_sylow_card_eq_prime
    (H : Subgroup G) (x₀ : G) (hx₀H : x₀ ∈ H) (hx₀ : orderOf x₀ = p)
    (hP : ∀ P : Sylow p G, Nat.card P = p)
    (x : G) (hx : orderOf x = p) :
    ∃ g : G, g * x * g⁻¹ ∈ H := by
  have hp₀ : IsPGroup p (zpowers x₀) := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers, hx₀, pow_one])
  have hpx : IsPGroup p (zpowers x) := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers, hx, pow_one])
  obtain ⟨P, h₀P⟩ := hp₀.exists_le_sylow
  obtain ⟨Q, hxQ⟩ := hpx.exists_le_sylow
  have hP₀ : (P : Subgroup G) = zpowers x₀ :=
    (eq_of_le_of_card_ge h₀P (by rw [hP P, Nat.card_zpowers, hx₀])).symm
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G Q P
  have hmem : g * x * g⁻¹ ∈ (P : Subgroup G) := by
    rw [← hg]
    exact ⟨x, hxQ (mem_zpowers x), rfl⟩
  rw [hP₀] at hmem
  exact ⟨g, (zpowers_le.mpr hx₀H) hmem⟩

end Subgroup
