module

public import CFSG.Quasithin.ChapterI.Section04To05.G2Recognition.SylowNineLocal
public import Theory.GroupTheory.ElementaryNormalizerThreeRank

/-!
# Sylow exclusions for the character-theoretic order candidates

In the Sylow-nine branch, the centralizers of involutions and cubic elements
have order dividing 576. A subgroup of prime order greater than three therefore
has centralizer of order prime to six. Its normalizer acts on a cyclic group,
so its additional prime factors divide p - 1. The Sylow congruences then exclude
the three orders left by the character arithmetic.

These are exclusions from the original local configuration; no character
table or block structure is assumed.
-/

public section
set_option maxRecDepth 100000
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterI.Section04To05.G2Recognition
open Chapter14.Section04.DimensionFour
variable {G : Type*} [Group G] [Finite G] (c : G2ThreeConfiguration G)

include c in
private theorem cubic_centralizer_card_dvd
    (hsmall : ¬ 3 ^ 3 ∣ Nat.card G) (u : G) (hu : orderOf u = 3) :
    Nat.card (centralizer ({u} : Set G)) ∣ 576 := by
  obtain ⟨t⟩ := exists_cubic_torus c
  obtain ⟨P, hP⟩ := t.cubic_plane_sylow_iff.mpr
    (t.small_cores_iff_not_cube_dvd.mpr hsmall)
  obtain ⟨v, hv⟩ := P.exists_isConj_of_orderOf_eq_prime_pow (n := 1)
    (by simpa using hu)
  obtain ⟨g, hg⟩ := isConj_iff.mp hv
  change MulAut.conj g u = (v : G) at hg
  have hv3 : orderOf (v : G) = 3 := by
    rw [← hg, (MulAut.conj g).orderOf_eq, hu]
  have hle : (centralizer ({u} : Set G)).map (MulAut.conj g).toMonoidHom ≤ c.H := by
    rintro _ ⟨a, ha, rfl⟩
    apply t.plane_cubic_centralizer_le_H_of_sylow ⟨P, hP⟩ (v : G)
      hv3
      (hP ▸ v.property)
    apply mem_centralizer_singleton_iff.mpr
    simpa only [MulEquiv.coe_toMonoidHom, map_mul, hg] using congrArg (MulAut.conj g)
      (mem_centralizer_singleton_iff.mp ha)
  have hd := card_dvd_of_le hle
  rwa [card_map_of_injective (MulAut.conj g).injective, H_card c] at hd

include c in
private theorem prime_centralizer_prime_to_six
    (hsmall : ¬ 3 ^ 3 ∣ Nat.card G) {p : ℕ} (A : Subgroup G)
    (hA : Nat.card A = p) (hp : ¬ p ∣ 576) :
    ¬ 2 ∣ Nat.card (centralizer (A : Set G)) ∧
      ¬ 3 ∣ Nat.card (centralizer (A : Set G)) := by
  have bound (q : ℕ) [Fact q.Prime]
      (hc : ∀ u : G, orderOf u = q → Nat.card (centralizer ({u} : Set G)) ∣ 576) :
      ¬ q ∣ Nat.card (centralizer (A : Set G)) := by
    intro hd
    obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' (G := centralizer (A : Set G)) q hd
    have hle : A ≤ centralizer ({(u : G)} : Set G) := by
      intro a ha
      exact mem_centralizer_singleton_iff.mpr (u.property a ha)
    apply hp
    rw [← hA]
    exact (card_dvd_of_le hle).trans
      (hc u ((orderOf_coe u).trans hu))
  exact ⟨bound 2 (fun u hu => (involution_centralizer_card c u hu) ▸ dvd_rfl),
    bound 3 (cubic_centralizer_card_dvd c hsmall)⟩

private theorem prime_sylow_card {p m : ℕ} [Fact p.Prime]
    (hG : Nat.card G = p * m) (hcop : Nat.Coprime p m) (P : Sylow p G) :
    Nat.card P = p := by
  have hp := P.dvd_card_of_dvd_card (hG ▸ dvd_mul_right p m)
  obtain ⟨n, hn⟩ := P.isPGroup'.exists_card_eq
  have hc : Nat.Coprime (Nat.card P) m := hn ▸ hcop.pow_left n
  exact Nat.dvd_antisymm
    (hc.dvd_of_dvd_mul_left (by simpa only [hG, Nat.mul_comm] using
      (P : Subgroup G).card_subgroup_dvd_card)) hp

private theorem sylow_count_data {p m : ℕ} [Fact p.Prime]
    (hG : Nat.card G = p * m) (hP : Nat.card (default : Sylow p G) = p) :
    let P : Sylow p G := default
    let n := Nat.card (Sylow p G)
    n ∣ m ∧ n % p = 1 % p ∧
      Nat.card (normalizer ((P : Subgroup G) : Set G)) * n = p * m := by
  let P : Sylow p G := default
  have hi : P.index = m := by
    have hh := (P : Subgroup G).card_mul_index
    rw [hP, hG] at hh
    exact Nat.eq_of_mul_eq_mul_left (Fact.out : p.Prime).pos hh
  refine ⟨hi ▸ P.card_dvd_index, card_sylow_modEq_one p G, ?_⟩
  rw [Sylow.card_eq_index_normalizer P]
  exact (normalizer ((P : Subgroup G) : Set G)).card_mul_index.trans hG

private theorem normalizer_card_dvd {p : ℕ} [Fact p.Prime]
    (A : Subgroup G) (hA : Nat.card A = p) :
    Nat.card (normalizer (A : Set G)) ∣ Nat.card (centralizer (A : Set G)) * (p - 1) := by
  let : IsCyclic A := isCyclic_of_prime_card hA
  simpa only [IsCyclic.card_mulAut, hA, Nat.totient_prime (Fact.out : p.Prime)] using
    A.card_normalizer_dvd_card_centralizer_mul_card_mulAut

private theorem divisor_split {n a b : ℕ} (h : n ∣ a * b)
    (ha : a ≠ 0) (hb : b ≠ 0) :
    ∃ x ∈ Nat.divisors a, ∃ y ∈ Nat.divisors b, n = x * y := by
  obtain ⟨x, y, hx, hy, hxy⟩ := exists_dvd_and_dvd_of_dvd_mul h
  exact ⟨x, Nat.mem_divisors.mpr ⟨hx, ha⟩, y, Nat.mem_divisors.mpr ⟨hy, hb⟩, hxy⟩

include c in
/-- The 280/281 character-degree candidate is incompatible with the
original involution centralizers and the Sylow congruence at 281. -/
theorem card_ne_5664960_of_sylow_nine
    (hsmall : ¬ 3 ^ 3 ∣ Nat.card G) : Nat.card G ≠ 5664960 := by
  intro hG
  let : Fact (Nat.Prime 281) := ⟨by decide⟩
  let P : Sylow 281 G := default
  have hG' : Nat.card G = 281 * 20160 := by omega
  have hP : Nat.card P = 281 := prime_sylow_card hG' (by decide) P
  obtain ⟨hn, hm, he⟩ := sylow_count_data hG' hP
  change Nat.card (normalizer ((P : Subgroup G) : Set G)) * Nat.card (Sylow 281 G) = 281 * 20160 at he
  have hcount : Nat.card (Sylow 281 G) = 1 := by
    obtain ⟨a, ha, b, hb, hab⟩ := divisor_split
      (show Nat.card (Sylow 281 G) ∣ 64 * 315 by simpa using hn) (by decide) (by decide)
    have hf : ∀ a ∈ Nat.divisors 64, ∀ b ∈ Nat.divisors 315,
        (a * b) % 281 = 1 → a * b = 1 := by decide +kernel
    rw [hab]
    exact hf a ha b hb (by simpa only [hab] using hm)
  have hN : Nat.card (normalizer ((P : Subgroup G) : Set G)) = 5664960 := by simpa [hcount] using he
  have hodd := (prime_centralizer_prime_to_six c hsmall (P : Subgroup G) hP (by decide)).1
  have hd := normalizer_card_dvd (P : Subgroup G) hP
  rw [hN] at hd
  have h16 : 16 ∣ Nat.card (centralizer ((P : Subgroup G) : Set G)) * 280 := (by decide : 16 ∣ 5664960).trans hd
  omega

include c in
/-- The 133/134 character-degree candidate forces a Sylow 67-normalizer
with too large a two-part for its cyclic automorphism group. -/
theorem card_ne_5132736_of_sylow_nine
    (hsmall : ¬ 3 ^ 3 ∣ Nat.card G) : Nat.card G ≠ 5132736 := by
  intro hG
  let : Fact (Nat.Prime 67) := ⟨by decide⟩
  let P : Sylow 67 G := default
  have hG' : Nat.card G = 67 * 76608 := by omega
  have hP : Nat.card P = 67 := prime_sylow_card hG' (by decide) P
  obtain ⟨hn, hm, he⟩ := sylow_count_data hG' hP
  change Nat.card (normalizer ((P : Subgroup G) : Set G)) * Nat.card (Sylow 67 G) = 67 * 76608 at he
  have hcount : Nat.card (Sylow 67 G) = 1 ∨ Nat.card (Sylow 67 G) = 336 := by
    obtain ⟨a, ha, b, hb, hab⟩ := divisor_split
      (show Nat.card (Sylow 67 G) ∣ 64 * 1197 by simpa using hn) (by decide) (by decide)
    have hf : ∀ a ∈ Nat.divisors 64, ∀ b ∈ Nat.divisors 1197,
        (a * b) % 67 = 1 → a * b = 1 ∨ a * b = 336 := by decide +kernel
    rw [hab]
    exact hf a ha b hb (by simpa only [hab] using hm)
  have hfour : 4 ∣ Nat.card (normalizer ((P : Subgroup G) : Set G)) := by
    rcases hcount with h | h <;> rw [h] at he <;> omega
  have hodd := (prime_centralizer_prime_to_six c hsmall (P : Subgroup G) hP (by decide)).1
  have hd := hfour.trans (normalizer_card_dvd (P : Subgroup G) hP)
  norm_num only [Nat.reduceSub] at hd
  omega

include c in
/-- The 154/155 character-degree candidate has no possible Sylow
11-normalizer: every Sylow congruence solution has a factor three or four. -/
theorem card_ne_6874560_of_sylow_nine
    (hsmall : ¬ 3 ^ 3 ∣ Nat.card G) : Nat.card G ≠ 6874560 := by
  intro hG
  let : Fact (Nat.Prime 11) := ⟨by decide⟩
  let P : Sylow 11 G := default
  have hG' : Nat.card G = 11 * 624960 := by omega
  have hP : Nat.card P = 11 := prime_sylow_card hG' (by decide) P
  obtain ⟨hn, hm, he⟩ := sylow_count_data hG' hP
  change Nat.card (normalizer ((P : Subgroup G) : Set G)) * Nat.card (Sylow 11 G) = 11 * 624960 at he
  have hbad : 3 ∣ Nat.card (normalizer ((P : Subgroup G) : Set G)) ∨
      4 ∣ Nat.card (normalizer ((P : Subgroup G) : Set G)) := by
    obtain ⟨a, ha, b, hb, hab⟩ := divisor_split
      (show Nat.card (Sylow 11 G) ∣ 64 * 9765 by simpa using hn) (by decide) (by decide)
    obtain ⟨d, hd, f, hf, hdf⟩ := divisor_split
      (show b ∣ 9 * 1085 from Nat.dvd_of_mem_divisors hb) (by decide) (by decide)
    have hcert : ∀ a ∈ Nat.divisors 64, ∀ d ∈ Nat.divisors 9,
        ∀ f ∈ Nat.divisors 1085, (a * (d * f)) % 11 = 1 →
        3 ∣ 6874560 / (a * (d * f)) ∨ 4 ∣ 6874560 / (a * (d * f)) := by decide +kernel
    have hh := hcert a ha d hd f hf (by simpa only [hab, hdf] using hm)
    have hnpos : 0 < Nat.card (Sylow 11 G) := Nat.card_pos
    have hquot : 6874560 / Nat.card (Sylow 11 G) = Nat.card (normalizer ((P : Subgroup G) : Set G)) := by
      norm_num only [Nat.reduceMul] at he
      rw [← he, Nat.mul_div_cancel _ hnpos]
    rw [← hdf, ← hab, hquot] at hh
    exact hh
  obtain ⟨h2, h3⟩ := prime_centralizer_prime_to_six c hsmall (P : Subgroup G) hP (by decide)
  have hd := normalizer_card_dvd (P : Subgroup G) hP
  norm_num only [Nat.reduceSub] at hd
  rcases hbad with hb | hb
  · have hh := hb.trans hd
    omega
  · have hh := hb.trans hd
    omega

end CFSG.Quasithin.ChapterI.Section04To05.G2Recognition
