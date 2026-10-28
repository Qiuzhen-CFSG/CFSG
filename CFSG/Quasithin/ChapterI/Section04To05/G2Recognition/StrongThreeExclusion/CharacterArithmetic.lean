module

public import Mathlib.Tactic
public import Mathlib.NumberTheory.Divisors

/-!
# Integer arithmetic for the strongly three-embedded character calculation

The degree-product divisibility cancels the two consecutive degrees from the
group-order identity. Thus the squared degree-minus-involution-value divides
5,971,968. Its positive square root divides 3456, leaving a short divisor
list. The involution column bound leaves finitely many integer character
values. Kernel-checked arithmetic gives the three possible group orders.

All character-theoretic identities are explicit premises here. Their
construction from the original configuration belongs to the source assembly.
-/

public section
set_option maxRecDepth 100000

namespace CFSG.Quasithin.ChapterI.Section04To05.G2Recognition

private theorem square_divisor_candidates (k : ℕ)
    (hk : 8 ∣ k) (hsq : k ^ 2 ∣ 5971968) :
    k ∈ ({8, 16, 24, 32, 48, 64, 72, 96, 144, 192, 216, 288, 432, 576, 864, 1728} : Finset ℕ) := by
  have hd : k ∣ 3456 := (Nat.pow_dvd_pow_iff (by decide : 2 ≠ 0)).mp
    (hsq.trans (by decide : 5971968 ∣ 3456 ^ 2))
  have hm : k ∈ (Nat.divisors 3456).filter (fun n => 8 ∣ n ∧ n ^ 2 ∣ 5971968) :=
    Finset.mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨hd, by decide⟩, hk, hsq⟩
  have hf : (Nat.divisors 3456).filter (fun n => 8 ∣ n ∧ n ^ 2 ∣ 5971968) =
      {8, 16, 24, 32, 48, 64, 72, 96, 144, 192, 216, 288, 432, 576, 864, 1728} := by
    decide +kernel
  simpa only [hf] using hm

set_option synthInstance.maxSize 1000 in
private theorem bounded_character_arithmetic :
    ∀ k ∈ ({8, 16, 24, 32, 48, 64, 72, 96, 144, 192, 216, 288, 432, 576, 864, 1728} : Finset ℕ),
    ∀ b ∈ Finset.Icc (-12 : ℤ) 12, ∀ δ ∈ ({-1, 1} : Finset ℤ),
    (fun (e : ℤ) (g : ℕ) =>
    0 < e → 0 < e + δ →
    1 + b ^ 2 + 4 * (b + δ) ^ 2 ≤ 576 →
    4032 ∣ g → ¬ 128 ∣ g → ¬ 27 ∣ g →
    ¬ (9 : ℤ) ∣ e → ¬ (9 : ℤ) ∣ e + δ →
    (g : ℤ) * (k : ℤ) ^ 2 = 5971968 * (e * (e + δ)) →
    g = 5664960 ∨ g = 5132736 ∨ g = 6874560)
      ((k : ℤ) + b) (5971968 * (((k : ℤ) + b) * ((k : ℤ) + b + δ)) / (k : ℤ) ^ 2).toNat := by
  dsimp only
  decide +kernel

/-- The actual signed degree and involution-value identities leave exactly
the three orders excluded by the Sylow-normalizer calculation. -/
theorem order_candidates_of_character_identities
    (g : ℕ) (e b δ : ℤ)
    (hδ : δ = -1 ∨ δ = 1) (he : 0 < e) (he' : 0 < e + δ)
    (hk : 0 < e - b) (h8 : (8 : ℤ) ∣ e - b)
    (hdegree : e * (e + δ) ∣ (g : ℤ))
    (horder : (g : ℤ) * (e - b) ^ 2 = 5971968 * (e * (e + δ)))
    (hcolumn : 1 + b ^ 2 + 4 * (b + δ) ^ 2 ≤ 576)
    (hlocal : 4032 ∣ g) (h128 : ¬ 128 ∣ g) (h27 : ¬ 27 ∣ g)
    (he9 : ¬ (9 : ℤ) ∣ e) (he9' : ¬ (9 : ℤ) ∣ e + δ) :
    g = 5664960 ∨ g = 5132736 ∨ g = 6874560 := by
  let k := (e - b).toNat
  have hkcast : (k : ℤ) = e - b := Int.toNat_of_nonneg hk.le
  have hkpos : 0 < k := by omega
  have hsquare : (e - b) ^ 2 ∣ (5971968 : ℤ) := by
    obtain ⟨a, ha⟩ := hdegree
    have hp : e * (e + δ) ≠ 0 := (mul_pos he he').ne'
    have hh : (e * (e + δ)) * ((e - b) ^ 2 * a) =
        (e * (e + δ)) * 5971968 := by
      calc
        _ = (g : ℤ) * (e - b) ^ 2 := by rw [ha]; ring
        _ = _ := horder.trans (mul_comm _ _)
    exact ⟨a, (mul_left_cancel₀ hp hh).symm⟩
  have hk8 : 8 ∣ k := by exact_mod_cast (hkcast ▸ h8 : (8 : ℤ) ∣ (k : ℤ))
  have hksquare : k ^ 2 ∣ 5971968 := by
    have hh : (k : ℤ) ^ 2 ∣ 5971968 := by simpa only [hkcast] using hsquare
    exact_mod_cast hh
  have hb : -12 ≤ b ∧ b ≤ 12 := by
    rcases hδ with rfl | rfl <;> constructor <;> nlinarith
  have hg : (5971968 * (e * (e + δ)) / (k : ℤ) ^ 2).toNat = g := by
    rw [← horder, ← hkcast, Int.mul_ediv_cancel _ (by positivity : (k : ℤ) ^ 2 ≠ 0)]
    simp
  have hkc : (k : ℤ) + b = e := by omega
  have hh := bounded_character_arithmetic k (square_divisor_candidates k hk8 hksquare)
    b (Finset.mem_Icc.mpr hb) δ (by simpa only [Finset.mem_insert, Finset.mem_singleton] using hδ)
  dsimp only at hh
  rw [hkc, hg] at hh
  exact hh he he' hcolumn hlocal h128 h27 he9 he9' (by simpa only [hkcast] using horder)

end CFSG.Quasithin.ChapterI.Section04To05.G2Recognition
