module
public import Mathlib.GroupTheory.Sylow
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring
/-!
# The final numerical step in J.3.1

The exact two- and three-primary Sylow orders, a subgroup of order125, and
seven/thirteen divisibility give the required base divisor of |G|. The order
estimate bounds its cofactor below42. The Sylow-thirteen congruence, together
with the exact two- and three-parts, then forces that cofactor to be29.

Source: Aschbacher--Smith, proof of J.3.1, printed p.439.
-/

public section
namespace CFSG.Quasithin.ChapterJ.Section03

theorem order_arithmetic (n : ℕ)
    (hdiv : 2^14 * 3^3 * 5^3 * 7 * 13 ∣ n)
    (htwo : ¬ 2^15 ∣ n) (hthree : ¬ 3^4 ∣ n)
    (hbound : n ≤ (2^14*3*5) * (455*(455+1391)))
    (hmod : Nat.ModEq (13^2) n (13*48)) :
    n = 2^14 * 3^3 * 5^3 * 7 * 13 * 29 := by
  obtain ⟨k, rfl⟩ := hdiv
  have hklt : k < 42 := by
    clear htwo hthree hmod
    norm_num at hbound
    omega
  have hk2 : ¬ 2 ∣ k := by
    rintro ⟨l, rfl⟩
    apply htwo
    refine ⟨307125*l, ?_⟩
    ring
  have hk3 : ¬ 3 ∣ k := by
    rintro ⟨l, rfl⟩
    apply hthree
    refine ⟨186368000*l, ?_⟩
    ring
  change (2^14 * 3^3 * 5^3 * 7 * 13 * k) % (13^2) = (13*48) % (13^2) at hmod
  rw [Nat.mul_mod] at hmod
  norm_num at hmod
  have hk : k = 29 := by
    clear htwo hthree hbound
    omega
  rw [hk]

open Subgroup
variable {G : Type*} [Group G] [Finite G]

/-- An exact Sylow order excludes the next prime power from the ambient order. -/
private theorem sylow_next_power_not_dvd {p n : ℕ} [Fact p.Prime] (P : Sylow p G)
    (hcard : Nat.card P = p^n) : ¬ p^(n+1) ∣ Nat.card G := by
  intro hd
  rw [← (P : Subgroup G).card_mul_index,hcard,pow_succ] at hd
  exact P.not_dvd_index ((Nat.mul_dvd_mul_iff_left (pow_pos (Fact.out : p.Prime).pos n)).mp hd)

/-- The full source order follows from the exact two- and three-primary
Sylow orders, a five-subgroup, the two odd-prime divisors and the thirteen normalizer. -/
theorem order_of_sylow_data (P2 : Sylow 2 G) (h2 : Nat.card P2 = 2^14)
    (P3 : Sylow 3 G) (h3 : Nat.card P3 = 3^3)
    (P5 : Subgroup G) (h5 : Nat.card P5 = 5^3)
    (h7 : 7 ∣ Nat.card G) (h13 : 13 ∣ Nat.card G)
    (hbound : Nat.card G ≤ (2^14*3*5)*(455*(455+1391)))
    (hmod : Nat.ModEq (13^2) (Nat.card G) (13*48)) :
    Nat.card G = 2^14 * 3^3 * 5^3 * 7 * 13 * 29 := by
  have hd2 : 2^14 ∣ Nat.card G := h2 ▸ (P2 : Subgroup G).card_subgroup_dvd_card
  have hd3 : 3^3 ∣ Nat.card G := h3 ▸ (P3 : Subgroup G).card_subgroup_dvd_card
  have hd5 : 5^3 ∣ Nat.card G := h5 ▸ P5.card_subgroup_dvd_card
  have h23 : 2^14 * 3^3 ∣ Nat.card G :=
    (show Nat.Coprime (2^14) (3^3) by decide).mul_dvd_of_dvd_of_dvd hd2 hd3
  have h235 : 2^14 * 3^3 * 5^3 ∣ Nat.card G :=
    (show Nat.Coprime (2^14 * 3^3) (5^3) by decide).mul_dvd_of_dvd_of_dvd h23 hd5
  have h2357 : 2^14 * 3^3 * 5^3 * 7 ∣ Nat.card G :=
    (show Nat.Coprime (2^14 * 3^3 * 5^3) 7 by decide).mul_dvd_of_dvd_of_dvd h235 h7
  have hdiv : 2^14 * 3^3 * 5^3 * 7 * 13 ∣ Nat.card G :=
    (show Nat.Coprime (2^14 * 3^3 * 5^3 * 7) 13 by decide).mul_dvd_of_dvd_of_dvd h2357 h13
  let : Fact (Nat.Prime 2) := ⟨by decide⟩
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  exact order_arithmetic (Nat.card G) hdiv (sylow_next_power_not_dvd P2 h2)
    (sylow_next_power_not_dvd P3 h3) hbound hmod

end CFSG.Quasithin.ChapterJ.Section03
