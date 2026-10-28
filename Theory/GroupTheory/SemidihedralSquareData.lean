module
public import Theory.GroupTheory.SemidihedralCenter
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
# Squares and a normal cyclic four in a semidihedral group

In an explicitly presented semidihedral group, the center has order two,
and the square of every element of order dividing four lies in that center.
The quarter-order rotation has order four and every element fixes or inverts it.
These intrinsic data let a commuting dihedral-eight factor supply order-four
roots in involution centralizers.

The proof uses the two bounded normal forms. The square of an outer element
is a power of the central involution; for a rotation, the fourth-power equation
forces its square into the center. The involutory generator inverts the
quarter-order rotation.

Source: the presentation calculations in Alperin–Brauer–Gorenstein, Chapter II,
Section 1, Lemma 1, printed p.9 (`refs/latex/alperin-brauer-gorenstein.tex`),
continuing `SemidihedralCenter`.
-/

open Subgroup

namespace Semidihedral

/-- Central involution squares and a normal cyclic subgroup of order four
in the explicit semidihedral presentation. -/
public theorem square_data
    {C : Type*} [Group C] {n : ℕ} (hn : 4 ≤ n) (a b : C)
    (ha : orderOf a = 2 ^ (n - 1)) (hb : orderOf b = 2)
    (hconj : b * a * b⁻¹ = a ^ (2 ^ (n - 2) - 1))
    (hgen : closure ({a, b} : Set C) = ⊤) :
    Nat.card (center C) = 2 ∧
      (∀ c : C, c ^ 4 = 1 → c ^ 2 ∈ center C) ∧
      ∃ q : C, orderOf q = 4 ∧ ∀ c : C, c * q * c⁻¹ = q ∨ c * q * c⁻¹ = q⁻¹ := by
  let scale := 2 ^ (n - 4)
  have hs : 0 < scale := by dsimp [scale]; positivity
  have hfull : 2 ^ (n - 1) = 8 * scale := by
    dsimp [scale]
    rw [show n - 1 = n - 4 + 3 by omega, pow_add]
    ring
  have hhalf : 2 ^ (n - 2) = 4 * scale := by
    dsimp [scale]
    rw [show n - 2 = n - 4 + 2 by omega, pow_add]
    ring
  rw [hfull] at ha
  rw [hhalf] at hconj
  have hZ : center C = zpowers (a ^ (4 * scale)) := by
    simpa only [hhalf] using Semidihedral.center_eq hn a b (hfull ▸ ha) hb
      (hhalf ▸ hconj) hgen
  have hz : orderOf (a ^ (4 * scale)) = 2 := by
    rw [orderOf_pow_of_dvd (by omega) (by rw [ha]; exact ⟨2, by ring⟩), ha]
    exact Nat.div_eq_of_eq_mul_left (by omega) (by omega)
  have hb2 : b * b = 1 := by simpa only [hb, pow_two] using pow_orderOf_eq_one b
  have hnf (c : C) : ∃ i : ℕ, i < 8 * scale ∧ (c = a ^ i ∨ c = a ^ i * b) :=
    Semidihedral.normal_form a b _ _ (by omega) ha (by simpa [pow_two] using hb2)
      hconj hgen c
  have hsq (i : ℕ) : (a ^ i * b) ^ 2 = a ^ (4 * scale * i) := by
    calc
      (a ^ i * b) ^ 2 = a ^ i * (b * a ^ i) * b := by simp only [pow_two, mul_assoc]
      _ = a ^ i * (a ^ ((4 * scale - 1) * i) * b) * b := by
        rw [Semidihedral.move_pow a b _ hconj i]
      _ = a ^ (i + (4 * scale - 1) * i) := by
        rw [mul_assoc, mul_assoc, hb2, mul_one, ← pow_add]
      _ = a ^ (4 * scale * i) := by
        congr 1
        have : 4 * scale - 1 + 1 = 4 * scale := by omega
        nlinarith
  refine ⟨by rw [hZ, Nat.card_zpowers, hz], ?_, a ^ (2 * scale), ?_, ?_⟩
  · intro c hc
    rw [hZ]
    obtain ⟨i, -, rfl | rfl⟩ := hnf c
    · have hd : 4 * (2 * scale) ∣ 4 * i := by
        rw [show 4 * (2 * scale) = 8 * scale by omega, ← ha,
          orderOf_dvd_iff_pow_eq_one, mul_comm 4 i, pow_mul]
        exact hc
      obtain ⟨j, rfl⟩ := (Nat.mul_dvd_mul_iff_left (by decide : 0 < 4)).mp hd
      simpa only [← pow_mul, show 2 * scale * j * 2 = (4 * scale) * j by ring] using
        (pow_mem (mem_zpowers (a ^ (4 * scale))) j)
    · rw [hsq]
      exact (pow_mul a (4 * scale) i).symm ▸ pow_mem (mem_zpowers _) i
  · rw [orderOf_pow_of_dvd (by omega) (by rw [ha]; exact ⟨4, by ring⟩), ha]
    exact Nat.div_eq_of_eq_mul_left (by omega) (by omega)
  · intro c
    have hbi : b * a ^ (2 * scale) * b⁻¹ = (a ^ (2 * scale))⁻¹ := by
      apply eq_inv_of_mul_eq_one_left
      have hp := congrArg (fun element : C => element ^ (2 * scale)) hconj
      rw [← MulAut.conj_apply, ← map_pow, MulAut.conj_apply, ← pow_mul] at hp
      rw [hp, ← pow_add]
      have he : (4 * scale - 1) * (2 * scale) + 2 * scale = (8 * scale) * scale := by
        have : 4 * scale - 1 + 1 = 4 * scale := by omega
        nlinarith
      rw [he, pow_mul, ← ha, pow_orderOf_eq_one, one_pow]
    obtain ⟨i, -, rfl | rfl⟩ := hnf c
    · exact Or.inl (mul_inv_eq_iff_eq_mul.mpr (Commute.pow_pow_self a i _).eq)
    · right
      calc
        (a ^ i * b) * a ^ (2 * scale) * (a ^ i * b)⁻¹ =
            a ^ i * (b * a ^ (2 * scale) * b⁻¹) * (a ^ i)⁻¹ := by group
        _ = a ^ i * (a ^ (2 * scale))⁻¹ * (a ^ i)⁻¹ := by rw [hbi]
        _ = (a ^ (2 * scale))⁻¹ :=
          mul_inv_eq_iff_eq_mul.mpr (Commute.pow_pow_self a i _).inv_right.eq

end Semidihedral
