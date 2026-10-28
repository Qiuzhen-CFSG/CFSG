module

public import ABG.ChapterII.Section1.WreathedDiagonalOrder
public import ABG.ChapterII.Section1.WreathedRelations

/-!
# Small exponent bounds for semidihedral and wreathed groups

An exponent dividing eight bounds a semidihedral group's cyclic subgroup
of index two by eight. In a wreathed presentation the square of s*z is the
diagonal generator of order 2^n. Its fourth power is one, forcing height
n=2. Thus these two Sylow shapes have order at most 32.

Source: ABG Chapter II §1, article pp.9--10; the degree-three Sylow
applications are Aschbacher--Smith A.3.21 and F.6.18.
-/

public section
namespace Theory.GroupTheory
variable {G : Type*} [Group G]

theorem card_le_32_of_semidihedral_or_wreathed_exponent_eight
    (h : Stellmacher.IsSemidihedralGroup G ∨ ABG.IsWreathedGroup G)
    (he : ∀ x : G, x ^ 8 = 1) : Nat.card G ≤ 32 := by
  rcases h with h | ⟨n, h⟩
  · obtain ⟨n, hn, hc, a, _, ha, _, _, _⟩ := h
    have hd : 2 ^ (n - 1) ∣ 8 := ha ▸ orderOf_dvd_of_pow_eq_one (he a)
    have hb : 2 ^ (n - 1) ≤ 2 ^ 3 := Nat.le_of_dvd (by decide) hd
    have hn3 := (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hb
    rw [hc]
    exact Nat.pow_le_pow_right (by decide) (by omega : n ≤ 5)
  · obtain ⟨P⟩ := ABG.Wreathed.nonempty_presentation h
    have hsq : (P.s * P.z) ^ 2 = P.u := by
      calc
        _ = P.s * (P.z * P.s) * P.z := by simp only [pow_two, mul_assoc]
        _ = P.s * (P.t * P.z) * P.z := by rw [P.z_mul_s]
        _ = P.u := by simp only [ABG.Wreathed.Presentation.u, mul_assoc, ← pow_two, P.z_sq, mul_one]
    have hu : P.u ^ 4 = 1 := by
      rw [← hsq, ← pow_mul]
      exact he (P.s * P.z)
    have hd : 2 ^ n ∣ 4 := P.orderOf_u ▸ orderOf_dvd_of_pow_eq_one hu
    have hb : 2 ^ n ≤ 2 ^ 2 := Nat.le_of_dvd (by decide) hd
    have hn2 := (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hb
    rw [P.card]
    exact Nat.pow_le_pow_right (by decide) (by omega : 2 * n + 1 ≤ 5)

end Theory.GroupTheory
