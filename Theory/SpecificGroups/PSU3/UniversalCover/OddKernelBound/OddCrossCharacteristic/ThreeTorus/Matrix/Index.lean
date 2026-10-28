module

public import Theory.SpecificGroups.PSU3.UniversalCover.OddKernelBound.OddCrossCharacteristic.ThreeTorus.Matrix.Parameters
public import Theory.SpecificGroups.PSU3.UniversalCover.EvenKernelBound.ThreePrimary.MatrixTorus.Weyl
public import Theory.GroupTheory.NormalizedSupCard
public import Theory.SpecificGroups.PSU3.UniversalCover.OddKernelBound.OddCrossCharacteristic.Order
/-!
# The three-primary torus and cycle have index prime to three

The coordinate cycle has order three and does not lie in the diagonal
projective torus: multiplying a diagonal matrix by a scalar cannot produce
its off-diagonal entry. Thus its cyclic subgroup meets the torus trivially.
Normalization gives the join order m², after the torus's scalar cubic kernel
has reduced its order to m²/3.

Write q+1 = m*d, where m is the full three-part and 3 does not divide d.
For q = 3*s+2 the remaining cubic factor divided by three is 3*s²+3*s+1.
The exact PSU₃ order then makes the join's index prime to three. There is
no bound on the three-valuation of q+1.

Source: Aschbacher–Smith I.1.3(2), I.1.4(2), PDF pp.418–419;
GLS III, Theorem 6.1.4 and Tables 6.1.2–3; Huppert II.10.12 for the order.
-/

open Matrix Subgroup BenderSuzuki.MatrixGroups
open BenderSuzuki.MatrixGroups.HermitianForm.UniversalCover.EvenKernelBound.ThreePrimary.MatrixTorus
@[expose] public noncomputable section
namespace BenderSuzuki.MatrixGroups.HermitianForm.UniversalCover.OddKernelBound.OddCrossCharacteristic.OddThreeMatrix
variable {F : Type*} [Field F] (J : HermitianForm 3 F) (hJ : J.form = 1)
variable (C : Subgroup Fˣ) (hC : ∀ u : C, J.conj (u.val : F) * (u.val : F) = 1)
local instance : Fact (Nat.Prime 3) := ⟨by decide⟩
/-- A scalar multiple of a diagonal matrix cannot be the coordinate cycle. -/
theorem cycle_not_mem_torus : cycle J hJ ∉ torus J hJ C hC := by
  rintro ⟨a, ha⟩
  have he : ProjGenLinGroup.mk (diagonalGL C a) = ProjGenLinGroup.mk (cycleGL (F := F)) := by
    simpa only [diagonalProjective_val, cycle, J.specialToProjective_apply_val] using
      congrArg Subtype.val ha
  obtain ⟨u, hu⟩ := ProjGenLinGroup.mk_eq_mk_iff.mp he
  have h01 := congrArg (fun g : GL (Fin 3) F => g.val 0 1) hu
  simp [diagonalGL_val, GeneralLinearGroup.coe_scalar, Matrix.scalar,
    cycleGL] at h01

/-- The coordinate cycle retains order three in the projective quotient. -/
theorem cycle_order : orderOf (cycle J hJ) = 3 := by
  apply orderOf_eq_prime (cycle_cube J hJ)
  intro he
  apply cycle_not_mem_torus J hJ (HermitianForm.EvenInner.normOne J) (normOne_norm J)
  rw [he]
  exact one_mem _

/-- The cyclic supplement meets the projective diagonal torus trivially. -/
theorem cycle_disjoint_torus [Finite F] :
    Disjoint (torus J hJ C hC) (zpowers (cycle J hJ)) := by
  classical
  rw [Subgroup.disjoint_def]
  intro x hx hy
  rw [mem_zpowers_iff_mem_range_orderOf, cycle_order] at hy
  obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hy
  have hn3 : n < 3 := Finset.mem_range.mp hn
  interval_cases n
  · simp
  · simp only [pow_one] at hx
    exact (cycle_not_mem_torus J hJ C hC hx).elim
  · have h4 : (cycle J hJ ^ 2) ^ 2 = cycle J hJ := by
      rw [← pow_mul, show 2 * 2 = 3 + 1 from rfl, pow_add, cycle_cube, pow_one, one_mul]
    exact (cycle_not_mem_torus J hJ C hC (h4 ▸ pow_mem hx 2)).elim


/-- Adjoining the normalizing cycle triples the actual projective torus order. -/
theorem torus_join_card [Finite F] :
    Nat.card (torus J hJ C hC ⊔ zpowers (cycle J hJ) :
      Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) = Nat.card (torus J hJ C hC) * 3 := by
  rw [card_sup_eq_mul_of_normalizes_of_disjoint _ _
    (zpowers_le.mpr (cycle_normalizes J hJ C hC)) (cycle_disjoint_torus J hJ C hC),
    Nat.card_zpowers, cycle_order]

/-- The full three-part squared, after cancelling the scalar cubic kernel. -/
theorem primary_join_card [Finite F] {q : ℕ}
    (hcard : Nat.card F = q ^ 2) (hc : ∀ x, J.conj x = x ^ q) (hq : 3 ∣ q + 1) :
    Nat.card (primaryTorus J hJ ⊔ zpowers (cycle J hJ) :
      Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) = Nat.card (primary J) ^ 2 := by
  rw [primaryTorus, torus_join_card, ← primaryTorus, primaryTorus_card J hJ hcard hc hq]
  exact Nat.div_mul_cancel (dvd_pow (primary_three_dvd J hcard hc hq) (by decide : 2 ≠ 0))
private theorem order_factorization {q : ℕ} (hq : q % 3 = 2) :
    (q ^ 3 + 1) * q ^ 3 * (q ^ 2 - 1) / Nat.gcd 3 (q + 1) =
      (q + 1) ^ 2 * (q ^ 3 * (3 * (q / 3) + 1) *
        (3 * (q / 3) ^ 2 + 3 * (q / 3) + 1)) := by
  have he : q = 3 * (q / 3) + 2 := by omega
  have hsq : q ^ 2 - 1 = (3 * (q / 3) + 1) * (q + 1) := by
    rw [show q ^ 2 - 1 = (q - 1) * (q + 1) by simpa [mul_comm] using Nat.sq_sub_sq q 1]
    congr 1
    omega
  have hcube : q ^ 3 + 1 = (q + 1) * (3 * (q / 3) ^ 2 + 3 * (q / 3) + 1) * 3 := by
    conv_lhs => rw [he]
    conv_rhs => arg 1; arg 1; rw [he]
    ring
  rw [Nat.gcd_eq_left (show 3 ∣ q + 1 from Nat.dvd_of_mod_eq_zero (by omega)), hsq, hcube]
  have hr : ((q + 1) * (3 * (q / 3) ^ 2 + 3 * (q / 3) + 1) * 3) * q ^ 3 *
      ((3 * (q / 3) + 1) * (q + 1)) =
      ((q + 1) ^ 2 * (q ^ 3 * (3 * (q / 3) + 1) *
        (3 * (q / 3) ^ 2 + 3 * (q / 3) + 1))) * 3 := by ring
  rw [hr, Nat.mul_div_left _ (by decide : 0 < 3)]

private theorem index_prime_to_three_of_card {q m d k : ℕ} (hq : q % 3 = 2)
    (hm : 0 < m) (hmd : m * d = q + 1) (hd : ¬ 3 ∣ d)
    (hk : m ^ 2 * k = (q ^ 3 + 1) * q ^ 3 * (q ^ 2 - 1) / Nat.gcd 3 (q + 1)) :
    ¬ 3 ∣ k := by
  rw [order_factorization hq, ← hmd, mul_pow, mul_assoc] at hk
  have he := Nat.eq_of_mul_eq_mul_left (pow_pos hm 2) hk
  rw [he]
  apply Nat.Prime.not_dvd_mul (by decide : Nat.Prime 3)
  · exact fun h => hd ((by decide : Nat.Prime 3).dvd_of_dvd_pow h)
  · apply Nat.Prime.not_dvd_mul (by decide : Nat.Prime 3)
    · apply Nat.Prime.not_dvd_mul (by decide : Nat.Prime 3)
      · intro h
        have h0 := Nat.mod_eq_zero_of_dvd ((by decide : Nat.Prime 3).dvd_of_dvd_pow h)
        omega
      · exact fun h => by have := Nat.mod_eq_zero_of_dvd h; omega
    · intro h
      have hz := Nat.mod_eq_zero_of_dvd h
      simp [Nat.add_mod] at hz

/-- The constructed join contains a Sylow three-subgroup of the actual PSU₃. -/
theorem primary_join_index [Finite F] {q : ℕ}
    (hcard : Nat.card F = q ^ 2) (hc : ∀ x, J.conj x = x ^ q) (hq : q % 3 = 2) :
    ¬ 3 ∣ (primaryTorus J hJ ⊔ zpowers (cycle J hJ)).index := by
  obtain ⟨d, hmd, hd⟩ := primary_complement J hcard hc
  apply index_prime_to_three_of_card hq (Nat.card_pos (α := primary J)) hmd hd
  have h := (primaryTorus J hJ ⊔ zpowers (cycle J hJ)).card_mul_index
  rw [primary_join_card J hJ hcard hc (Nat.dvd_of_mod_eq_zero (by omega)),
    card_projective J hcard hc] at h
  exact h

end BenderSuzuki.MatrixGroups.HermitianForm.UniversalCover.OddKernelBound.OddCrossCharacteristic.OddThreeMatrix
