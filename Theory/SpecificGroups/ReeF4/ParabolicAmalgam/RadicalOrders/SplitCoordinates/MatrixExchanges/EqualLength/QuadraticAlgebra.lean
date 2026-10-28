module

public import Mathlib.Algebra.Ring.Commute
public import Mathlib.Algebra.Group.Torsion
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NoncommRing

/-!
# A finite exponential identity for a central commutator

In an additively torsion-free ring, suppose [A,B] = D commutes with A and B,
and A³ = B³ = 0. Given integral second divided powers A₂, B₂, D₂, the
quadratic exponentials satisfy exp(A)exp(B) = exp(B)exp(A)exp(D).
The proof cancels 2 and 3 to establish the mixed divided-power identities
and the higher-degree vanishings before expanding the finite products.

This elementary associative-ring calculation supplies the equal-length
Chevalley collection used in Aschbacher–Smith F.1.12(I)(5), printed p.263
of `refs/quasithin.pdf`. It will be applied over an integer polynomial ring
before evaluation in characteristic two.
-/

public section
namespace ReeF4.Parabolics.RadicalCoordinates.EqualLength
variable {R : Type*} [Ring R] [IsAddTorsionFree R]

private lemma triple (a b d : R) (hab : a*b - b*a = d) (had : Commute a d)
    (ha3 : a^3 = 0) : a*a*d = 0 := by
  have h : (3 : ℕ) • (a*a*d) = 0 := by
    calc
      _ = a*a*(a*b-b*a)+a*(a*b-b*a)*a+(a*b-b*a)*a*a := by
        rw [hab]
        noncomm_ring [← had.eq, ← had.left_comm]
      _ = a^3*b - b*a^3 := by noncomm_ring
      _ = 0 := by rw [ha3]; simp
  exact (nsmul_right_injective (by decide : (3 : ℕ) ≠ 0)) (by simpa using h)

private lemma half_bracket (a b d a2 : R) (hab : a*b - b*a = d) (had : Commute a d)
    (ha2 : a*a = (2 : ℕ) • a2) : a2*b - b*a2 = a*d := by
  apply nsmul_right_injective (by decide : (2 : ℕ) ≠ 0)
  calc
    (2 : ℕ) • (a2*b - b*a2) = a*(a*b-b*a)+(a*b-b*a)*a := by
      rw [smul_sub, ← smul_mul_assoc, ← mul_smul_comm, ← ha2]
      noncomm_ring
    _ = (2 : ℕ) • (a*d) := by rw [hab, ← had.eq]; abel

private lemma commute_half (a a2 d : R) (ha2 : a*a = (2 : ℕ) • a2)
    (had : Commute a d) : Commute a2 d := by
  change a2*d = d*a2
  apply nsmul_right_injective (by decide : (2 : ℕ) ≠ 0)
  dsimp only
  rw [← smul_mul_assoc, ← mul_smul_comm, ← ha2]
  exact had.mul_left had |>.eq

private lemma half_mul_zero (a b d a2 : R) (hab : a*b-b*a=d) (had : Commute a d)
    (ha2 : a*a = (2 : ℕ) • a2) (ha3 : a^3=0) : a2*d=0 := by
  apply nsmul_right_injective (by decide : (2 : ℕ) ≠ 0)
  dsimp only
  rw [smul_zero, ← smul_mul_assoc, ← ha2]
  exact triple a b d hab had ha3

private lemma mul_half_commutator_zero (a b d a2 d2 : R) (hab : a*b-b*a=d)
    (had : Commute a d) (hbd : Commute b d)
    (ha2 : a*a = (2 : ℕ) • a2) (hd2 : d*d = (2 : ℕ) • d2)
    (ha3 : a^3=0) : a*d2=0 := by
  have hz := half_mul_zero a b d a2 hab had ha2 ha3
  have hhalf := half_bracket a b d a2 hab had ha2
  apply nsmul_right_injective (by decide : (2 : ℕ) ≠ 0)
  calc
    (2 : ℕ) • (a*d2) = (a*d)*d := by rw [mul_assoc, hd2, mul_smul_comm]
    _ = (a2*b-b*a2)*d := by rw [hhalf]
    _ = 0 := by rw [sub_mul, mul_assoc a2, hbd.eq, ← mul_assoc a2, hz,
        zero_mul, mul_assoc b, hz, mul_zero, sub_zero]
    _ = (2 : ℕ) • (0 : R) := by simp

private lemma half_mul_half_commutator_zero (a b d a2 d2 : R) (hab : a*b-b*a=d)
    (had : Commute a d) (ha2 : a*a = (2 : ℕ) • a2)
    (hd2 : d*d = (2 : ℕ) • d2) (ha3 : a^3=0) : a2*d2=0 := by
  have hz := half_mul_zero a b d a2 hab had ha2 ha3
  apply nsmul_right_injective (by decide : (2 : ℕ) ≠ 0)
  calc
    (2 : ℕ) • (a2*d2) = (a2*d)*d := by rw [mul_assoc, hd2, mul_smul_comm]
    _ = (2 : ℕ) • (0 : R) := by rw [hz]; simp

private lemma half_half_bracket (a b d a2 b2 d2 : R) (hab : a*b-b*a=d)
    (had : Commute a d) (hbd : Commute b d)
    (ha2 : a*a = (2 : ℕ) • a2) (hb2 : b*b = (2 : ℕ) • b2)
    (hd2 : d*d = (2 : ℕ) • d2) : a2*b2-b2*a2 = b*a*d+d2 := by
  have hh := half_bracket a b d a2 hab had ha2
  apply nsmul_right_injective (by decide : (2 : ℕ) ≠ 0)
  calc
    (2 : ℕ) • (a2*b2-b2*a2) = (a2*b-b*a2)*b+b*(a2*b-b*a2) := by
      rw [smul_sub, ← mul_smul_comm, ← smul_mul_assoc, ← hb2]
      noncomm_ring
    _ = (a*b-b*a)*d + (2 : ℕ) • (b*a*d) := by
      rw [hh]
      noncomm_ring [hbd.left_comm, hbd.eq]
    _ = (2 : ℕ) • (b*a*d+d2) := by rw [hab, hd2]; abel


/-- A central commutator exchanges the quadratic divided-power exponentials.
All cancellations occur in the torsion-free additive group of the ring. -/
theorem quadratic_exchange_of_central_bracket (a b d a2 b2 d2 : R) (hab : a*b-b*a=d)
    (had : Commute a d) (hbd : Commute b d)
    (ha2 : a*a = (2 : ℕ) • a2) (hb2 : b*b = (2 : ℕ) • b2)
    (hd2 : d*d = (2 : ℕ) • d2) (ha3 : a^3=0) (hb3 : b^3=0) :
    (1+a+a2)*(1+b+b2) = (1+b+b2)*(1+a+a2)*(1+d+d2) := by
  have hba : b*a-a*b = -d := by rw [← hab]; abel
  have hnd2 : (-d)*(-d) = (2 : ℕ) • d2 := by simpa using hd2
  have hab2 : a*b2-b2*a = b*d := by
    have h := half_bracket b a (-d) b2 hba hbd.neg_right hb2
    rw [mul_neg] at h
    linear_combination (norm := noncomm_ring) -h
  have ha2b := half_bracket a b d a2 hab had ha2
  have ha2b2 := half_half_bracket a b d a2 b2 d2 hab had hbd ha2 hb2 hd2
  have ha2d := half_mul_zero a b d a2 hab had ha2 ha3
  have hb2d : b2*d=0 := by
    have h := half_mul_zero b a (-d) b2 hba hbd.neg_right hb2 hb3
    simpa only [mul_neg, neg_eq_zero] using h
  have had2 := mul_half_commutator_zero a b d a2 d2 hab had hbd ha2 hd2 ha3
  have hbd2 := mul_half_commutator_zero b a (-d) b2 d2 hba hbd.neg_right had.neg_right hb2 hnd2 hb3
  have ha2d2 := half_mul_half_commutator_zero a b d a2 d2 hab had ha2 hd2 ha3
  have hb2d2 := half_mul_half_commutator_zero b a (-d) b2 d2 hba hbd.neg_right hb2 hnd2 hb3
  have hb2ad : b2*(a*d)=0 := by rw [had.eq, ← mul_assoc, hb2d, zero_mul]
  have he : (1+a+a2)*(1+b+b2) =
      (1+b+b2)*(1+a+a2) + (d+a*d+b*d+b*a*d+d2) := by
    linear_combination (norm := noncomm_ring) hab + hab2 + ha2b + ha2b2
  have hx : (1+a+a2)*d = d+a*d := by simp [add_mul, ha2d]
  have hy : (1+a+a2)*d2 = d2 := by simp [add_mul, had2, ha2d2]
  have hz : (1+b+b2)*(1+a+a2)*d = d+a*d+b*d+b*a*d := by
    rw [mul_assoc, hx]
    simp only [add_mul, mul_add, one_mul, hb2d, hb2ad, add_zero]
    noncomm_ring
  have hz2 : (1+b+b2)*(1+a+a2)*d2 = d2 := by
    rw [mul_assoc, hy]
    simp only [add_mul, one_mul, hbd2, hb2d2, add_zero]
  calc
    _ = (1+b+b2)*(1+a+a2) + (d+a*d+b*d+b*a*d+d2) := he
    _ = (1+b+b2)*(1+a+a2) + (1+b+b2)*(1+a+a2)*d +
        (1+b+b2)*(1+a+a2)*d2 := by rw [hz, hz2]; abel
    _ = _ := by noncomm_ring

end ReeF4.Parabolics.RadicalCoordinates.EqualLength
