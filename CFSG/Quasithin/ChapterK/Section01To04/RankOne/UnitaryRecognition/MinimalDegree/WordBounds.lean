module

public import CFSG.Quasithin.ChapterK.Section01To04.RankOne.UnitaryRecognition.MinimalDegree.TensorWords

/-!
# The numerical separation of the unitary tensor words

Write e for the binary Schur degree. Twisted Frobenius orbits give two
possibilities for a nontrivial word. If it has a natural or dual label,
there are at least r such labels with e*r = 2*s. Otherwise there are at
least r adjoint labels with e*r = s. The inequalities 3^r > 3*r for r≥2
and 8^r > 6*r for r≥1 force e=2*s and exactly one natural or dual label
when the binary dimension is at most 6*s.

The orbit statements are explicit hypotheses below. Their representation-
theoretic proof must retain the graph twist; ordinary SL₃ word rotation
does not supply them. The consumer in MinimalDegree applies this calculation
to the actual scalar extension of a binary action's endomorphism field.

Source: GLS III, §2.8, especially Remark 2.8.8 and 2.8.10(c).
-/

public section
namespace CFSG.Quasithin.ChapterK.RankOne.UnitaryRecognition.MinimalDegree
open Representation.SL3.BinaryDefiningFactors

/-- The two counting consequences of the twisted Frobenius orbit.
This is a conditional numerical interface, not a recognition hypothesis
in the source theorem. -/
def PeriodCounts (s e : ℕ) (w : List Factor) : Prop :=
  (∃ r : ℕ, 0 < r ∧ e * r = 2 * s ∧ r ≤ naturalCount w) ∨
  (∃ r : ℕ, 0 < r ∧ e * r = s ∧ r ≤ adjointCount w)

private theorem three_mul_lt_pow {r : ℕ} (hr : 2 ≤ r) : 3 * r < 3 ^ r := by
  induction r, hr using Nat.le_induction with
  | base => decide
  | succ r hr ih =>
    rw [pow_succ]
    nlinarith

private theorem six_mul_lt_eight_pow {r : ℕ} (hr : 0 < r) : 6 * r < 8 ^ r := by
  induction r, hr using Nat.le_induction with
  | base => decide
  | succ r hr ih =>
    rw [pow_succ]
    nlinarith

private theorem natural_power_le_degree (w : List Factor) :
    3 ^ naturalCount w ≤ wordDegree w := by
  rw [wordDegree_eq]
  exact Nat.le_mul_of_pos_right _ (pow_pos (by decide) _)

private theorem adjoint_power_le_degree (w : List Factor) :
    8 ^ adjointCount w ≤ wordDegree w := by
  rw [wordDegree_eq]
  exact Nat.le_mul_of_pos_left _ (pow_pos (by decide) _)

/-- The degree bound excludes every repeated or adjoint word. It identifies
the two surviving labels separately from constructing their intertwiners. -/
theorem single_factor_of_periodCounts (s e : ℕ) (he : 0 < e)
    (w : List Factor) (hp : PeriodCounts s e w)
    (hd : e * wordDegree w ≤ 6 * s) :
    e = 2 * s ∧ naturalCount w = 1 ∧ adjointCount w = 0 := by
  rcases hp with ⟨r, hr, hperiod, hcount⟩ | ⟨r, hr, hperiod, hcount⟩
  · have hpow : 3 ^ r ≤ wordDegree w :=
      (Nat.pow_le_pow_right (by decide) hcount).trans (natural_power_le_degree w)
    have hrone : r = 1 := by
      by_contra h
      have hstrict := three_mul_lt_pow (r := r) (by omega)
      have hlt : e * (3 * r) < e * wordDegree w :=
        Nat.mul_lt_mul_of_pos_left (hstrict.trans_le hpow) he
      nlinarith
    subst r
    have hes : e = 2 * s := by simpa using hperiod
    have hdegree : wordDegree w ≤ 3 := by nlinarith
    have hn : naturalCount w = 1 := by
      have hpn := natural_power_le_degree w
      by_contra h
      have htwo : 2 ≤ naturalCount w := by omega
      have hlarge := Nat.pow_le_pow_right (n := 3) (by decide) htwo
      norm_num at hlarge
      omega
    have ha : adjointCount w = 0 := by
      have hpa := adjoint_power_le_degree w
      by_contra h
      have hone : 1 ≤ adjointCount w := by omega
      have hlarge := Nat.pow_le_pow_right (n := 8) (by decide) hone
      norm_num at hlarge
      omega
    exact ⟨hes, hn, ha⟩
  · have hpow : 8 ^ r ≤ wordDegree w :=
      (Nat.pow_le_pow_right (by decide) hcount).trans (adjoint_power_le_degree w)
    have hstrict := six_mul_lt_eight_pow hr
    have hlt : e * (6 * r) < e * wordDegree w :=
      Nat.mul_lt_mul_of_pos_left (hstrict.trans_le hpow) he
    nlinarith

end CFSG.Quasithin.ChapterK.RankOne.UnitaryRecognition.MinimalDegree
