module

public import Theory.GroupTheory.PerfectCentralInvolutionExtension
public import Theory.SpecificGroups.SL2.CentralTwoExtensions

/-!
# The orthogonal local model for odd G₂ covers

The centralizer of an involution in odd G₂ has shape
`(SL₂(p) ∘ SL₂(p)) . 2`. The interface below asks for the actual homomorphism
from a semidirect product, with kernel the diagonal scalar involution and
image of odd index. It does not assert existence of this homomorphism.

The two involutions needed by the covering argument are the outer generator
and the image of a pair of order-four matrices. The latter squares to the
diagonal kernel generator before projection. Fusing both to the scalar
involution in one factor will eliminate the possible double-cover defect.

Source: the odd G₂ calculation underlying Aschbacher–Smith I.1.1–I.1.4,
printed pp.407–408, and GLS III §6.1. This is local geometric input to the
calculation, not a multiplier-table assertion.
-/

@[expose] public section

namespace Atlas.G2.MultiplierOrdinary.OddTwoPrimary

open scoped MatrixGroups

abbrev RankOne (p : ℕ) [Fact p.Prime] := Matrix.SpecialLinearGroup (Fin 2) (ZMod p)
abbrev C2 := Multiplicative (ZMod 2)

/-- The standard determinant-one matrix with square minus one. -/
def quarterTurn (p : ℕ) [Fact p.Prime] : RankOne p :=
  ⟨!![0, 1; -1, 0], by simp [Matrix.det_fin_two_of]⟩

theorem quarterTurn_sq (p : ℕ) [Fact p.Prime] : quarterTurn p ^ 2 = -1 := by
  rw [pow_two]
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul]
  change (!![0, 1; -1, 0] * !![0, 1; -1, 0] : Matrix (Fin 2) (Fin 2) (ZMod p)) = -1
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem quarterTurn_ne_one (p : ℕ) [Fact p.Prime] : quarterTurn p ≠ 1 := by
  intro h
  have h01 := congrArg (fun x : RankOne p => x.val 0 1) h
  simp [quarterTurn] at h01

theorem quarterTurn_ne_neg_one (p : ℕ) [Fact p.Prime] : quarterTurn p ≠ -1 := by
  intro h
  have h01 := congrArg (fun x : RankOne p => x.val 0 1) h
  simp [quarterTurn] at h01

theorem rankOne_neg_one_ne_one {p : ℕ} [Fact p.Prime] (hp : 3 < p) :
    (-1 : RankOne p) ≠ 1 := by
  intro h
  have h00 := congrArg (fun x : RankOne p => x.val 0 0) h
  have hz : (2 : ZMod p) = 0 := by
    have he : (-1 : ZMod p) = 1 := by simpa using h00
    linear_combination -he
  exact Nat.not_dvd_of_pos_of_lt (by decide) (by omega : 2 < p)
    ((ZMod.natCast_eq_zero_iff 2 p).mp hz)

/-- Concrete local geometry still to be constructed inside the octonion model.
The kernel and index refer to this specified map. -/
structure LocalModel (p : ℕ) [Fact p.Prime] (G : Type*) [Group G] where
  action : C2 →* MulAut (RankOne p × RankOne p)
  inclusion : (RankOne p × RankOne p) ⋊[action] C2 →* G
  kernel : ∀ x, inclusion x = 1 ↔
    x = 1 ∨ x = SemidirectProduct.inl (-1, -1)
  odd_index : Odd inclusion.range.index

namespace LocalModel
variable {p : ℕ} [Fact p.Prime] {G : Type*} [Group G] (m : LocalModel p G)

abbrev Domain := (RankOne p × RankOne p) ⋊[m.action] C2

def scalar : m.Domain := SemidirectProduct.inl (-1, 1)
def diagonal : m.Domain := SemidirectProduct.inl (-1, -1)
def outer : m.Domain := SemidirectProduct.inr (.ofAdd 1)
def paired : m.Domain := SemidirectProduct.inl (quarterTurn p, quarterTurn p)

theorem scalar_sq : m.scalar ^ 2 = 1 := by
  rw [scalar, ← map_pow, show ((-1, 1) : RankOne p × RankOne p) ^ 2 = 1 by
    ext <;> simp, map_one]

theorem diagonal_sq : m.diagonal ^ 2 = 1 := by
  rw [diagonal, ← map_pow, show ((-1, -1) : RankOne p × RankOne p) ^ 2 = 1 by
    ext <;> simp, map_one]

theorem outer_sq : m.outer ^ 2 = 1 := by
  rw [outer, ← map_pow]
  have h : (Multiplicative.ofAdd (1 : ZMod 2)) ^ 2 = 1 := by decide
  rw [h, map_one]

theorem paired_sq : m.paired ^ 2 = m.diagonal := by
  rw [paired, ← map_pow]
  simp only [Prod.pow_mk, quarterTurn_sq]
  rfl

theorem diagonal_mem_kernel : m.inclusion m.diagonal = 1 :=
  (m.kernel _).mpr (Or.inr rfl)

theorem scalar_image_order (hp : 3 < p) : orderOf (m.inclusion m.scalar) = 2 := by
  have hn := rankOne_neg_one_ne_one hp
  apply orderOf_eq_prime_iff.mpr
  refine ⟨by rw [← map_pow, m.scalar_sq, map_one], ?_⟩
  intro h
  rcases (m.kernel _).mp h with h | h
  · exact hn (congrArg (fun x : m.Domain => x.left.1) h)
  · exact hn (congrArg (fun x : m.Domain => x.left.2) h).symm

theorem outer_image_order : orderOf (m.inclusion m.outer) = 2 := by
  apply orderOf_eq_prime_iff.mpr
  refine ⟨by rw [← map_pow, m.outer_sq, map_one], ?_⟩
  intro h
  rcases (m.kernel _).mp h with h | h
  all_goals
    have he : (Multiplicative.ofAdd (1 : ZMod 2)) = 1 :=
      congrArg (fun x : m.Domain => x.right) h
    exact (by decide : (Multiplicative.ofAdd (1 : ZMod 2)) ≠ 1) he

theorem paired_image_order : orderOf (m.inclusion m.paired) = 2 := by
  apply orderOf_eq_prime_iff.mpr
  refine ⟨by rw [← map_pow, m.paired_sq, m.diagonal_mem_kernel], ?_⟩
  intro h
  rcases (m.kernel _).mp h with h | h
  · exact quarterTurn_ne_one p (congrArg (fun x : m.Domain => x.left.1) h)
  · exact quarterTurn_ne_neg_one p (congrArg (fun x : m.Domain => x.left.1) h)

end LocalModel
end Atlas.G2.MultiplierOrdinary.OddTwoPrimary

end
