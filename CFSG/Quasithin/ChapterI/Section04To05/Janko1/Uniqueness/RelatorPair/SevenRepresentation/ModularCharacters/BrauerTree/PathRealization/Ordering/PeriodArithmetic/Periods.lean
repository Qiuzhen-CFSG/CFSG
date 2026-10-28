module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Uniqueness.RelatorPair.SevenRepresentation.ModularCharacters.BrauerTree.PathRealization.Ordering.Arithmetic
public import Mathlib.RingTheory.RootsOfUnity.Complex
public import Mathlib.Tactic.LinearCombination

/-!
# Multiplication and reality of the literal J₁ periods

The geometric sums of primitive fifth and nineteenth roots vanish. Explicit
polynomial identities give the multiplication rules of the period basis;
conjugation reverses exponents and permutes each period's terms. These are
identities for the literal roots in `ordinaryValue`, without an independence
assumption on the six coordinates used by the tensor certificate.

Source: the ATLAS/GAP CTblLib J1 table (Thomas Breuer, GPL-3.0-or-later),
`ModularCharacters/Source.md`, and `PathRealization/Source.md`.
-/

namespace CFSG.Quasithin.Janko1SevenRepresentation.ModularCharacters.BrauerTree.PathOrdering

private theorem star_root_pow {ζ : ℂ} {n k : ℕ} (hζ : IsPrimitiveRoot ζ n)
    (hn : n ≠ 0) (hk : k ≤ n) : star (ζ ^ k) = ζ ^ (n - k) := by
  have hnorm : ‖ζ ^ k‖ = 1 := by rw [norm_pow, hζ.norm'_eq_one hn, one_pow]
  have hp : ζ ^ (n - k) * ζ ^ k = 1 := by
    rw [← pow_add, Nat.sub_add_cancel hk, hζ.pow_eq_one]
  exact (Complex.inv_eq_conj hnorm).symm.trans (eq_inv_of_mul_eq_one_left hp).symm

/-- The fifth-root quadratic relation, complementary period, and reality. -/
public theorem fifth_period_arithmetic {ζ : ℂ} (hζ : IsPrimitiveRoot ζ 5) :
    let a := ζ + ζ ^ 4
    let b := ζ ^ 2 + ζ ^ 3
    a ^ 2 = 1 - a ∧ b = -1 - a ∧ star a = a ∧ star b = b := by
  dsimp only
  have hg := hζ.geom_sum_eq_zero (by decide : 1 < 5)
  norm_num [Finset.sum_range_succ] at hg
  refine ⟨?_, ?_, ?_, ?_⟩
  · linear_combination (ζ ^ 4 - ζ ^ 3 + 2 * ζ - 1) * hg
  · linear_combination hg
  · have hs : star ζ = ζ ^ 4 := by
      simpa using star_root_pow hζ (by decide) (by decide : 1 ≤ 5)
    rw [star_add, hs, star_root_pow hζ (by decide) (by decide : 4 ≤ 5)]
    norm_num
    ring
  · rw [star_add, star_root_pow hζ (by decide) (by decide : 2 ≤ 5),
      star_root_pow hζ (by decide) (by decide : 3 ≤ 5)]
    norm_num
    ring

/-- The nineteenth-root multiplication rules, remaining period, and reality. -/
public theorem nineteenth_period_arithmetic {ζ : ℂ} (hζ : IsPrimitiveRoot ζ 19) :
    let c := ζ + ζ ^ 7 + ζ ^ 8 + ζ ^ 11 + ζ ^ 12 + ζ ^ 18
    let d := ζ ^ 2 + ζ ^ 3 + ζ ^ 5 + ζ ^ 14 + ζ ^ 16 + ζ ^ 17
    let e := ζ ^ 4 + ζ ^ 6 + ζ ^ 9 + ζ ^ 10 + ζ ^ 13 + ζ ^ 15
    c ^ 2 = 4 - d ∧ c * d = -3 - 2*c - d ∧ d ^ 2 = 5 + c + d ∧
      e = -1 - c - d ∧ star c = c ∧ star d = d ∧ star e = e := by
  dsimp only
  have hg := hζ.geom_sum_eq_zero (by decide : 1 < 19)
  norm_num [Finset.sum_range_succ] at hg
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · linear_combination (ζ ^ 18 - ζ ^ 17 + 2*ζ ^ 12 - 2*ζ ^ 10 + 2*ζ ^ 8 -
      ζ ^ 6 + ζ ^ 5 - ζ ^ 4 - ζ ^ 3 + 2*ζ ^ 2 + 4*ζ - 4) * hg
  · linear_combination (ζ ^ 17 - ζ ^ 15 + ζ ^ 14 - ζ ^ 13 + ζ ^ 11 + ζ ^ 10 -
      ζ ^ 9 + ζ ^ 7 - ζ ^ 4 + ζ ^ 3 - ζ ^ 2 - ζ + 3) * hg
  · linear_combination (ζ ^ 16 + ζ ^ 15 - ζ ^ 14 + ζ ^ 13 - 2*ζ ^ 11 + ζ ^ 10 -
      ζ ^ 9 + 2*ζ ^ 4 + 4*ζ - 5) * hg
  · linear_combination hg
  · have hs : star ζ = ζ ^ 18 := by
      simpa using star_root_pow hζ (by decide) (by decide : 1 ≤ 19)
    simp only [star_add, hs]
    rw [star_root_pow hζ (by decide) (by decide : 7 ≤ 19),
      star_root_pow hζ (by decide) (by decide : 8 ≤ 19),
      star_root_pow hζ (by decide) (by decide : 11 ≤ 19),
      star_root_pow hζ (by decide) (by decide : 12 ≤ 19),
      star_root_pow hζ (by decide) (by decide : 18 ≤ 19)]
    norm_num
    ring
  · simp only [star_add]
    rw [star_root_pow hζ (by decide) (by decide : 2 ≤ 19),
      star_root_pow hζ (by decide) (by decide : 3 ≤ 19),
      star_root_pow hζ (by decide) (by decide : 5 ≤ 19),
      star_root_pow hζ (by decide) (by decide : 14 ≤ 19),
      star_root_pow hζ (by decide) (by decide : 16 ≤ 19),
      star_root_pow hζ (by decide) (by decide : 17 ≤ 19)]
    norm_num
    ring
  · simp only [star_add]
    rw [star_root_pow hζ (by decide) (by decide : 4 ≤ 19),
      star_root_pow hζ (by decide) (by decide : 6 ≤ 19),
      star_root_pow hζ (by decide) (by decide : 9 ≤ 19),
      star_root_pow hζ (by decide) (by decide : 10 ≤ 19),
      star_root_pow hζ (by decide) (by decide : 13 ≤ 19),
      star_root_pow hζ (by decide) (by decide : 15 ≤ 19)]
    norm_num
    ring
end CFSG.Quasithin.Janko1SevenRepresentation.ModularCharacters.BrauerTree.PathOrdering
