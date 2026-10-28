module

public import Theory.SpecificGroups.BabyMonster.Order.LowerBound.ImageSize.RemainingFactors.LargePrimes.Packed

/-!
# From packed word orbits to prime divisors

The action soundness theorem is iterated first along a positive word and then
around its proposed prime-length orbit. A certificate records the closed orbit
of the first coordinate vector and a coordinate moved by one word action.
`prime_dvd_of_certificate` transfers these two concrete checks to the existing
prime-period theorem for the standard matrix subgroup.

The final two lemmas assemble intermediate packed vectors, so certificates can
check each generator action separately. No matrix-order assertion is needed.
Source words and matrices: ATLAS, as documented in `RemainingFactors/source/README.md`.
-/

@[expose] public section

namespace BabyMonster.OrderLowerBound.RemainingFactors.LargePrimes

def wordAction : List Bool → ℕ → ℕ
  | [], x => x
  | b :: w, x => wordAction w (action b x)

theorem wordAction_correct (ha : atlasA ^ 2 = 1) (hb : atlasB ^ 3 = 1)
    (w : List Bool) (x : ℕ) :
    vector (wordAction w x) = Matrix.vecMul (vector x) (positiveWord ha hb w : AtlasMatrix) := by
  induction w generalizing x with
  | nil => exact (Matrix.vecMul_one (vector x)).symm
  | cons b w ih =>
    rw [wordAction, ih, action_correct, Matrix.vecMul_vecMul]
    cases b <;> rfl

theorem wordAction_append (u w : List Bool) (x : ℕ) :
    wordAction (u ++ w) x = wordAction w (wordAction u x) := by
  induction u generalizing x with
  | nil => rfl
  | cons b u ih => exact ih _

def wordIterate (w : List Bool) : ℕ → ℕ → ℕ
  | 0, x => x
  | n+1, x => wordIterate w n (wordAction w x)

theorem wordIterate_correct (ha : atlasA ^ 2 = 1) (hb : atlasB ^ 3 = 1)
    (w : List Bool) (n x : ℕ) :
    vector (wordIterate w n x) =
      Matrix.vecMul (vector x) ((positiveWord ha hb w : AtlasMatrix) ^ n) := by
  induction n generalizing x with
  | zero => simp only [wordIterate, pow_zero, Matrix.vecMul_one]
  | succ n ih =>
    rw [wordIterate, ih, wordAction_correct, Matrix.vecMul_vecMul, pow_succ']

/-- A packed orbit closes after `p` word actions and moves a specified coordinate. -/
structure Certificate (p : ℕ) (w : List Bool) : Prop where
  closes : wordIterate w p 1 = 1
  moves : ∃ j : Fin 4370, bit (wordAction w 1) j.val ≠ bit 1 j.val

theorem prime_dvd_of_certificate (ha : atlasA ^ 2 = 1) (hb : atlasB ^ 3 = 1)
    {p : ℕ} (hp : p.Prime) {w : List Bool} (h : Certificate p w) :
    p ∣ Nat.card (standardImage ha hb) := by
  apply prime_dvd_of_vector_period ha hb (positiveWord ha hb w)
    (positiveWord_mem ha hb w) hp (vector 1)
  · rw [← wordIterate_correct, h.closes]
  · rw [← wordAction_correct]
    obtain ⟨j, hj⟩ := h.moves
    intro he
    exact hj (congrFun he j)

/-- Join generator-action evaluations without evaluating matrix multiplication. -/
theorem wordAction_cons_of_eq {b : Bool} {w : List Bool} {x y z : ℕ}
    (hxy : action b x = y) (hyz : wordAction w y = z) :
    wordAction (b :: w) x = z := by
  simpa only [wordAction, hxy] using hyz

/-- Join whole-word evaluations into an orbit. -/
theorem wordIterate_succ_of_eq {w : List Bool} {n x y z : ℕ}
    (hxy : wordAction w x = y) (hyz : wordIterate w n y = z) :
    wordIterate w (n+1) x = z := by
  simpa only [wordIterate, hxy] using hyz

end BabyMonster.OrderLowerBound.RemainingFactors.LargePrimes
