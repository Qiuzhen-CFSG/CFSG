module

public import Theory.SpecificGroups.ReeF4.ExceptionalEndomorphism.WordRelations.Coordinates
public import Theory.SpecificGroups.ReeF4.ExceptionalEndomorphism.RootDuality.Negation

/-!
# Sparse coordinates for the simple-root comparison

Multiplication by the quotient-to-ideal map selects long rows on the source
and short columns on the target. These formulas turn the divided-power
intertwining identities into comparisons of individual coefficients, and turn
the required vanishing identities into row or column support conditions.

The map also respects opposition, which fixes the Cartan coordinates and
negates root indices. This is the coordinate symmetry used to transfer the
positive simple-root computations to the negative ones. The representation
and root convention are those of `RootDuality` and `Coordinates`.
-/

public section

namespace ReeF4.WordRelations

open Theory.AlgebraicGroup.StandardRootSystem
open scoped Classical Matrix

-- A unique name permits importing this extension together with `Intertwining.Transport`.
noncomputable local instance simpleCoordinateRootsFintype : Fintype typeF4Roots :=
  Fintype.ofFinite _

theorem quotientToIdeal_mul {K : Type*} [Semiring K]
    (A : Matrix Coordinate Coordinate K) (i j : Coordinate) :
    (quotientToIdeal (K := K) * A) i j =
      if IsShortCoordinate i then A (coordinatePermutation i) j else 0 := by
  classical
  have heq (k : Coordinate) : i = coordinatePermutation k ↔ k = coordinatePermutation i := by
    constructor
    · intro h
      rw [h, coordinatePermutation_involutive k]
    · intro h
      rw [h, coordinatePermutation_involutive i]
  rw [Matrix.mul_apply, Finset.sum_eq_single (coordinatePermutation i)]
  · by_cases hi : IsShortCoordinate i <;>
      simp [quotientToIdeal_apply, coordinatePermutation_short_iff, hi,
        coordinatePermutation_involutive i]
  · intro k _ hk
    rw [quotientToIdeal_apply]
    by_cases hs : IsShortCoordinate k <;> simp [hs, heq, hk]
  · simp

theorem quotientToIdeal_mul_eq_zero_iff {K : Type*} [Semiring K]
    (A : Matrix Coordinate Coordinate K) :
    quotientToIdeal * A = 0 ↔
      ∀ i, ¬IsShortCoordinate i → ∀ j, A i j = 0 := by
  constructor
  · intro h i hi j
    have hc := congrFun (congrFun h (coordinatePermutation i)) j
    rw [quotientToIdeal_mul, if_pos ((coordinatePermutation_short_iff i).mpr hi),
      coordinatePermutation_involutive i] at hc
    exact hc
  · intro h
    ext i j
    rw [quotientToIdeal_mul]
    by_cases hi : IsShortCoordinate i
    · rw [if_pos hi]
      exact h _ (by simpa only [coordinatePermutation_short_iff, not_not] using hi) j
    · exact if_neg hi

theorem mul_quotientToIdeal_eq_zero_iff {K : Type*} [Semiring K]
    (A : Matrix Coordinate Coordinate K) :
    A * quotientToIdeal = 0 ↔
      ∀ j, IsShortCoordinate j → ∀ i, A i j = 0 := by
  constructor
  · intro h j hj i
    have hc := congrFun (congrFun h i) (coordinatePermutation j)
    have hn : ¬IsShortCoordinate (coordinatePermutation j) := by
      simpa only [coordinatePermutation_short_iff, not_not] using hj
    rw [mul_quotientToIdeal, if_neg hn, coordinatePermutation_involutive j] at hc
    exact hc
  · intro h
    ext i j
    rw [mul_quotientToIdeal]
    by_cases hj : IsShortCoordinate j
    · exact if_pos hj
    · rw [if_neg hj]
      exact h _ ((coordinatePermutation_short_iff j).mpr hj) i

/-- Opposition fixes Cartan coordinates and exchanges opposite root coordinates. -/
noncomputable def coordinateOpposition : Equiv.Perm Coordinate := by
  let := typeF4RootPairing.indexNeg
  exact Equiv.sumCongr (Equiv.refl _) (Equiv.neg _)

@[simp] theorem coordinateOpposition_inl (i : typeF4RootPairing_base.support) :
    coordinateOpposition (Sum.inl i) = Sum.inl i := by rfl

@[simp] theorem coordinateOpposition_inr (r : typeF4Roots) :
    letI := typeF4RootPairing.indexNeg
    coordinateOpposition (Sum.inr r) = Sum.inr (-r) := by rfl

theorem coordinateOpposition_involutive : Function.Involutive coordinateOpposition := by
  let := typeF4RootPairing.indexNeg
  rintro (i | r)
  · rfl
  · simp only [coordinateOpposition_inr, neg_neg]

theorem coordinateOpposition_short_iff (i : Coordinate) :
    IsShortCoordinate (coordinateOpposition i) ↔ IsShortCoordinate i := by
  rcases i with i | r
  · rfl
  · exact isShortRoot_neg_iff r

theorem coordinatePermutation_opposition (i : Coordinate) :
    coordinatePermutation (coordinateOpposition i) =
      coordinateOpposition (coordinatePermutation i) := by
  let := typeF4RootPairing.indexNeg
  rcases i with i | r
  · simp only [coordinateOpposition_inl, coordinatePermutation_inl]
  · simp only [coordinateOpposition_inr, coordinatePermutation_inr,
      exceptionalRootPermutation_neg]

theorem quotientToIdeal_opposition {K : Type*} [Zero K] [One K] (i j : Coordinate) :
    quotientToIdeal (K := K) (coordinateOpposition i) (coordinateOpposition j) =
      quotientToIdeal i j := by
  simp only [quotientToIdeal_apply, coordinateOpposition_short_iff,
    coordinatePermutation_opposition, Equiv.apply_eq_iff_eq]

end ReeF4.WordRelations
