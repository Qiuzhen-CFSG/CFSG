module

public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.RadicalOrders.Coordinates

/-!
# Scalar solutions for Ree root blocks

Write `f(t) = t^(2^m)` and `g(t) = t^(2^(m+1))`. These field maps
are inverse even at `m = 0`. A commuting dual pair contributes one free
scalar. For a B₂ block ordered as long root, short root, their sum, and
long root plus twice the short root, collection contributes the terms
`g(b) * f(a)` and `g(b) * f(a)^2`. Its fixed tuples are exactly
`(a, f(a), c, g(c) + a*g(a))`.

This module solves those polynomial equations. Identifying this polynomial
map with the actual matrix twist is a separate obligation, as is partitioning
the three supports into these blocks. It is not a fixed-subgroup order theorem.
Source: the root calculation underlying Aschbacher–Smith F.1.12(I)(5),
printed p.263 (PDF p.274) of `refs/quasithin.pdf`.
-/

@[expose] public section
noncomputable section

namespace ReeF4.Parabolics.RadicalCoordinates.FixedCoordinates

def halfFrobenius (m : ℕ) : CoefficientField m →+* CoefficientField m :=
  iterateFrobenius (CoefficientField m) 2 m

theorem halfFrobenius_titsEnd (m : ℕ) (x : CoefficientField m) :
    halfFrobenius m (titsEnd m x) = x := by
  change (x ^ (2 ^ (m + 1))) ^ (2 ^ m) = x
  rw [← pow_mul, ← pow_add]
  convert field_pow m x using 1
  congr 2
  omega

theorem titsEnd_halfFrobenius (m : ℕ) (x : CoefficientField m) :
    titsEnd m (halfFrobenius m x) = x := by
  change (x ^ (2 ^ m)) ^ (2 ^ (m + 1)) = x
  rw [← pow_mul, ← pow_add]
  convert field_pow m x using 1
  congr 2
  omega

theorem halfFrobenius_sq (m : ℕ) (x : CoefficientField m) :
    halfFrobenius m x ^ 2 = titsEnd m x := by
  change (x ^ (2 ^ m)) ^ 2 = x ^ (2 ^ (m + 1))
  rw [← pow_mul, pow_succ]

def pairTwist (m : ℕ) (t : Fin 2 → CoefficientField m) :
    Fin 2 → CoefficientField m :=
  ![titsEnd m (t 1), halfFrobenius m (t 0)]

def quartetTwist (m : ℕ) (t : Fin 4 → CoefficientField m) :
    Fin 4 → CoefficientField m :=
  ![titsEnd m (t 1), halfFrobenius m (t 0),
    titsEnd m (t 1) * halfFrobenius m (t 0) + halfFrobenius m (t 3),
    titsEnd m (t 1) * halfFrobenius m (t 0) ^ 2 + titsEnd m (t 2)]

def pairSolution (m : ℕ) (a : CoefficientField m) : Fin 2 → CoefficientField m :=
  ![a, halfFrobenius m a]

def quartetSolution (m : ℕ) (a c : CoefficientField m) :
    Fin 4 → CoefficientField m :=
  ![a, halfFrobenius m a, c, titsEnd m c + a * titsEnd m a]

theorem pairSolution_fixed (m : ℕ) (a : CoefficientField m) :
    pairTwist m (pairSolution m a) = pairSolution m a := by
  ext i
  fin_cases i <;> simp [pairTwist, pairSolution, titsEnd_halfFrobenius]

theorem quartetSolution_fixed (m : ℕ) (a c : CoefficientField m) :
    quartetTwist m (quartetSolution m a c) = quartetSolution m a c := by
  ext i
  fin_cases i <;>
    simp [quartetTwist, quartetSolution, titsEnd_halfFrobenius,
      halfFrobenius_titsEnd, map_add, map_mul, halfFrobenius_sq,
      mul_comm, add_comm, add_left_comm, CharTwo.add_self_eq_zero]

theorem pairTwist_fixed_iff (m : ℕ) (t : Fin 2 → CoefficientField m) :
    pairTwist m t = t ↔ t = pairSolution m (t 0) := by
  constructor
  · intro h
    ext i
    fin_cases i
    · rfl
    · exact (congrFun h 1).symm
  · intro h
    rw [h]
    exact pairSolution_fixed m _

theorem quartetTwist_fixed_iff (m : ℕ) (t : Fin 4 → CoefficientField m) :
    quartetTwist m t = t ↔ t = quartetSolution m (t 0) (t 2) := by
  constructor
  · intro h
    have hb : halfFrobenius m (t 0) = t 1 := congrFun h 1
    have hd := congrFun h 3
    change titsEnd m (t 1) * halfFrobenius m (t 0) ^ 2 + titsEnd m (t 2) = t 3 at hd
    rw [← hb, titsEnd_halfFrobenius, halfFrobenius_sq] at hd
    ext i
    fin_cases i
    · rfl
    · exact hb.symm
    · rfl
    · change t 3 = titsEnd m (t 2) + t 0 * titsEnd m (t 0)
      simpa only [add_comm] using hd.symm
  · intro h
    rw [h]
    exact quartetSolution_fixed m _ _

def pairFixedEquiv (m : ℕ) :
    {t : Fin 2 → CoefficientField m // pairTwist m t = t} ≃ CoefficientField m where
  toFun t := t.val 0
  invFun a := ⟨pairSolution m a, pairSolution_fixed m a⟩
  left_inv t := Subtype.ext ((pairTwist_fixed_iff m t.val).mp t.property).symm
  right_inv _ := rfl

def quartetFixedEquiv (m : ℕ) :
    {t : Fin 4 → CoefficientField m // quartetTwist m t = t} ≃
      (Fin 2 → CoefficientField m) where
  toFun t := ![t.val 0, t.val 2]
  invFun t := ⟨quartetSolution m (t 0) (t 1), quartetSolution_fixed m _ _⟩
  left_inv t := Subtype.ext ((quartetTwist_fixed_iff m t.val).mp t.property).symm
  right_inv t := by ext i; fin_cases i <;> rfl

end ReeF4.Parabolics.RadicalCoordinates.FixedCoordinates
