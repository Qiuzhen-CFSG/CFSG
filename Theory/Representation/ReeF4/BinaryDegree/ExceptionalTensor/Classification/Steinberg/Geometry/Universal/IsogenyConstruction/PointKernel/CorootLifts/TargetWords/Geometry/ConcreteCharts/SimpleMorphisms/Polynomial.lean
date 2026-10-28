module

public import Theory.AlgebraicGroup.RootSystems.AlgebraicGroups.F4IntegralChevalleyRepresentation

/-!
# Polynomial matrices for the simple F4 rank-one actions

A root string with `n + 1` roots carries the degree-`n` divided-power action of a
2-by-2 matrix. The Cartan columns are coupled to the two opposite root lines;
all their coefficients are integral, so specialization never divides by two.

This module defines the polynomial candidate and its coefficient naturality.
Its multiplicative law and agreement with the literal integral root curves
are separate proof obligations. Source: the integral construction behind
GLS3, Remarks 1.12.10 and the parametrizations in 1.12.1.
-/

@[expose] public section
noncomputable section
open scoped BigOperators
open Theory.AlgebraicGroup.StandardRootSystem

namespace Theory.AlgebraicGroup.F4Chevalley.ConcreteCharts

/-- A divided-power matrix entry, with input position `q` and output position `r`.
Positions are counted from the bottom of the root string. -/
def dividedStringEntry {S : Type*} [CommRing S]
    (n q r : ℕ) (A : Matrix (Fin 2) (Fin 2) S) : S :=
  ∑ s ∈ Finset.range (q + 1), ∑ t ∈ Finset.range (n - q + 1),
    if s + t = r then
      (r.choose s : S) * ((n - r).choose (q - s) : S) *
        A 0 0 ^ s * A 1 0 ^ (q - s) * A 0 1 ^ t * A 1 1 ^ (n - q - t)
    else 0

/-- Divided-power coefficients commute with every change of coefficient ring. -/
lemma dividedStringEntry_map {S T : Type*} [CommRing S] [CommRing T]
    (f : S →+* T) (n q r : ℕ) (A : Matrix (Fin 2) (Fin 2) S) :
    dividedStringEntry n q r (A.map f) = f (dividedStringEntry n q r A) := by
  classical
  simp [dividedStringEntry, map_sum, apply_ite]

local instance simpleMorphismsPolynomialNeg : InvolutiveNeg Root := typeF4RootPairing.indexNeg

/-- The explicit polynomial candidate on the integral Cartan-plus-root basis.
The terms involving `A 0 1 * A 1 0` retain the integral Cartan coupling. -/
def simpleSL2Matrix {S : Type*} [CommRing S]
    (i : typeF4RootPairing_base.support) (A : Matrix (Fin 2) (Fin 2) S) :
    Matrix BasisIndex BasisIndex S := by
  classical
  let C (j : typeF4RootPairing_base.support) : S :=
    (|typeF4RootPairing_base.cartanMatrix i j| : ℤ)
  exact Matrix.of fun row col => match row, col with
  | Sum.inl l, Sum.inl j =>
      (if l = j then 1 else 0) + (if l = i then C j * A 0 1 * A 1 0 else 0)
  | Sum.inr r, Sum.inl j =>
      (if r = (i : Root) then C j * A 0 0 * A 0 1 else 0) +
        (if r = (-i : Root) then C j * A 1 0 * A 1 1 else 0)
  | Sum.inl l, Sum.inr j =>
      if l = i then
        (if j = (i : Root) then A 0 0 * A 1 0 else 0) +
          (if j = (-i : Root) then A 0 1 * A 1 1 else 0)
      else 0
  | Sum.inr r, Sum.inr j =>
      if j = (i : Root) then
        (if r = (i : Root) then A 0 0 ^ 2 else 0) +
          (if r = (-i : Root) then A 1 0 ^ 2 else 0)
      else if j = (-i : Root) then
        (if r = (i : Root) then A 0 1 ^ 2 else 0) +
          (if r = (-i : Root) then A 1 1 ^ 2 else 0)
      else
        let q := typeF4RootPairing.chainBotCoeff i j
        let p := typeF4RootPairing.chainTopCoeff i j
        let s := typeF4RootPairing.chainBotCoeff i r
        if typeF4RootPairing.root r + q • typeF4RootPairing.root i =
            typeF4RootPairing.root j + s • typeF4RootPairing.root i then
          dividedStringEntry (q + p) q s A
        else 0

/-- The entire candidate is polynomial over the integers. -/
lemma simpleSL2Matrix_map {S T : Type*} [CommRing S] [CommRing T]
    (f : S →+* T) (i : typeF4RootPairing_base.support)
    (A : Matrix (Fin 2) (Fin 2) S) :
    simpleSL2Matrix i (A.map f) = (simpleSL2Matrix i A).map f := by
  classical
  ext (r | r) (j | j) <;>
    simp only [simpleSL2Matrix, Matrix.map_apply, Matrix.of_apply] <;>
    simp only [map_add, map_mul, map_pow, map_intCast, map_zero, map_one,
      apply_ite f, dividedStringEntry_map]

/-- The divided-power identity matrix, including strings of length zero. -/
lemma dividedStringEntry_one {S : Type*} [CommRing S] (n q r : ℕ) :
    dividedStringEntry n q r (1 : Matrix (Fin 2) (Fin 2) S) =
      if q = r then 1 else 0 := by
  classical
  unfold dividedStringEntry
  rw [Finset.sum_eq_single q]
  · rw [Finset.sum_eq_single 0]
    · by_cases h : q = r
      · subst r
        simp
      · simp [h]
    · intro t ht hne
      simp [zero_pow hne]
    · simp
  · intro s hs hne
    have hpos : q - s ≠ 0 := by
      have := Finset.mem_range.mp hs
      omega
    apply Finset.sum_eq_zero
    intro t ht
    simp [zero_pow hpos]
  · simp

/-- The polynomial candidate fixes the identity without any matrix-law premise. -/
lemma simpleSL2Matrix_one {S : Type*} [CommRing S]
    (i : typeF4RootPairing_base.support) :
    simpleSL2Matrix i (1 : Matrix (Fin 2) (Fin 2) S) = 1 := by
  classical
  ext (r | r) (j | j)
  · simp [simpleSL2Matrix, Matrix.one_apply]
  · simp [simpleSL2Matrix]
  · simp [simpleSL2Matrix]
  · by_cases hj : j = (i : Root)
    · subst j
      simp [simpleSL2Matrix, Matrix.one_apply]
    by_cases hjn : j = typeF4RootPairing.reflectionPerm i i
    · subst j
      simp [simpleSL2Matrix, Matrix.one_apply, hj]
    by_cases hrj : r = j
    · subst r
      simp [simpleSL2Matrix, hj, hjn, dividedStringEntry_one]
    have hneq (h : typeF4RootPairing.root r +
        typeF4RootPairing.chainBotCoeff i j • typeF4RootPairing.root i =
        typeF4RootPairing.root j +
        typeF4RootPairing.chainBotCoeff i r • typeF4RootPairing.root i) :
        typeF4RootPairing.chainBotCoeff i j ≠ typeF4RootPairing.chainBotCoeff i r := by
      intro heq
      rw [heq] at h
      exact hrj (typeF4RootPairing.root.injective (add_right_cancel h))
    simp [simpleSL2Matrix, hj, hjn, dividedStringEntry_one, hrj]
    intro h hq
    exact (hneq (by simpa using h) hq).elim

end Theory.AlgebraicGroup.F4Chevalley.ConcreteCharts
