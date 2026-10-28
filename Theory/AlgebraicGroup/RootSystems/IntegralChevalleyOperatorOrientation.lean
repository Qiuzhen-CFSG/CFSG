module

public import Theory.AlgebraicGroup.RootSystems.IntegralAllRootOperators

/-!
# Integral Chevalley operator orientations

The sign with which a Tits word acts on Geck's carrier root vector does not by itself determine
the conjugation sign of the corresponding Chevalley operator.  Already in rank one, the empty
positive-simple route and the reflected negative-simple route have equal endpoint and equal raw
carrier sign, while their degree-one divided powers differ by `-1`.  Adjacent simple roots give
the analogous discrepancy between the two one-step routes to their sum.

This module supplies the missing operator normalization without an irreducibility hypothesis.
The support graph of a finite crystallographic root system is acyclic: positive-definite Cartan
symmetrization and the rank-two Cartan classification give a forest, including in the reducible
case.  Its canonical two-colouring yields a simple-root sign which reverses across every Cartan
edge; negative polarity reverses it once more.

Consequently a route from a signed simple root has orientation
`titsWordSign * signedSimpleOperatorOrientation`.  Two routes to one root line are compared by
the product of their route orientations, and divided powers use the corresponding power of this
scalar.  This is only the normalization API: route-line equality itself is proved in the next
layer from the integral Tits, Matsumoto, and root-route results.  The construction uses no Borel
geometry, algebraic closure, or decomposition into irreducible components.
-/

namespace RootPairing.IntegralGeckConstruction

open Theory.AlgebraicGroup

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

noncomputable section

variable {ι R M N : Type*} [Field R] [CharZero R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {P : RootPairing ι R M N} [P.IsRootSystem]
  [P.IsCrystallographic] [P.IsReduced]
  {b : P.Base} [Fintype ι] [DecidableEq ι]

/-- The unoriented Cartan support graph whose edges join interacting simple roots. -/
def operatorOrientationGraph : SimpleGraph b.support :=
  SimpleGraph.fromRel fun i j => b.cartanMatrix i j ≠ 0

/-- The Cartan support graph of a finite root system is a forest, component by component. -/
theorem operatorOrientationGraph_isAcyclic :
    (operatorOrientationGraph (b := b)).IsAcyclic := by
  obtain ⟨d, _, hd⟩ := b.exists_cartanMatrix_diagaonal_mul_posDef
  exact Theory.AlgebraicGroup.cartanSupport_isAcyclic b.cartanMatrix d
    b.cartanMatrix_apply_same (Theory.AlgebraicGroup.base_rankTwo_cartanClassification b) hd

/-- A canonical two-colouring of the Cartan support forest. -/
noncomputable def simpleOperatorColoring :
    (operatorOrientationGraph (b := b)).Coloring (Fin 2) :=
  (operatorOrientationGraph_isAcyclic (b := b)).coloringTwo

/-- The operator orientation on simple roots obtained by sending the two colours to `1` and `-1`.

This is an orientation of Chevalley operators, not the sign with which a Tits word acts on the
carrier root-vector basis. -/
noncomputable def simpleOperatorOrientation (i : b.support) : ℤ :=
  if simpleOperatorColoring (b := b) i = 0 then 1 else -1

theorem simpleOperatorOrientation_sq (i : b.support) :
    simpleOperatorOrientation (b := b) i * simpleOperatorOrientation (b := b) i = 1 := by
  simp only [simpleOperatorOrientation]
  split <;> norm_num

theorem simpleOperatorOrientation_mul_eq_neg_one_of_cartan_ne_zero
    (i j : b.support) (hij : i ≠ j) (hcartan : b.cartanMatrix i j ≠ 0) :
    simpleOperatorOrientation (b := b) i * simpleOperatorOrientation (b := b) j = -1 := by
  have hadj : (operatorOrientationGraph (b := b)).Adj i j :=
    (SimpleGraph.fromRel_adj _ _ _).2 ⟨hij, Or.inl hcartan⟩
  have hcolor := (simpleOperatorColoring (b := b)).valid hadj
  simp only [simpleOperatorOrientation]
  by_cases hi : simpleOperatorColoring (b := b) i = 0
  · have hj : simpleOperatorColoring (b := b) j ≠ 0 := by
      intro hj
      exact hcolor (hi.trans hj.symm)
    simp [hi, hj]
  · have hj : simpleOperatorColoring (b := b) j = 0 := by
      by_contra hj
      apply hcolor
      rw [Fin.eq_one_of_ne_zero _ hi, Fin.eq_one_of_ne_zero _ hj]
    simp [hi, hj]

/-- Existence and coherence of a simple-root operator orientation on every finite root system. -/
theorem simpleOperatorOrientation_spec :
    (∀ i : b.support,
      simpleOperatorOrientation (b := b) i * simpleOperatorOrientation (b := b) i = 1) ∧
    (∀ i j : b.support, i ≠ j → b.cartanMatrix i j ≠ 0 →
      simpleOperatorOrientation (b := b) i * simpleOperatorOrientation (b := b) j = -1) :=
  ⟨simpleOperatorOrientation_sq, simpleOperatorOrientation_mul_eq_neg_one_of_cartan_ne_zero⟩

/-- Operator orientation on a signed simple root. Negative polarity reverses the simple sign. -/
noncomputable def signedSimpleOperatorOrientation (positive : Bool) (i : b.support) : ℤ :=
  if positive then simpleOperatorOrientation (b := b) i
  else -simpleOperatorOrientation (b := b) i

@[simp] theorem signedSimpleOperatorOrientation_true (i : b.support) :
    signedSimpleOperatorOrientation (b := b) true i = simpleOperatorOrientation (b := b) i := by
  simp [signedSimpleOperatorOrientation]

@[simp] theorem signedSimpleOperatorOrientation_false (i : b.support) :
    signedSimpleOperatorOrientation (b := b) false i = -simpleOperatorOrientation (b := b) i := by
  simp [signedSimpleOperatorOrientation]

theorem signedSimpleOperatorOrientation_neg (i : b.support) :
    signedSimpleOperatorOrientation (b := b) false i =
      -signedSimpleOperatorOrientation (b := b) true i := by
  simp

theorem signedSimpleOperatorOrientation_sq (positive : Bool) (i : b.support) :
    signedSimpleOperatorOrientation (b := b) positive i *
      signedSimpleOperatorOrientation (b := b) positive i = 1 := by
  cases positive <;> simp [simpleOperatorOrientation_sq]

theorem signedSimpleOperatorOrientation_mul_self_opposite (i : b.support) :
    signedSimpleOperatorOrientation (b := b) true i *
      signedSimpleOperatorOrientation (b := b) false i = -1 := by
  simp [simpleOperatorOrientation_sq]

theorem signedSimpleOperatorOrientation_mul_of_cartan_ne_zero
    (positive negative : Bool) (i j : b.support) (hij : i ≠ j)
    (hcartan : b.cartanMatrix i j ≠ 0) :
    signedSimpleOperatorOrientation (b := b) positive i *
        signedSimpleOperatorOrientation (b := b) negative j =
      if positive = negative then -1 else 1 := by
  cases positive <;> cases negative <;>
    simp [simpleOperatorOrientation_mul_eq_neg_one_of_cartan_ne_zero i j hij hcartan]

/-- The corrected orientation of a route from a signed simple root.

The first factor is the sign of the carrier root vector under the Tits word. The second factor
converts the signed simple carrier line to its Chevalley operator orientation. -/
noncomputable def simpleRouteOperatorOrientation
    (positive : Bool) (word : List b.support) (i : b.support) : ℤ := by
  classical
  letI := P.indexNeg
  exact titsWordSign (P := P) word (if positive then (i : ι) else -(i : ι)) *
    signedSimpleOperatorOrientation (b := b) positive i

/-- The corrected scalar comparing two signed-simple routes to the same root line. -/
noncomputable def simpleRouteLineComparisonSign
    (positive : Bool) (word : List b.support) (i : b.support)
    (positive' : Bool) (word' : List b.support) (i' : b.support) : ℤ :=
  simpleRouteOperatorOrientation (P := P) positive word i *
    simpleRouteOperatorOrientation (P := P) positive' word' i'

private theorem titsWordSign_mul_self_orientation (word : List b.support) (j : ι) :
    titsWordSign (P := P) word j * titsWordSign (P := P) word j = 1 := by
  induction word with
  | nil => simp [titsWordSign]
  | cons i word ih =>
      simp only [titsWordSign]
      rw [mul_mul_mul_comm, ih]
      simp [← pow_add, ← two_mul]

theorem simpleRouteOperatorOrientation_sq
    (positive : Bool) (word : List b.support) (i : b.support) :
    simpleRouteOperatorOrientation (P := P) positive word i *
      simpleRouteOperatorOrientation (P := P) positive word i = 1 := by
  classical
  letI := P.indexNeg
  unfold simpleRouteOperatorOrientation
  rw [mul_mul_mul_comm, titsWordSign_mul_self_orientation,
    signedSimpleOperatorOrientation_sq]
  norm_num

theorem simpleRouteLineComparisonSign_sq
    (positive : Bool) (word : List b.support) (i : b.support)
    (positive' : Bool) (word' : List b.support) (i' : b.support) :
    simpleRouteLineComparisonSign (P := P) positive word i positive' word' i' *
      simpleRouteLineComparisonSign (P := P) positive word i positive' word' i' = 1 := by
  unfold simpleRouteLineComparisonSign
  rw [mul_mul_mul_comm, simpleRouteOperatorOrientation_sq,
    simpleRouteOperatorOrientation_sq]
  norm_num

/-- The corrected scalar is `-1` for the rank-one polarity routes from the counterexample. -/
theorem simpleRouteLineComparisonSign_empty_reflected_negative (i : b.support) :
    simpleRouteLineComparisonSign (P := P) true [] i false [i] i = -1 := by
  classical
  letI := P.indexNeg
  have hdep : ¬ LinearIndependent R ![P.root i, P.root i] := by
    rw [LinearIndependent.pair_iff]
    intro h
    have hone := h 1 (-1) (by simp)
    exact one_ne_zero hone.1
  have htop : P.chainTopCoeff (i : ι) i = 0 :=
    P.chainTopCoeff_eq_zero_iff.mpr (Or.inl hdep)
  simp [simpleRouteLineComparisonSign, simpleRouteOperatorOrientation, titsWordSign,
    reflectionWord, htop, simpleOperatorOrientation_sq]

/-- The corrected scalar is `-1` for the two adjacent positive one-step routes. -/
theorem simpleRouteLineComparisonSign_adjacent_positive
    (i j : b.support) (hij : i ≠ j) (hcartan : b.cartanMatrix i j ≠ 0) :
    simpleRouteLineComparisonSign (P := P) true [i] j true [j] i = -1 := by
  have hbotij : P.chainBotCoeff (i : ι) j = 0 :=
    RootPairing.Base.chainBotCoeff_eq_zero
  have hbotji : P.chainBotCoeff (j : ι) i = 0 :=
    RootPairing.Base.chainBotCoeff_eq_zero
  simp only [simpleRouteLineComparisonSign, simpleRouteOperatorOrientation, if_true,
    signedSimpleOperatorOrientation_true, titsWordSign, reflectionWord,
    hbotij, hbotji, pow_zero, one_mul]
  rw [mul_comm]
  exact simpleOperatorOrientation_mul_eq_neg_one_of_cartan_ne_zero i j hij hcartan

end

end

end RootPairing.IntegralGeckConstruction
