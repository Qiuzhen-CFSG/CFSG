module
public import Theory.SpecificGroups.Triality.SimplyConnectedModel.PinningTorus.RegularRoots.RootSupport.NaturalCoefficients.Coefficients

/-!
# Detecting additive curves between distinct hyperbolic pairs

If all entries between different hyperbolic planes vanish, each isotropic
column identity is a product of its two entries. The diagonal entry has value
one at zero, so the polynomial domain property kills the opposite entry.
The resulting diagonal matrix squares to one in characteristic two, hence is
one. Faithfulness of the natural Spin action then contradicts injectivity of
the additive curve.

Source: the natural representation of GLS3 §§1.10 and 1.14,
`refs/KGroup/GLS3/Chapter1.tex`. This argument uses no differential.
-/

public section
noncomputable section
namespace Triality.SimplyConnected.Pinning.NaturalCoefficients
open Theory Theory.AlgebraicGroup
open scoped BigOperators
universe u
variable (k : Type u) [Field k] [IsAlgClosed k]

/-- Vanishing between distinct pairs forces every off-diagonal polynomial to vanish. -/
lemma polynomial_offDiagonal_zero_of_pairs
    (f : AlgebraicGroup.Morphism (KPlus k) (groupVariety k))
    (h : ∀ p q : Index, pairIndex p ≠ pairIndex q → polynomial k f p q = 0) :
    ∀ p q : Index, p ≠ q → polynomial k f p q = 0 := by
  have hop (i : Fin 4) : polynomial k f (.inl i) (.inr i) = 0 ∧
      polynomial k f (.inr i) (.inl i) = 0 := by
    have hc (q : Index) (hq : pairIndex q = i) :
        polynomial k f (.inl i) q * polynomial k f (.inr i) q = 0 := by
      have hsum := polynomial_isotropic_column k f q
      rw [Finset.sum_eq_single i] at hsum
      · exact hsum
      · intro j _ hji
        rw [h (.inl j) q (by change j ≠ pairIndex q; rw [hq]; exact hji), zero_mul]
      · simp
    constructor
    · exact (mul_eq_zero.mp (hc (.inr i) rfl)).resolve_right
        (polynomial_diagonal_ne_zero k f (.inr i))
    · exact (mul_eq_zero.mp (hc (.inl i) rfl)).resolve_left
        (polynomial_diagonal_ne_zero k f (.inl i))
  intro p q hpq
  by_cases hi : pairIndex p = pairIndex q
  · cases p with
    | inl i =>
      cases q with
      | inl j => exact (hpq (congrArg Sum.inl hi)).elim
      | inr j => cases hi; exact (hop i).1
    | inr i =>
      cases q with
      | inl j => cases hi; exact (hop i).2
      | inr j => exact (hpq (congrArg Sum.inr hi)).elim
  · exact h p q hi

variable [CharP k 2]
/-- A diagonal additive curve is trivial in characteristic two. -/
lemma curve_eq_one_of_offDiagonal_zero
    (f : AlgebraicGroup.Morphism (KPlus k) (groupVariety k))
    (h : ∀ p q : Index, p ≠ q → polynomial k f p q = 0) (a : k) :
    f.onPoints (kPlusPoint a) = 1 := by
  classical
  let d : Index → k := fun p => (polynomial k f p p).eval a
  have hd : pointMatrix k (f.onPoints (kPlusPoint a)) = Matrix.diagonal d := by
    ext p q
    rw [← polynomial_eval_matrix]
    by_cases hpq : p = q
    · subst q; simp [d]
    · simp [h p q hpq, Matrix.diagonal_apply_ne _ hpq]
  have hsq : pointMatrix k (f.onPoints (kPlusPoint a)) *
      pointMatrix k (f.onPoints (kPlusPoint a)) = 1 := by
    rw [← pointMatrix_mul, curve_square, pointMatrix_one]
  have hd1 (p : Index) : d p = 1 := by
    apply CharTwo.sq_injective
    have he := congrFun (congrFun hsq p) p
    rw [hd, Matrix.diagonal_mul_diagonal] at he
    simpa [pow_two] using he
  apply pointMatrix_injective k
  rw [hd, pointMatrix_one]
  rw [show d = fun _ => 1 from funext hd1]
  exact Matrix.diagonal_one

/-- An injective additive curve has a nonzero entry between different hyperbolic planes. -/
lemma exists_polynomial_ne_zero_distinct_pairs
    (f : AlgebraicGroup.Morphism (KPlus k) (groupVariety k))
    (hf : Function.Injective f.onPoints) :
    ∃ p q : Index, pairIndex p ≠ pairIndex q ∧ polynomial k f p q ≠ 0 := by
  classical
  by_contra hn
  push Not at hn
  have hz := curve_eq_one_of_offDiagonal_zero k f
    (polynomial_offDiagonal_zero_of_pairs k f hn)
  have he := hf ((hz 1).trans (hz 0).symm)
  have h10 : (1 : k) = 0 := congrArg (fun x : Variety.Point (KPlus k) => x.val PUnit.unit) he
  exact one_ne_zero h10

end Triality.SimplyConnected.Pinning.NaturalCoefficients
