module

public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.FiniteHighestWeight.FiniteUnipotent.ExtremalGrid.NormSections.PolynomialBounds.Resonance
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.FiniteHighestWeight.FiniteUnipotent.ExtremalGrid.RootCoordinates
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.FiniteHighestWeight.FiniteUnipotent.ExtremalGrid.CellPolynomialSums

/-!
# Mixed-grid coefficient extraction for actual D4 root charts

First substitute the literal triality tuples into a twelve-variable chart
polynomial, then reduce exponents by the finite-field identities. The resulting
six-variable polynomial has exactly the same values on the actual mixed grid
and satisfies the support condition for `hasNonzeroCellSum_of_polynomial`.
The D4 resonance lemma proves its top coefficient equals the original root-top
coefficient whenever the original support lies below 2(q-1)rho. Thus every
collision, including terms whose unreduced exponents exceed the mixed top,
is accounted for. No ordinary root-height bound is substituted for this proof.

The final lemmas apply this calculation to a globally regular covariant function
and to its actual left translates. The chart equation, four root-weight bounds,
and nonzero root-top coefficient remain explicit inputs. Proving them for a
suitable transformation of normalized extremal sections is still required;
this module does not yet construct the requested two-sign norm sections.

Source: Steinberg, `Chapter2St2.tex`, 13.2(d) and 13.3(a), referring to
*Representations of algebraic groups* (1963), Sections 8--9.
-/

@[expose] public noncomputable section
open scoped BigOperators Classical
open MvPolynomial Triality.Standard
namespace Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.ExtremalGrid.PolynomialBounds

variable {k : Type*} [Field k]

def gridPolynomial (P : Parameters) (p : MvPolynomial (Fin 12) k) :
    MvPolynomial MixedIndex k :=
  ∑ d ∈ p.support,
    monomial (reduceExponent (CoordinateField P) (foldExponent P.q d)) (p.coeff d)

lemma eval_gridPolynomial (P : Parameters) (ι : ExtensionField P →+* k)
    (p : MvPolynomial (Fin 12) k) (x : ∀ i, CoordinateField P i) :
    eval (fun i => coordinateEmbedding P ι i (x i)) (gridPolynomial P p) =
      eval (fun i => ι (PositiveCoordinates.expand P (parameterEquiv P x) i)) p := by
  rw [← eval_restrictPolynomial P ι p x]
  simp only [gridPolynomial, restrictPolynomial, map_sum]
  apply Finset.sum_congr rfl
  intro d hd
  exact eval_monomial_reduceExponent (CoordinateField P) (coordinateEmbedding P ι)
    (foldExponent P.q d) (p.coeff d) x

lemma gridPolynomial_support (P : Parameters) (p : MvPolynomial (Fin 12) k) :
    ∀ e ∈ (gridPolynomial P p).support,
      e ≠ PolynomialSums.topExponent (CoordinateField P) →
        ∃ i, e i < Fintype.card (CoordinateField P i)-1 :=
  reduced_sum_support (CoordinateField P) p.support (foldExponent P.q) p.coeff

lemma coeff_gridPolynomial (P : Parameters) (p : MvPolynomial (Fin 12) k)
    (e : MixedIndex →₀ ℕ) :
    (gridPolynomial P p).coeff e =
      ∑ d ∈ p.support with reduceExponent (CoordinateField P) (foldExponent P.q d) = e,
        p.coeff d := by
  simp [gridPolynomial, coeff_sum, coeff_monomial, Finset.sum_filter]

lemma top_coefficient_gridPolynomial (P : Parameters) (p : MvPolynomial (Fin 12) k)
    (hp : ∀ d ∈ p.support, RootWeightBound P.q d) :
    (gridPolynomial P p).coeff (PolynomialSums.topExponent (CoordinateField P)) =
      p.coeff (rootTopExponent P.q) := by
  rw [coeff_gridPolynomial]
  have ht : reduceExponent (CoordinateField P) (foldExponent P.q (rootTopExponent P.q)) =
      PolynomialSums.topExponent (CoordinateField P) := by
    rw [rootTopExponent, foldExponent_rootTop, reduceExponent_top]
  rw [Finset.sum_eq_single (rootTopExponent P.q)]
  · intro d hd hne
    exact False.elim (hne (reduced_fold_top_unique P d (hp d (Finset.mem_filter.mp hd).1)
      (Finset.mem_filter.mp hd).2))
  · intro hn
    apply MvPolynomial.notMem_support_iff.mp
    intro hd
    exact hn (Finset.mem_filter.mpr ⟨hd, ht⟩)

open Theory.AlgebraicGroup MvPolynomial Triality.Standard PositiveCoordinates
open scoped Classical
universe u
variable {k : Type u} [Field k] [CharP k 2]
variable {K : Variety k} [AlgebraicGroup K]

/-- Transport the checked mixed-grid calculation to an actual root chart. -/
theorem hasNonzeroCellSum_of_chart_bound (S : Geometry K) (n : ℕ)
    (R Q : Set S.roots.Root) (chi : TorusWeight S.torus)
    (P : Parameters) (ι : ExtensionField P →+* k)
    (e : FixedCoordinates P ≃ finiteCell S n Q) (r : Fin 12 → S.roots.Root)
    (he : ∀ a, cellInclusion S n Q (e a) =
      orderedRootPoint S r (fun i => ι (a.val i)))
    (f : K.PolynomialFunction) (hf : RootCovariant S R chi f)
    (p : MvPolynomial (Fin 12) k)
    (hchart : ∀ x, f (orderedRootPoint S r x) = eval x p)
    (hp : ∀ d ∈ p.support, RootWeightBound P.q d)
    (hc : p.coeff (rootTopExponent P.q) ≠ 0) :
    HasNonzeroCellSum S n R Q chi := by
  refine hasNonzeroCellSum_of_polynomial S n R Q chi (CoordinateField P)
    (coordinateEmbedding P ι) ((parameterEquiv P).trans ((fixedCoordinatesEquiv P).trans e))
    ⟨f, hf⟩ (gridPolynomial P p) ?_ (gridPolynomial_support P p) ?_
  · intro x
    change f (cellInclusion S n Q (e (fixedCoordinatesEquiv P (parameterEquiv P x)))) = _
    rw [he, hchart, eval_gridPolynomial]
    rfl
  · rwa [top_coefficient_gridPolynomial P p hp]

/-- The same calculation for an actual left translate; right covariance is proved,
not included among the inputs for the translated function. -/
theorem hasNonzeroCellSum_of_translated_chart_bound (S : Geometry K) (n : ℕ)
    (R Q : Set S.roots.Root) (chi : TorusWeight S.torus)
    (P : Parameters) (ι : ExtensionField P →+* k)
    (e : FixedCoordinates P ≃ finiteCell S n Q) (r : Fin 12 → S.roots.Root)
    (he : ∀ a, cellInclusion S n Q (e a) =
      orderedRootPoint S r (fun i => ι (a.val i)))
    (f : K.PolynomialFunction) (hf : RootCovariant S R chi f)
    (g : Variety.Point K) (p : MvPolynomial (Fin 12) k)
    (hchart : ∀ x, f (g * orderedRootPoint S r x) = eval x p)
    (hp : ∀ d ∈ p.support, RootWeightBound P.q d)
    (hc : p.coeff (rootTopExponent P.q) ≠ 0) :
    HasNonzeroCellSum S n R Q chi :=
  hasNonzeroCellSum_of_chart_bound S n R Q chi P ι e r he
    (leftTranslate S R chi g ⟨f, hf⟩).val (leftTranslate S R chi g ⟨f, hf⟩).property
    p (fun x => by rw [leftTranslate_apply]; exact hchart x) hp hc

end Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.ExtremalGrid.PolynomialBounds
