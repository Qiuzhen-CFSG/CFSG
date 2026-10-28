module
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.FiniteHighestWeight.FiniteUnipotent.ExtremalGrid.NormSections.PolynomialBounds.DividedPowerEndpoint.Operators
public import Mathlib.Algebra.MvPolynomial.Equiv
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.FiniteHighestWeight.FiniteUnipotent.ExtremalGrid.NormSections.GlobalCoefficients
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.FiniteHighestWeight.FiniteUnipotent.ExtremalGrid.NormSections.PolynomialBounds.Substitution

/-!
# Exact coefficients of the ordered root chart

Successively applying the polynomial equivalence which separates the first
coordinate identifies every multivariate coefficient with the corresponding
ordered word of actual divided-power operators. The rightmost operator acts
first, exactly as in the supplied root product. This uses polynomial uniqueness
over the algebraic closure and never divides by factorials.

The global matrix coefficient of a highest vector supplies the actual regular
covariant function and chart polynomial. Its top coefficient is the chosen
covector applied to the literal twelve-root top operator.

Source: Steinberg (1963), Sections 2.8 and 4.3; GLS3 Chapter2St2, 13.2(d).
-/

public noncomputable section
open Theory.AlgebraicGroup
namespace Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.ExtremalGrid.SourceCharts
open AlgebraicTensor.RestrictedStep CyclicDimension
universe u v
variable {k : Type u} [Field k] [IsAlgClosed k]
variable {K : Variety k} [AlgebraicGroup K]
variable {V : Type v} [AddCommGroup V] [Module k V] [FiniteDimensional k V]

/-- Coefficient extraction for a finite ordered product of actual rational curves. -/
theorem coeff_eq_ordered_curveCoefficient
    (rho : RationalRepresentation K V) (hr : IsRationalRepresentation rho)
    (m : ℕ) (x : Fin m → Morphism (KPlus k) K)
    (l : Module.Dual k V) (v : V) (p : MvPolynomial (Fin m) k)
    (hp : ∀ t, MvPolynomial.eval t p =
      l ((List.ofFn fun i => (rho.action ((x i).onPoints (kPlusPoint (t i))))).prod.val v))
    (d : Fin m →₀ ℕ) :
    p.coeff d = l ((List.ofFn fun i => curveCoefficient rho hr (x i) (d i)).prod v) := by
  induction m generalizing l with
  | zero =>
    have hd : d = 0 := Subsingleton.elim _ _
    simpa only [hd, MvPolynomial.eval_zero, MvPolynomial.constantCoeff_eq,
      List.ofFn_zero, List.prod_nil, Units.val_one, Module.End.one_apply] using hp 0
  | succ m ih =>
    let p' := (MvPolynomial.finSuccEquiv k m p).coeff (d 0)
    let l' : Module.Dual k V := l.comp (curveCoefficient rho hr (x 0) (d 0))
    have hp' (t : Fin m → k) : MvPolynomial.eval t p' =
        l' ((List.ofFn fun i => (rho.action ((x i.succ).onPoints (kPlusPoint (t i))))).prod.val v) := by
      let w := (List.ofFn fun i =>
        (rho.action ((x i.succ).onPoints (kPlusPoint (t i))))).prod.val v
      have he : Polynomial.map (MvPolynomial.eval t) (MvPolynomial.finSuccEquiv k m p) =
          curvePolynomial rho hr (x 0) l w := by
        apply Polynomial.funext
        intro a
        rw [← MvPolynomial.eval_eq_eval_mv_eval', curvePolynomial_eval, hp]
        simp only [List.ofFn_succ, Fin.cons_zero, Fin.cons_succ, List.prod_cons,
          Units.val_mul, Module.End.mul_apply]
        rfl
      have hc := congrArg (fun q : Polynomial k => q.coeff (d 0)) he
      rw [Polynomial.coeff_map, ← dual_curveCoefficient] at hc
      exact hc
    have h := ih (fun i => x i.succ) l' p' hp' d.tail
    rw [MvPolynomial.finSuccEquiv_coeff_coeff, Finsupp.cons_tail] at h
    rw [h]
    simp only [l', LinearMap.comp_apply, List.ofFn_succ, List.prod_cons,
      Module.End.mul_apply, Finsupp.tail_apply]

variable [CharP k 2]
open DividedPowerEndpoint

/-- Every coefficient of an actual root-chart polynomial is the same ordered
word in the supplied root divided powers. -/
theorem coeff_eq_ordered_rootDividedPower (S : Geometry K)
    (rho : RationalRepresentation K V) (hr : IsRationalRepresentation rho)
    (r : Fin 12 → S.roots.Root) (l : Module.Dual k V) (v : V)
    (p : MvPolynomial (Fin 12) k)
    (hp : ∀ t, MvPolynomial.eval t p = l ((rho.action (orderedRootPoint S r t)).val v))
    (d : Fin 12 →₀ ℕ) :
    p.coeff d = l ((List.ofFn fun i => rootDividedPower S rho hr (r i) (d i)).prod v) := by
  apply coeff_eq_ordered_curveCoefficient rho hr 12 (fun i => rootCurve S (r i)) l v p
  intro t
  rw [hp]
  have he := map_list_prod rho.action (List.ofFn fun i =>
    (rootCurve S (r i)).onPoints (kPlusPoint (t i)))
  simpa only [List.map_ofFn, Function.comp_def, rootCurve_apply, orderedRootPoint] using
    congrArg (fun a => l (a.val v)) he

/-- The root-top monomial uses precisely the source operator order. -/
theorem top_coeff_eq_topOperator (S : Geometry K)
    (rho : RationalRepresentation K V) (hr : IsRationalRepresentation rho)
    (r : Fin 12 → S.roots.Root) (n : ℕ) (l : Module.Dual k V) (v : V)
    (p : MvPolynomial (Fin 12) k)
    (hp : ∀ t, MvPolynomial.eval t p = l ((rho.action (orderedRootPoint S r t)).val v)) :
    p.coeff (PolynomialBounds.rootTopExponent (2 ^ n)) =
      l (topOperator S rho hr r n v) := by
  exact coeff_eq_ordered_rootDividedPower S rho hr r l v p hp _

/-- Construct the global covariant matrix coefficient and its actual chart,
retaining the exact formula for every multivariate coefficient. -/
theorem exists_covariant_chart (S : Geometry K)
    (rho : RationalRepresentation K V) (hr : IsRationalRepresentation rho)
    {P : Set S.roots.Root} {B : ClosedSubgroup K}
    (hB : IsBorelOfPositiveSystem S.roots P B)
    (v : V) (chi : TorusWeight S.torus) (hv : HasHighWeight rho B S.torus v chi)
    (l : Module.Dual k V) (r : Fin 12 → S.roots.Root) :
    ∃ (f : K.PolynomialFunction) (p : MvPolynomial (Fin 12) k),
      RootCovariant S P chi f ∧
      (∀ g, f g = l ((rho.action g).val v)) ∧
      (∀ t, f (orderedRootPoint S r t) = MvPolynomial.eval t p) ∧
      (∀ d, p.coeff d =
        l ((List.ofFn fun i => rootDividedPower S rho hr (r i) (d i)).prod v)) := by
  obtain ⟨f,hf,he⟩ := exists_rootCovariant_matrixCoefficient S rho hr hB v chi hv l
  obtain ⟨p,hp⟩ := exists_polynomial_on_orderedRootPoint S r f
  refine ⟨f,p,hf,he,hp,fun d => coeff_eq_ordered_rootDividedPower S rho hr r l v p ?_ d⟩
  intro t
  exact (hp t).symm.trans (he _)

end Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.ExtremalGrid.SourceCharts
