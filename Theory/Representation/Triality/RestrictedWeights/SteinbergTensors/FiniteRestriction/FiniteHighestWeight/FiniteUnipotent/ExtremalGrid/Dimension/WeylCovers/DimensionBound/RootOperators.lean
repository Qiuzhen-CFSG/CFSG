module

public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.FiniteHighestWeight.FiniteUnipotent.ExtremalGrid.Dimension.WeylCovers.Cyclic
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.LeftContracts.Extremal
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.AlgebraicTensor.RestrictedStep.Coefficients
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.FiniteHighestWeight.FiniteUnipotent.ExtremalGrid.RootCoordinates

/-!+# Higher root coefficients for the cyclic dimension argument

The degree `j` coefficient of an actual rational root action is a linear
endomorphism. This construction uses polynomial coefficients, so it does not
divide by factorials in characteristic two. The coefficients of degree below
`q` generate a concrete subalgebra of endomorphisms. Its orbit on a highest
vector is the candidate infinitesimal cyclic module.

The ordered negative-root products have `q^12` possible exponent tuples.
Their span therefore has dimension at most `q^12`. Identifying the full
coefficient-algebra orbit with this span, and proving that it is invariant
under the algebraic group, are separate remaining obligations. No such
identification, invariance, or dimension bound for the original module is
included in the definitions.

Source: the root-monomial construction in Steinberg, *Representations of
algebraic groups* (1963), §2, and the extremal weight in GLS3/St2 13.2(d).
Higher coefficients are needed when `q = 2^n`, including `n > 1`.
-/

public noncomputable section
namespace Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.ExtremalGrid
open Theory.AlgebraicGroup
open AlgebraicTensor.RestrictedStep
universe u v
variable {k : Type u} [Field k] [IsAlgClosed k]
variable {K : Variety k} [AlgebraicGroup K]
variable {V : Type v} [AddCommGroup V] [Module k V] [FiniteDimensional k V]

namespace CyclicDimension

/-- All polynomial coefficients of a rational additive-root action. -/
@[expose] def curveCoefficient (rho : RationalRepresentation K V)
    (hr : IsRationalRepresentation rho) (x : Morphism (KPlus k) K)
    (j : ℕ) : Module.End k V :=
  let b := Module.finBasis k V
  { toFun := fun v => ∑ i, (curvePolynomial rho hr x (b.coord i) v).coeff j • b i
    map_add' := by
      intro v w
      simp only [curvePolynomial_add, Polynomial.coeff_add, add_smul,
        Finset.sum_add_distrib]
    map_smul' := by
      intro c v
      simp only [curvePolynomial_smul, Polynomial.coeff_smul, smul_eq_mul,
        mul_smul, Finset.smul_sum, RingHom.id_apply] }

/-- Covectors recover the specified scalar coefficient, independently of basis. -/
theorem dual_curveCoefficient (rho : RationalRepresentation K V)
    (hr : IsRationalRepresentation rho) (x : Morphism (KPlus k) K)
    (j : ℕ) (l : Module.Dual k V) (v : V) :
    l (curveCoefficient rho hr x j v) = (curvePolynomial rho hr x l v).coeff j := by
  let b := Module.finBasis k V
  have hp : curvePolynomial rho hr x l v =
      ∑ i, l (b i) • curvePolynomial rho hr x (b.coord i) v := by
    apply Polynomial.funext
    intro t
    simp only [Polynomial.eval_finsetSum, Polynomial.eval_smul, curvePolynomial_eval]
    conv_lhs => rw [← b.sum_repr ((rho.action (x.onPoints (kPlusPoint t))).val v)]
    simp only [map_sum, map_smul, smul_eq_mul, Module.Basis.coord_apply, mul_comm]
  rw [hp]
  change l (∑ i, (curvePolynomial rho hr x (b.coord i) v).coeff j • b i) = _
  simp only [map_sum, map_smul, Polynomial.finsetSum_coeff, Polynomial.coeff_smul,
    smul_eq_mul, mul_comm]

@[simp] theorem curveCoefficient_zero (rho : RationalRepresentation K V)
    (hr : IsRationalRepresentation rho) (x : Morphism (KPlus k) K) :
    curveCoefficient rho hr x 0 = 1 := by
  ext v
  change (∑ i, (curvePolynomial rho hr x ((Module.finBasis k V).coord i) v).coeff 0 •
    (Module.finBasis k V) i) = v
  simp only [curvePolynomial_coeff_zero, Module.Basis.coord_apply,
    Module.Basis.sum_repr]

/-- Point-invariant subspaces are stable under every higher root coefficient. -/
theorem curveCoefficient_mem (rho : RationalRepresentation K V)
    (hr : IsRationalRepresentation rho) (x : Morphism (KPlus k) K)
    (j : ℕ) (U : Submodule k V) (hU : IsInvariantSubmodule rho U)
    (v : V) (hv : v ∈ U) : curveCoefficient rho hr x j v ∈ U := by
  rw [← Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff]
  intro l hl
  rw [dual_curveCoefficient]
  have hp : curvePolynomial rho hr x l v = 0 := by
    apply Polynomial.funext
    intro t
    rw [curvePolynomial_eval, Polynomial.eval_zero]
    exact (Submodule.mem_dualAnnihilator _).mp hl _ (hU _ _ hv)
  simp only [hp, Polynomial.coeff_zero]

variable [CharP k 2]

/-- The literal root parametrization supplied by finite-restriction geometry. -/
@[expose] def rootCurve (S : Geometry K) (r : S.roots.Root) : Morphism (KPlus k) K :=
  (S.roots.rootSubgroup r).inclusion.comp (S.rootParameter r).hom

@[expose] def rootCoefficient (S : Geometry K) (rho : RationalRepresentation K V)
    (hr : IsRationalRepresentation rho) (r : S.roots.Root) (j : ℕ) : Module.End k V :=
  curveCoefficient rho hr (rootCurve S r) j

/-- An actual subalgebra, generated by all roots and all orders strictly below q. -/
@[expose] def coefficientAlgebra (S : Geometry K) (rho : RationalRepresentation K V)
    (hr : IsRationalRepresentation rho) (q : ℕ) : Subalgebra k (Module.End k V) :=
  Algebra.adjoin k (Set.range fun rj : S.roots.Root × Fin q =>
    rootCoefficient S rho hr rj.1 rj.2)

/-- A concrete normalization condition on an operator algebra. -/
@[expose] def Normalizes (rho : RationalRepresentation K V)
    (A : Subalgebra k (Module.End k V)) : Prop :=
  ∀ g (a : Module.End k V), a ∈ A →
    ∃ b : Module.End k V, b ∈ A ∧ (rho.action g).val * a = b * (rho.action g).val

/-- The orbit of a vector under a specified algebra of linear operators. -/
@[expose] def operatorOrbit (A : Subalgebra k (Module.End k V)) (v : V) : Submodule k V :=
  Submodule.span k (Set.range fun a : A => a.val v)

omit [IsAlgClosed k] [CharP k 2] [FiniteDimensional k V] in
theorem mem_operatorOrbit (A : Subalgebra k (Module.End k V)) (v : V) :
    v ∈ operatorOrbit A v := by
  exact Submodule.subset_span ⟨1, rfl⟩

omit [IsAlgClosed k] [CharP k 2] [FiniteDimensional k V] in
/-- Multiplication in the operator algebra preserves its orbit span. -/
theorem operatorOrbit_stable (A : Subalgebra k (Module.End k V)) (v : V)
    (a : Module.End k V) (ha : a ∈ A) (w : V) (hw : w ∈ operatorOrbit A v) :
    a w ∈ operatorOrbit A v := by
  induction hw using Submodule.span_induction with
  | mem w hw =>
      obtain ⟨b, rfl⟩ := hw
      exact Submodule.subset_span ⟨⟨a * b.val, A.mul_mem ha b.property⟩, rfl⟩
  | zero => simpa only [map_zero] using (operatorOrbit A v).zero_mem
  | add w z _ _ hw hz => simpa only [map_add] using (operatorOrbit A v).add_mem hw hz
  | smul c w _ hw => simpa only [map_smul] using (operatorOrbit A v).smul_mem c hw

/-- Low root coefficients belong to the algebra by its actual generating set. -/
theorem rootCoefficient_mem (S : Geometry K) (rho : RationalRepresentation K V)
    (hr : IsRationalRepresentation rho) (q : ℕ) (r : S.roots.Root)
    (j : ℕ) (hj : j < q) : rootCoefficient S rho hr r j ∈ coefficientAlgebra S rho hr q :=
  Algebra.subset_adjoin ⟨(r, ⟨j, hj⟩), rfl⟩

/-- A degree bound on one root orbit places its evaluations in the coefficient
algebra orbit. No degree bound on an entire twelve-variable chart is used. -/
theorem rootAction_mem_of_highCoefficients_zero (S : Geometry K)
    (rho : RationalRepresentation K V) (hr : IsRationalRepresentation rho)
    (q : ℕ) (r : S.roots.Root) (v : V)
    (hzero : ∀ j, q ≤ j → rootCoefficient S rho hr r j v = 0) (t : k) :
    (rho.action ((rootCurve S r).onPoints (kPlusPoint t))).val v ∈
      operatorOrbit (coefficientAlgebra S rho hr q) v := by
  rw [← Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff]
  intro l hl
  have hp : curvePolynomial rho hr (rootCurve S r) l v = 0 := by
    apply Polynomial.ext
    intro j
    rw [Polynomial.coeff_zero, ← dual_curveCoefficient]
    change l (rootCoefficient S rho hr r j v) = 0
    by_cases hj : j < q
    · apply (Submodule.mem_dualAnnihilator _).mp hl
      exact Submodule.subset_span
        ⟨⟨rootCoefficient S rho hr r j, rootCoefficient_mem S rho hr q r j hj⟩, rfl⟩
    · rw [hzero j (Nat.le_of_not_gt hj), map_zero]
  rw [← curvePolynomial_eval rho hr (rootCurve S r) l v t, hp, Polynomial.eval_zero]

/-- The actual signed simple-root points; no point-generation theorem is assumed. -/
@[expose] def simpleRootPoints (S : Geometry K) : Set (Variety.Point K) :=
  Set.range fun a : Fin 4 × Bool × k =>
    (rootCurve S (if a.2.1 then (S.simpleRoot a.1).val
      else S.roots.neg (S.simpleRoot a.1).val)).onPoints (kPlusPoint a.2.2)

/-- An ordered divided-power word on the actual twelve root curves. -/
@[expose] def orderedCoefficient (S : Geometry K) (rho : RationalRepresentation K V)
    (hr : IsRationalRepresentation rho) (r : Fin 12 → S.roots.Root)
    (q : ℕ) (a : Fin 12 → Fin q) : Module.End k V :=
  (List.ofFn fun i => rootCoefficient S rho hr (r i) (a i)).prod

@[expose] def orderedCoefficientSpan (S : Geometry K) (rho : RationalRepresentation K V)
    (hr : IsRationalRepresentation rho) (r : Fin 12 → S.roots.Root)
    (q : ℕ) (v : V) : Submodule k V :=
  Submodule.span k (Set.range fun a : Fin 12 → Fin q =>
    orderedCoefficient S rho hr r q a v)

/-- Counting exponent tuples bounds this particular span, without asserting
that it is the full cyclic module. -/
theorem finrank_orderedCoefficientSpan_le (S : Geometry K)
    (rho : RationalRepresentation K V) (hr : IsRationalRepresentation rho)
    (r : Fin 12 → S.roots.Root) (q : ℕ) (v : V) :
    Module.finrank k (orderedCoefficientSpan S rho hr r q v) ≤ q ^ 12 := by
  change Module.finrank k (Submodule.span k (Set.range fun a : Fin 12 → Fin q =>
    orderedCoefficient S rho hr r q a v)) ≤ q ^ 12
  calc
    _ ≤ Fintype.card (Fin 12 → Fin q) := finrank_range_le_card _
    _ = q ^ 12 := by simp only [Fintype.card_fun, Fintype.card_fin]

end CyclicDimension
end Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.ExtremalGrid
