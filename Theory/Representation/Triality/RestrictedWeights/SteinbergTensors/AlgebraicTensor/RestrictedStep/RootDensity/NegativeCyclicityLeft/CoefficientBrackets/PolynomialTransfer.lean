module

public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.AlgebraicTensor.RestrictedStep.RootDensity.NegativeCyclicityLeft.Triangular

/-!
# Coefficient transfer for the actual D4 root curves

Finite-dimensional rationality supplies an endomorphism-valued polynomial
for each pinned root curve. Scalar evaluation is a ring homomorphism and
polynomial uniqueness holds after applying every covector. Comparing the two
parameters of an actual root exchange therefore identifies the mixed `(1,1)`
coefficient with the commutator of the published `rootOperator`s.

In characteristic two, the same polynomial squares to one pointwise. Its
degree-two coefficient proves that the first root operator squares to zero.
These arguments divide by no factorial and use no characteristic-zero
representation differential. The exchange premise is explicit here; its D4
Chevalley-system proof is a separate geometric step.

The scalar-evaluation proof adapts the repository's F4
`SpanInvariance.Nonopposite.PolynomialTransfer` to arbitrary `D4Geometry` and
constructs the polynomial from the given rational representation itself.
Sources: GLS3 §1.12, especially 1.12.1(a,b); Steinberg,
*Representations of Algebraic Groups* (1963), §§2 and 4.
-/

open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
namespace Triality.RestrictedWeights.SteinbergTensors.AlgebraicTensor.RestrictedStep.RootDensity.NegativeCyclicityLeft
public noncomputable section
universe u v
variable {k : Type u} [Field k] [IsAlgClosed k]
section Polynomial
variable {A : Type*} [Ring A] [Algebra k A]

private def scalarEval (t : k) : Polynomial A →+* A :=
  Polynomial.eval₂RingHom' (RingHom.id A) (algebraMap k A t)
    (fun a => (Algebra.commutes t a).symm)

omit [IsAlgClosed k] in
private lemma scalarEval_eq_sum (q : Polynomial A) (t : k) :
    scalarEval t q = q.sum (fun n a => t ^ n • a) := by
  classical
  change Polynomial.eval₂ (RingHom.id A) (algebraMap k A t) q = _
  rw [Polynomial.eval₂_eq_sum]
  apply Finset.sum_congr rfl
  intro n hn
  simp only [RingHom.id_apply, ← map_pow, Algebra.smul_def]
  exact (Algebra.commutes (t ^ n) (q.coeff n)).symm

omit [IsAlgClosed k] in
private lemma scalarEval_C (t : k) (a : A) : scalarEval t (Polynomial.C a) = a := by
  exact Polynomial.eval₂_C _ _

omit [IsAlgClosed k] in
private lemma scalarEval_monomial (t : k) (n : ℕ) (a : A) :
    scalarEval t (Polynomial.monomial n a) = t ^ n • a := by
  change Polynomial.eval₂ _ _ _ = _
  rw [Polynomial.eval₂_monomial]
  simp only [RingHom.id_apply, ← map_pow, Algebra.smul_def]
  exact (Algebra.commutes (t ^ n) a).symm

private lemma scalarEval_ext (q z : Polynomial A) (h : ∀ t : k, scalarEval t q = scalarEval t z) :
    q = z := by
  classical
  let mapDual (l : Module.Dual k A) (p : Polynomial A) : Polynomial k :=
    p.sum fun n a => Polynomial.monomial n (l a)
  have hc (l : Module.Dual k A) (p : Polynomial A) (n : ℕ) :
      (mapDual l p).coeff n = l (p.coeff n) := by
    by_cases hn : n ∈ p.support
    · simp [mapDual, Polynomial.sum, Polynomial.coeff_monomial, eq_comm, hn]
    · simp [mapDual, Polynomial.sum, Polynomial.coeff_monomial, eq_comm, hn,
        Polynomial.notMem_support_iff.mp hn]
  have he (l : Module.Dual k A) (p : Polynomial A) (t : k) :
      (mapDual l p).eval t = l (scalarEval t p) := by
    rw [scalarEval_eq_sum]
    simp only [mapDual, Polynomial.sum, Polynomial.eval_finsetSum,
      Polynomial.eval_monomial, map_sum, map_smul, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro n hn
    exact mul_comm _ _
  apply Polynomial.ext
  intro n
  apply sub_eq_zero.mp
  rw [← Module.forall_dual_apply_eq_zero_iff k]
  intro l
  have hp : mapDual l q = mapDual l z := by
    apply Polynomial.funext
    intro t
    rw [he, he, h]
  have hh := congrArg (fun p : Polynomial k => p.coeff n) hp
  rw [hc, hc] at hh
  simpa only [map_sub, sub_eq_zero] using hh
end Polynomial


variable {K : Variety k} [AlgebraicGroup K]
variable {V : Type v} [AddCommGroup V] [Module k V] [FiniteDimensional k V]

private def liftPolynomial (p : Polynomial k) (A : Module.End k V) :
    Polynomial (Module.End k V) := p.sum fun n c => Polynomial.monomial n (c • A)

omit [IsAlgClosed k] [FiniteDimensional k V] in
private theorem liftPolynomial_coeff (p : Polynomial k) (A : Module.End k V) (n : ℕ) :
    (liftPolynomial p A).coeff n = p.coeff n • A := by
  classical
  by_cases hn : n ∈ p.support
  · simp [liftPolynomial, Polynomial.sum, Polynomial.coeff_monomial, eq_comm, hn]
  · simp [liftPolynomial, Polynomial.sum, Polynomial.coeff_monomial, eq_comm, hn,
      Polynomial.notMem_support_iff.mp hn]

omit [IsAlgClosed k] [FiniteDimensional k V] in
private theorem liftPolynomial_eval (p : Polynomial k) (A : Module.End k V) (t : k) :
    scalarEval t (liftPolynomial p A) = p.eval t • A := by
  classical
  simp only [liftPolynomial, Polynomial.sum, map_sum, scalarEval_monomial, smul_smul]
  rw [Polynomial.eval_eq_sum]
  simp only [Polynomial.sum, Finset.sum_smul]
  congr 1
  funext n
  rw [mul_comm]

private def operatorPolynomial (S : D4Geometry K) (ρ : RationalRepresentation K V)
    (hρ : IsRationalRepresentation ρ) (α : S.roots.Root) :
    Polynomial (Module.End k V) :=
  let b := Module.finBasis k V
  ∑ i, ∑ j, liftPolynomial (curvePolynomial ρ hρ (rootMorphism S α) (b.coord i) (b j))
    (b.end (i,j))

private theorem operatorPolynomial_eval (S : D4Geometry K) (ρ : RationalRepresentation K V)
    (hρ : IsRationalRepresentation ρ) (α : S.roots.Root) (t : k) :
    scalarEval t (operatorPolynomial S ρ hρ α) = (ρ.action (S.chevalley.x α t)).val := by
  classical
  let b := Module.finBasis k V
  simp only [operatorPolynomial, map_sum, liftPolynomial_eval, curvePolynomial_eval,
    rootMorphism_apply]
  apply LinearMap.ext_on b.span_eq
  rintro _ ⟨j, rfl⟩
  simp only [b, LinearMap.sum_apply, LinearMap.smul_apply, Module.Basis.end_apply_apply,
    smul_ite, smul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  exact b.sum_repr _

private theorem operatorPolynomial_coeff_one (S : D4Geometry K) (ρ : RationalRepresentation K V)
    (hρ : IsRationalRepresentation ρ) (α : S.roots.Root) :
    (operatorPolynomial S ρ hρ α).coeff 1 = rootOperator S ρ hρ α := by
  classical
  let b := Module.finBasis k V
  simp only [operatorPolynomial, Polynomial.finsetSum_coeff, liftPolynomial_coeff,
    ← dual_curveOperator]
  apply LinearMap.ext_on b.span_eq
  rintro _ ⟨j, rfl⟩
  simp only [b, LinearMap.sum_apply, LinearMap.smul_apply, Module.Basis.end_apply_apply,
    smul_ite, smul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  exact b.sum_repr _

private theorem operatorPolynomial_coeff_zero (S : D4Geometry K) (ρ : RationalRepresentation K V)
    (hρ : IsRationalRepresentation ρ) (α : S.roots.Root) :
    (operatorPolynomial S ρ hρ α).coeff 0 = 1 := by
  classical
  let b := Module.finBasis k V
  simp only [operatorPolynomial, Polynomial.finsetSum_coeff, liftPolynomial_coeff,
    curvePolynomial_coeff_zero]
  apply LinearMap.ext_on b.span_eq
  rintro _ ⟨j, rfl⟩
  simp only [b, LinearMap.sum_apply, LinearMap.smul_apply, Module.Basis.end_apply_apply,
    smul_ite, smul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  exact b.sum_repr _

private def scaledPolynomial {A : Type*} [Ring A] [Algebra k A]
    (p : Polynomial A) (c : k) : Polynomial A :=
  p.sum fun n a => Polynomial.monomial n (c ^ n • a)

omit [IsAlgClosed k] in
private theorem scaledPolynomial_coeff {A : Type*} [Ring A] [Algebra k A]
    (p : Polynomial A) (c : k) (n : ℕ) :
    (scaledPolynomial p c).coeff n = c ^ n • p.coeff n := by
  classical
  by_cases hn : n ∈ p.support
  · simp [scaledPolynomial, Polynomial.sum, Polynomial.coeff_monomial, eq_comm, hn]
  · simp [scaledPolynomial, Polynomial.sum, Polynomial.coeff_monomial, eq_comm, hn,
      Polynomial.notMem_support_iff.mp hn]

omit [IsAlgClosed k] in
private theorem scaledPolynomial_eval {A : Type*} [Ring A] [Algebra k A]
    (p : Polynomial A) (c t : k) :
    scalarEval t (scaledPolynomial p c) = scalarEval (c * t) p := by
  classical
  rw [scalarEval_eq_sum p]
  simp only [scaledPolynomial, Polynomial.sum, map_sum, scalarEval_monomial, smul_smul,
    mul_pow]
  apply Finset.sum_congr rfl
  intro n hn
  rw [mul_comm]

/-- Mixed coefficient extraction from an actual single-term root exchange. -/
theorem rootOperator_commutator_of_exchange (S : D4Geometry K)
    (ρ : RationalRepresentation K V) (hρ : IsRationalRepresentation ρ)
    (α β γ : S.roots.Root) (c : k)
    (h : ∀ a b : k, S.chevalley.x α a * S.chevalley.x β b =
      S.chevalley.x β b * S.chevalley.x α a * S.chevalley.x γ (c * a * b)) :
    rootOperator S ρ hρ α * rootOperator S ρ hρ β -
      rootOperator S ρ hρ β * rootOperator S ρ hρ α = c • rootOperator S ρ hρ γ := by
  let p := operatorPolynomial S ρ hρ
  let E := rootOperator S ρ hρ
  have hfirst (a : k) :
      (ρ.action (S.chevalley.x α a)).val * E β =
        (ρ.action (S.chevalley.x α a)).val * ((c * a) • E γ) +
          E β * (ρ.action (S.chevalley.x α a)).val := by
    let R := (ρ.action (S.chevalley.x α a)).val
    have hp : Polynomial.C R * p β =
        p β * Polynomial.C R * scaledPolynomial (p γ) (c * a) := by
      apply scalarEval_ext (k := k)
      intro b
      simp only [map_mul, scalarEval_C, scaledPolynomial_eval, p, operatorPolynomial_eval]
      have he := congrArg (fun g => (ρ.action g).val) (h a b)
      simpa only [map_mul, Units.val_mul, R] using he
    have hc := congrArg (fun P : Polynomial (Module.End k V) => P.coeff 1) hp
    simpa only [Polynomial.mul_coeff_one, Polynomial.mul_coeff_zero,
      Polynomial.coeff_C_zero, Polynomial.coeff_C_succ, scaledPolynomial_coeff,
      pow_zero, pow_one, one_smul, p, operatorPolynomial_coeff_one,
      operatorPolynomial_coeff_zero, mul_one, one_mul, zero_mul, mul_zero,
      add_zero, zero_add, R, E] using hc
  have hp : p α * Polynomial.C (E β) =
      p α * Polynomial.monomial 1 (c • E γ) + Polynomial.C (E β) * p α := by
    apply scalarEval_ext (k := k)
    intro a
    simp only [map_mul, map_add, scalarEval_C, scalarEval_monomial, p,
      operatorPolynomial_eval, pow_one, smul_smul]
    simpa only [mul_comm a c] using hfirst a
  have hc := congrArg (fun P : Polynomial (Module.End k V) => P.coeff 1) hp
  apply sub_eq_iff_eq_add.mpr
  simpa only [Polynomial.coeff_add, Polynomial.mul_coeff_one,
    Polynomial.coeff_C_zero, Polynomial.coeff_C_succ, Polynomial.coeff_monomial,
    p, operatorPolynomial_coeff_zero, operatorPolynomial_coeff_one,
    mul_one, one_mul, zero_mul, mul_zero, add_zero, zero_add, if_true,
    show ¬ (1 : ℕ) = 0 by decide, if_false, E] using hc

/-- Commuting actual root subgroups have commuting first coefficients. -/
theorem rootOperator_commutator_of_commute (S : D4Geometry K)
    (ρ : RationalRepresentation K V) (hρ : IsRationalRepresentation ρ)
    (α β : S.roots.Root)
    (h : ∀ a b : k, Commute (S.chevalley.x α a) (S.chevalley.x β b)) :
    rootOperator S ρ hρ α * rootOperator S ρ hρ β -
      rootOperator S ρ hρ β * rootOperator S ρ hρ α = 0 := by
  have hz : S.chevalley.x α 0 = 1 := by
    rw [← rootMorphism_apply]
    have hzero : kPlusPoint (0 : k) = 1 := by
      apply (additiveGroupPointEquiv k).injective
      rfl
    rw [hzero, map_one]
  have he := rootOperator_commutator_of_exchange S ρ hρ α β α 0 (by
    intro a b
    simpa only [zero_mul, hz, mul_one] using (h a b).eq)
  simpa only [zero_smul] using he

/-- Actual first root coefficients square to zero in characteristic two. -/
theorem rootOperator_square_zero [CharP k 2] (S : D4Geometry K)
    (ρ : RationalRepresentation K V) (hρ : IsRationalRepresentation ρ)
    (α : S.roots.Root) : rootOperator S ρ hρ α * rootOperator S ρ hρ α = 0 := by
  let p := operatorPolynomial S ρ hρ α
  have hp : p * p = 1 := by
    apply scalarEval_ext (k := k)
    intro t
    rw [map_mul, map_one, operatorPolynomial_eval, ← Units.val_mul, ← map_mul]
    rw [S.chevalley_spec.2.2.2.1, CharTwo.add_self_eq_zero]
    have hz : S.chevalley.x α 0 = 1 := by
      rw [← rootMorphism_apply]
      have hzero : kPlusPoint (0 : k) = 1 := by
        apply (additiveGroupPointEquiv k).injective
        rfl
      rw [hzero, map_one]
    rw [hz, map_one, Units.val_one]
  have hc := congrArg (fun q : Polynomial (Module.End k V) => q.coeff 2) hp
  rw [Polynomial.coeff_mul, Finset.Nat.antidiagonal_eq_map] at hc
  simp only [Finset.sum_map, Finset.sum_range_succ,
    Finset.sum_range_zero, zero_add] at hc
  change p.coeff 0 * p.coeff 2 + p.coeff 1 * p.coeff 1 +
    p.coeff 2 * p.coeff 0 = (1 : Polynomial (Module.End k V)).coeff 2 at hc
  simp only [p, operatorPolynomial_coeff_zero, operatorPolynomial_coeff_one,
    one_mul, mul_one, Polynomial.coeff_one, show (2 : ℕ) ≠ 0 by decide, if_false] at hc
  have htwo (A : Module.End k V) : A + A = 0 := by
    rw [← two_smul k A, show (2 : k) = 0 from CharTwo.two_eq_zero, zero_smul]
  rw [add_right_comm, htwo, zero_add] at hc
  exact hc
end
end Triality.RestrictedWeights.SteinbergTensors.AlgebraicTensor.RestrictedStep.RootDensity.NegativeCyclicityLeft
