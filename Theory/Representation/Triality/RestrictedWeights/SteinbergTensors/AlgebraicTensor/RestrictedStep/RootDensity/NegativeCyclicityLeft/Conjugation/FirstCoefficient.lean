module

public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.AlgebraicTensor.RestrictedStep.RootDensity.NegativeCyclicityLeft.Cyclic
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.AlgebraicTensor.RestrictedStep.RootDensity.NegativeCyclicityLeft.CartanHighest
public import Theory.AlgebraicGroup.Bor1.ConjugationRational

/-!
# First-coefficient conjugation for actual D4 root curves

For independent roots, the Chevalley commutator word gives a polynomial
identity with constant term one in every factor. Its first coefficient is
therefore a sum of scalar multiples of first root coefficients; only terms
whose exponent in the varying parameter is one contribute.

For opposite roots, apply the proved rank-one highest-string calculation to
the rational conjugation representation on endomorphisms. A root coefficient
is fixed by its own root subgroup and has exponent minus two on the preserved
raw coroot. The actual `n/h` relations bound the opposite-root orbit by degree
two and identify its top coefficient with the opposite root coefficient.
The linear coefficient is the operator bracket. This proves root-algebra
containment for every pair of roots without a characteristic-zero differential
or any factorial division.

The private polynomial construction follows
`CoefficientBrackets.PolynomialTransfer`, retaining narrow imports and the
actual arbitrary `D4Geometry` throughout. Sources: GLS3, Theorem 1.12.1(a,b,g,h,k)
and the definitions of `n` and `h` in `refs/KGroup/GLS3/Chapter1.tex`;
Steinberg, *Representations of Algebraic Groups* (1963), §§2 and 4.
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

private def polynomialDual (l : Module.Dual k A) (p : Polynomial A) : Polynomial k :=
  p.sum fun n a => Polynomial.monomial n (l a)

omit [IsAlgClosed k] in
private theorem polynomialDual_coeff (l : Module.Dual k A) (p : Polynomial A) (n : ℕ) :
    (polynomialDual l p).coeff n = l (p.coeff n) := by
  classical
  by_cases hn : n ∈ p.support
  · simp [polynomialDual, Polynomial.sum, Polynomial.coeff_monomial, eq_comm, hn]
  · simp [polynomialDual, Polynomial.sum, Polynomial.coeff_monomial, eq_comm, hn,
      Polynomial.notMem_support_iff.mp hn]

omit [IsAlgClosed k] in
private theorem polynomialDual_eval (l : Module.Dual k A) (p : Polynomial A) (t : k) :
    (polynomialDual l p).eval t = l (scalarEval t p) := by
  classical
  rw [scalarEval_eq_sum]
  simp only [polynomialDual, Polynomial.sum, Polynomial.eval_finsetSum,
    Polynomial.eval_monomial, map_sum, map_smul, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro n hn
  exact mul_comm _ _

private lemma scalarEval_ext (q z : Polynomial A) (h : ∀ t : k, scalarEval t q = scalarEval t z) :
    q = z := by
  apply Polynomial.ext
  intro n
  apply sub_eq_zero.mp
  rw [← Module.forall_dual_apply_eq_zero_iff k]
  intro l
  have hp : polynomialDual l q = polynomialDual l z := by
    apply Polynomial.funext
    intro t
    rw [polynomialDual_eval, polynomialDual_eval, h]
  have hh := congrArg (fun p : Polynomial k => p.coeff n) hp
  rw [polynomialDual_coeff, polynomialDual_coeff] at hh
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

private def powerScaledPolynomial {A : Type*} [Ring A] [Algebra k A]
    (p : Polynomial A) (c : k) (j : ℕ) : Polynomial A :=
  p.sum fun n a => Polynomial.monomial (n * j) (c ^ n • a)

omit [IsAlgClosed k] in
private theorem powerScaledPolynomial_eval {A : Type*} [Ring A] [Algebra k A]
    (p : Polynomial A) (c t : k) (j : ℕ) :
    scalarEval t (powerScaledPolynomial p c j) = scalarEval (c * t ^ j) p := by
  classical
  rw [scalarEval_eq_sum p]
  simp only [powerScaledPolynomial, Polynomial.sum, map_sum, scalarEval_monomial,
    smul_smul, mul_pow, ← pow_mul]
  apply Finset.sum_congr rfl
  intro n hn
  rw [Nat.mul_comm n j, mul_comm]

omit [IsAlgClosed k] in
private theorem powerScaledPolynomial_coeff_zero {A : Type*} [Ring A] [Algebra k A]
    (p : Polynomial A) (c : k) (j : ℕ) (hj : 0 < j) :
    (powerScaledPolynomial p c j).coeff 0 = p.coeff 0 := by
  classical
  simp [powerScaledPolynomial, Polynomial.sum, Polynomial.coeff_monomial,
    Nat.ne_of_gt hj, eq_comm]

omit [IsAlgClosed k] in
private theorem powerScaledPolynomial_coeff_one {A : Type*} [Ring A] [Algebra k A]
    (p : Polynomial A) (c : k) (j : ℕ) :
    (powerScaledPolynomial p c j).coeff 1 = if j = 1 then c • p.coeff 1 else 0 := by
  classical
  by_cases hj : j = 1
  · subst j
    simpa only [powerScaledPolynomial, scaledPolynomial, Nat.mul_one, ite_true, pow_one] using
      scaledPolynomial_coeff p c 1
  · have h (n : ℕ) : n * j ≠ 1 := by
      intro hn
      exact hj (Nat.dvd_one.mp ⟨n, by simpa only [Nat.mul_comm] using hn.symm⟩)
    simp [powerScaledPolynomial, Polynomial.sum, Polynomial.coeff_monomial, h, hj]

private theorem polynomial_prod_coeff_zero {A : Type*} [Ring A]
    (l : List (Polynomial A)) (h : ∀ p ∈ l, p.coeff 0 = 1) : l.prod.coeff 0 = 1 := by
  induction l with
  | nil => simp
  | cons p l ih =>
    rw [List.prod_cons, Polynomial.mul_coeff_zero, h p (by simp),
      ih (fun q hq => h q (by simp [hq])), one_mul]

private theorem polynomial_prod_coeff_one {A : Type*} [Ring A]
    (l : List (Polynomial A)) (h : ∀ p ∈ l, p.coeff 0 = 1) :
    l.prod.coeff 1 = (l.map fun p => p.coeff 1).sum := by
  induction l with
  | nil => simp [Polynomial.coeff_one]
  | cons p l ih =>
    have hl := fun q hq => h q (List.mem_cons_of_mem p hq)
    rw [List.prod_cons, Polynomial.mul_coeff_one, h p (by simp),
      polynomial_prod_coeff_zero l hl, ih hl]
    simp only [one_mul, mul_one, List.map_cons, List.sum_cons]
    exact add_comm _ _

omit [IsAlgClosed k] in
private theorem root_zero (S : D4Geometry K) (α : S.roots.Root) :
    S.chevalley.x α 0 = 1 := by
  have h := S.chevalley_spec.2.2.2.1 α 0 0
  simpa using h

omit [IsAlgClosed k] in
private theorem root_inverse [CharP k 2] (S : D4Geometry K)
    (α : S.roots.Root) (t : k) : (S.chevalley.x α t)⁻¹ = S.chevalley.x α t := by
  apply inv_eq_of_mul_eq_one_right
  rw [S.chevalley_spec.2.2.2.1, CharTwo.add_self_eq_zero, root_zero]

/-- First-coefficient conjugation along a Chevalley commutator word. -/
theorem rootOperator_conjugation_of_word [CharP k 2] (S : D4Geometry K)
    (ρ : RationalRepresentation K V) (hρ : IsRationalRepresentation ρ)
    (α β : S.roots.Root) (t : k)
    (word : List (ChevalleyCommutatorTerm S.roots.Root))
    (c : ChevalleyCommutatorTerm S.roots.Root → k)
    (hpos : ∀ q ∈ word, 0 < q.j)
    (hw : ∀ u, S.chevalley.x β t * S.chevalley.x α u * S.chevalley.x β t *
      S.chevalley.x α u =
        (word.map fun q => S.chevalley.x q.root (c q * t ^ q.i * u ^ q.j)).prod) :
    (ρ.action (S.chevalley.x β t)).val * rootOperator S ρ hρ α *
        (ρ.action (S.chevalley.x β t)⁻¹).val =
      rootOperator S ρ hρ α +
        (word.map fun q => if q.j = 1 then
          (c q * t ^ q.i) • rootOperator S ρ hρ q.root else 0).sum := by
  let p := operatorPolynomial S ρ hρ
  let R := (ρ.action (S.chevalley.x β t)).val
  let f := fun q : ChevalleyCommutatorTerm S.roots.Root =>
    powerScaledPolynomial (p q.root) (c q * t ^ q.i) q.j
  have hp : Polynomial.C R * p α * Polynomial.C R = (word.map f).prod * p α := by
    apply scalarEval_ext (k := k)
    intro u
    simp only [map_mul, scalarEval_C, map_list_prod, List.map_map,
      Function.comp_def, f, powerScaledPolynomial_eval, p, operatorPolynomial_eval]
    have he : S.chevalley.x β t * S.chevalley.x α u * S.chevalley.x β t =
        (word.map fun q => S.chevalley.x q.root (c q * t ^ q.i * u ^ q.j)).prod *
          S.chevalley.x α u := by
      rw [← hw]
      rw [mul_assoc (_ * _ * _) _ _]
      have hxx : S.chevalley.x α u * S.chevalley.x α u = 1 := by
        simpa only [root_inverse] using inv_mul_cancel (S.chevalley.x α u)
      rw [hxx, mul_one]
    have he' := congrArg ((Units.coeHom _).comp ρ.action) he
    simpa only [map_mul, map_list_prod, List.map_map,
      Function.comp_def, MonoidHom.comp_apply, Units.coeHom_apply, R] using he'
  have hz : ∀ q ∈ word.map f, q.coeff 0 = 1 := by
    intro q hq
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hq
    dsimp only [f]
    rw [powerScaledPolynomial_coeff_zero _ _ _ (hpos r hr)]
    exact operatorPolynomial_coeff_zero S ρ hρ r.root
  have hc := congrArg (fun q : Polynomial (Module.End k V) => q.coeff 1) hp
  simp only [Polynomial.mul_coeff_one, Polynomial.mul_coeff_zero,
    Polynomial.coeff_C_zero, Polynomial.coeff_C_succ,
    polynomial_prod_coeff_zero _ hz, polynomial_prod_coeff_one _ hz,
    List.map_map, Function.comp_def, f, powerScaledPolynomial_coeff_one,
    p, operatorPolynomial_coeff_one, operatorPolynomial_coeff_zero,
    one_mul, mul_one, mul_zero, zero_add, add_zero] at hc
  rw [root_inverse]
  exact hc

/-- Independent roots conjugate every first coefficient into the actual root algebra. -/
theorem rootOperator_conjugation_mem_of_independent [CharP k 2] (S : D4Geometry K)
    (ρ : RationalRepresentation K V) (hρ : IsRationalRepresentation ρ)
    (α β : S.roots.Root) (t : k)
    (hLI : AreLinearlyIndependentRoots S.roots (typeDRootPairing 2) S.rootEquiv β α) :
    (ρ.action (S.chevalley.x β t)).val * rootOperator S ρ hρ α *
        (ρ.action (S.chevalley.x β t)⁻¹).val ∈ rootOperatorAlgebra S ρ hρ := by
  obtain ⟨word, c, _, _, hvalid, _, hw⟩ := S.chevalley_spec.2.2.2.2.1 β α hLI
  rw [rootOperator_conjugation_of_word S ρ hρ α β t word c
    (fun q hq => ((hvalid q).mp hq).2.1) (by
      intro u
      simpa only [root_inverse] using hw t u)]
  apply (rootOperatorAlgebra S ρ hρ).add_mem (Algebra.subset_adjoin ⟨α, rfl⟩)
  apply Subalgebra.list_sum_mem
  intro A hA
  obtain ⟨q, _, rfl⟩ := List.mem_map.mp hA
  split_ifs
  · exact (rootOperatorAlgebra S ρ hρ).smul_mem (Algebra.subset_adjoin ⟨q.root, rfl⟩) _
  · exact (rootOperatorAlgebra S ρ hρ).zero_mem

/-- Conjugation and a scalar reparametrization pass to first coefficients. -/
theorem rootOperator_conjugation_of_curve (S : D4Geometry K)
    (ρ : RationalRepresentation K V) (hρ : IsRationalRepresentation ρ)
    (g : K.Point) (α β : S.roots.Root) (c : k)
    (h : ∀ t, g * S.chevalley.x α t * g⁻¹ = S.chevalley.x β (c * t)) :
    (ρ.action g).val * rootOperator S ρ hρ α * (ρ.action g⁻¹).val =
      c • rootOperator S ρ hρ β := by
  have hp : Polynomial.C (ρ.action g).val * operatorPolynomial S ρ hρ α *
      Polynomial.C (ρ.action g⁻¹).val = scaledPolynomial (operatorPolynomial S ρ hρ β) c := by
    apply scalarEval_ext (k := k)
    intro t
    simp only [map_mul, scalarEval_C, scaledPolynomial_eval, operatorPolynomial_eval]
    simpa only [map_mul, Units.val_mul] using congrArg (fun x => (ρ.action x).val) (h t)
  have hc := congrArg (fun q : Polynomial (Module.End k V) => q.coeff 1) hp
  simpa only [Polynomial.mul_coeff_one, Polynomial.mul_coeff_zero,
    Polynomial.coeff_C_zero, Polynomial.coeff_C_succ, scaledPolynomial_coeff,
    pow_one, operatorPolynomial_coeff_one, operatorPolynomial_coeff_zero,
    mul_one, zero_mul, mul_zero, add_zero, zero_add] using hc

/-- A root subgroup fixes its own first coefficient under conjugation. -/
theorem rootOperator_conjugation_self (S : D4Geometry K)
    (ρ : RationalRepresentation K V) (hρ : IsRationalRepresentation ρ)
    (α : S.roots.Root) (t : k) :
    (ρ.action (S.chevalley.x α t)).val * rootOperator S ρ hρ α *
      (ρ.action (S.chevalley.x α t)⁻¹).val = rootOperator S ρ hρ α := by
  simpa only [one_smul] using rootOperator_conjugation_of_curve S ρ hρ
    (S.chevalley.x α t) α α 1 (by
      intro u
      rw [one_mul, mul_inv_eq_iff_eq_mul,
        S.chevalley_spec.2.2.2.1, S.chevalley_spec.2.2.2.1, add_comm])

omit [IsAlgClosed k] [FiniteDimensional k V] in
private theorem conjugation_apply (ρ : RationalRepresentation K V)
    (g : K.Point) (A : Module.End k V) :
    ((Bor1.conjEndRationalRepresentation ρ).action g).val A =
      (ρ.action g).val * A * (ρ.action g⁻¹).val := by
  change (ρ.action g).val * A * ((ρ.action g)⁻¹).val = _
  rw [map_inv]

omit [IsAlgClosed k] in
private theorem raw_coroot_inverse (S : D4Geometry K)
    (α : S.roots.Root) (t : kˣ) :
    S.chevalley.h α t⁻¹ = (S.chevalley.h α t)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [S.chevalley_spec.2.2.2.2.2.2.1, inv_mul_cancel,
    S.chevalley_spec.2.2.1, inv_mul_cancel]

/-- The preserved raw coroot has the inverse exponent on a left conjugation action. -/
theorem rootOperator_conjugation_coroot (S : D4Geometry K)
    (ρ : RationalRepresentation K V) (hρ : IsRationalRepresentation ρ)
    (α β : S.roots.Root) (t : kˣ) :
    (ρ.action (S.chevalley.h β t)).val * rootOperator S ρ hρ α *
      (ρ.action (S.chevalley.h β t)⁻¹).val =
        ((t : k)⁻¹) ^ S.roots.pairing α β • rootOperator S ρ hρ α := by
  apply rootOperator_conjugation_of_curve
  intro s
  have h := S.chevalley_spec.2.2.2.2.2.2.2.2.2.2.2.1 α β s t⁻¹
  simpa only [raw_coroot_inverse, inv_inv, Units.val_inv_eq_inv_val] using h

private theorem rootOperator_conjugation_weyl_self [CharP k 2] (S : D4Geometry K)
    (ρ : RationalRepresentation K V) (hρ : IsRationalRepresentation ρ)
    (α : S.roots.Root) :
    ((Bor1.conjEndRationalRepresentation ρ).action (S.chevalley.n α 1)).val
      (rootOperator S ρ hρ α) = rootOperator S ρ hρ (S.roots.neg α) := by
  rw [conjugation_apply, rootOperator_weyl]
  have hr : S.roots.reflect α α = S.roots.neg α := by
    apply S.rootEquiv.injective
    rw [S.based.2.1, S.based.2.2.1]
  rw [hr, mul_assoc, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one,
    Units.val_one, mul_one]

/-- The first root coefficient of conjugation is the operator commutator
(written as a sum in characteristic two). -/
theorem rootOperator_conjugationRepresentation [CharP k 2] (S : D4Geometry K)
    (ρ : RationalRepresentation K V) (hρ : IsRationalRepresentation ρ)
    (α : S.roots.Root) (A : Module.End k V) :
    rootOperator S (Bor1.conjEndRationalRepresentation ρ)
      (Bor1.conjEndRationalRepresentation_isRational ρ hρ) α A =
        rootOperator S ρ hρ α * A + A * rootOperator S ρ hρ α := by
  apply sub_eq_zero.mp
  rw [← Module.forall_dual_apply_eq_zero_iff k]
  intro l
  let τ := Bor1.conjEndRationalRepresentation ρ
  let hτ := Bor1.conjEndRationalRepresentation_isRational ρ hρ
  let p := operatorPolynomial S ρ hρ α
  have hp : curvePolynomial τ hτ (rootMorphism S α) l A =
      polynomialDual l (p * Polynomial.C A * p) := by
    apply Polynomial.funext
    intro t
    rw [curvePolynomial_eval, rootMorphism_apply, polynomialDual_eval]
    simp only [map_mul, scalarEval_C, p, operatorPolynomial_eval]
    rw [conjugation_apply, root_inverse]
  change l (curveOperator τ hτ (rootMorphism S α) A - _) = 0
  rw [map_sub, dual_curveOperator, hp, polynomialDual_coeff]
  simp only [Polynomial.mul_coeff_one, Polynomial.mul_coeff_zero,
    Polynomial.coeff_C_zero, Polynomial.coeff_C_succ,
    p, operatorPolynomial_coeff_one, operatorPolynomial_coeff_zero,
    one_mul, mul_one, mul_zero, zero_add, sub_eq_zero]
  rw [add_comm]

/-- The opposite-root conjugation polynomial is quadratic, with constant
coefficient `Eα`, linear coefficient the bracket, and top coefficient `E₋α`.
The degree bound and top coefficient use the actual raw `n/h` relations. -/
theorem rootOperator_conjugation_opposite [CharP k 2] (S : D4Geometry K)
    (ρ : RationalRepresentation K V) (hρ : IsRationalRepresentation ρ)
    (α : S.roots.Root) (t : k) :
    (ρ.action (S.chevalley.x (S.roots.neg α) t)).val * rootOperator S ρ hρ α *
        (ρ.action (S.chevalley.x (S.roots.neg α) t)⁻¹).val =
      rootOperator S ρ hρ α +
        t • (rootOperator S ρ hρ (S.roots.neg α) * rootOperator S ρ hρ α +
          rootOperator S ρ hρ α * rootOperator S ρ hρ (S.roots.neg α)) +
        t ^ 2 • rootOperator S ρ hρ (S.roots.neg α) := by
  let τ := Bor1.conjEndRationalRepresentation ρ
  let hτ := Bor1.conjEndRationalRepresentation_isRational ρ hρ
  let E := rootOperator S ρ hρ α
  have hx (s : k) : (τ.action (S.chevalley.x α s)).val E = E := by
    rw [conjugation_apply]
    exact rootOperator_conjugation_self S ρ hρ α s
  have hh (s : kˣ) : (τ.action (S.chevalley.h α s)).val E = ((s : k)⁻¹) ^ 2 • E := by
    rw [conjugation_apply, rootOperator_conjugation_coroot,
      S.realized.2.2.2.2.2.2.1, zpow_ofNat]
  have hn : (τ.action (S.chevalley.n α 1)).val E =
      rootOperator S ρ hρ (S.roots.neg α) :=
    rootOperator_conjugation_weyl_self S ρ hρ α
  apply sub_eq_zero.mp
  rw [← Module.forall_dual_apply_eq_zero_iff k]
  intro l
  let q := curvePolynomial τ hτ (rootMorphism S (S.roots.neg α)) l E
  have hq : q = Polynomial.C (l E) +
      Polynomial.monomial 1 (q.coeff 1) +
      Polynomial.monomial 2 (l (rootOperator S ρ hρ (S.roots.neg α))) := by
    ext j
    match j with
    | 0 => simp [q, curvePolynomial_coeff_zero]
    | 1 => simp [Polynomial.coeff_monomial]
    | 2 =>
      have hc := negative_rootPolynomial_top_coeff_of_left_exponent S τ hτ α 2 E hx hh l
      simpa only [q, hn, Polynomial.coeff_add, Polynomial.coeff_C_succ,
        Polynomial.coeff_monomial, if_false, if_true, zero_add,
        show ¬ (1 : ℕ) = 2 by decide] using hc
    | j + 3 =>
      have hc := negative_rootPolynomial_coeff_eq_zero_of_left_exponent
        S τ hτ α 2 E hx hh l (j + 3) (by omega)
      simpa [q, Polynomial.coeff_monomial, show ¬ (1 : ℕ) = j + 3 by omega,
        show ¬ (2 : ℕ) = j + 3 by omega] using hc
  have hc : q.coeff 1 = l (rootOperator S ρ hρ (S.roots.neg α) * E +
      E * rootOperator S ρ hρ (S.roots.neg α)) := by
    rw [show q.coeff 1 = l (curveOperator τ hτ (rootMorphism S (S.roots.neg α)) E)
      from (dual_curveOperator τ hτ _ l E).symm]
    exact congrArg l (rootOperator_conjugationRepresentation S ρ hρ (S.roots.neg α) E)
  have he := congrArg (fun p : Polynomial k => p.eval t) hq
  simp only [Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_monomial,
    pow_one, hc] at he
  have hqe : q.eval t = l ((ρ.action (S.chevalley.x (S.roots.neg α) t)).val * E *
      (ρ.action (S.chevalley.x (S.roots.neg α) t)⁻¹).val) := by
    rw [curvePolynomial_eval, rootMorphism_apply, conjugation_apply]
  rw [hqe] at he
  simpa only [map_sub, map_add, map_smul, smul_eq_mul, sub_eq_zero, mul_comm, E] using he

/-- Opposite roots also conjugate first coefficients into their generated algebra. -/
theorem rootOperator_conjugation_mem_opposite [CharP k 2] (S : D4Geometry K)
    (ρ : RationalRepresentation K V) (hρ : IsRationalRepresentation ρ)
    (α : S.roots.Root) (t : k) :
    (ρ.action (S.chevalley.x (S.roots.neg α) t)).val * rootOperator S ρ hρ α *
        (ρ.action (S.chevalley.x (S.roots.neg α) t)⁻¹).val ∈ rootOperatorAlgebra S ρ hρ := by
  rw [rootOperator_conjugation_opposite]
  let B := rootOperatorAlgebra S ρ hρ
  have hpos : rootOperator S ρ hρ α ∈ B := Algebra.subset_adjoin ⟨α, rfl⟩
  have hneg : rootOperator S ρ hρ (S.roots.neg α) ∈ B := Algebra.subset_adjoin ⟨_, rfl⟩
  exact B.add_mem (B.add_mem hpos
    (B.smul_mem (B.add_mem (B.mul_mem hneg hpos) (B.mul_mem hpos hneg)) t))
      (B.smul_mem hneg (t ^ 2))

/-- Every actual root element conjugates every first root coefficient into
the algebra generated by those coefficients. -/
theorem rootOperator_conjugation_mem [CharP k 2] (S : D4Geometry K)
    (ρ : RationalRepresentation K V) (hρ : IsRationalRepresentation ρ)
    (α β : S.roots.Root) (t : k) :
    (ρ.action (S.chevalley.x β t)).val * rootOperator S ρ hρ α *
        (ρ.action (S.chevalley.x β t)⁻¹).val ∈ rootOperatorAlgebra S ρ hρ := by
  by_cases heq : β = α
  · subst β
    rw [rootOperator_conjugation_self]
    exact Algebra.subset_adjoin ⟨α, rfl⟩
  by_cases hopp : β = S.roots.neg α
  · subst β
    exact rootOperator_conjugation_mem_opposite S ρ hρ α t
  apply rootOperator_conjugation_mem_of_independent
  have hlin := RootPairing.IsReduced.linearIndependent (typeDRootPairing 2)
    (show S.rootEquiv β ≠ S.rootEquiv α from fun h => heq (S.rootEquiv.injective h))
    (show (typeDRootPairing 2).root (S.rootEquiv β) ≠
      -(typeDRootPairing 2).root (S.rootEquiv α) from by
        intro h
        apply hopp
        apply S.rootEquiv.injective
        rw [S.based.2.2.1]
        exact (typeDRootPairing 2).root_eq_neg_iff.mp h)
  simpa only [AreLinearlyIndependentRoots] using (LinearIndependent.pair_iff.mp hlin)

end
end Triality.RestrictedWeights.SteinbergTensors.AlgebraicTensor.RestrictedStep.RootDensity.NegativeCyclicityLeft
