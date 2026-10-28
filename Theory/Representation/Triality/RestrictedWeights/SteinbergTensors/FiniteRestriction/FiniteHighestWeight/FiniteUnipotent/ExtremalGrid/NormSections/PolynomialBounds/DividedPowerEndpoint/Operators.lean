module

public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.FiniteHighestWeight.FiniteUnipotent.ExtremalGrid.Dimension.WeylCovers.DimensionBound.RootOperators
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.LeftWeights.Roots

/-!
# Divided coefficients and extremal weights for the supplied D4 curves

Reuse the higher coefficient operators from the cyclic-dimension development.
Polynomial uniqueness identifies them with the actual supplied root curves.
Parameter changes and torus conjugation then give the scalar-rescaling and
weight-shift equations in every degree, without dividing by factorials.

The standard twelve-root expansion has total simple-root coordinates
`(6,10,6,6)` and hence fundamental-weight coordinates `(2,2,2,2)`.
This determines the weights of both literal ordered top products. It does
not assert that either product is nonzero, or that its weight space is a line.
Those are independent representation-theoretic obligations.

Source: Steinberg, *Representations of algebraic groups*, Nagoya Math. J. 22
(1963), Sections 2.8 and 4.3; `refs/KGroup/GLS3/Chapter2St2.tex`, 13.2(d).
Direct root characters are the inverses of the raw GLS characters, as in the
triality coroot convention audit. The positive roots and their order are unchanged.
-/

open Theory.AlgebraicGroup
namespace Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.ExtremalGrid.DividedPowerEndpoint
open AlgebraicTensor.RestrictedStep CyclicDimension
public noncomputable section
universe u v
variable {k : Type u} [Field k] [IsAlgClosed k]
variable {K : Variety k} [AlgebraicGroup K]
variable {V : Type v} [AddCommGroup V] [Module k V] [FiniteDimensional k V]

/-- The scalar orbit polynomial is unique over the algebraically closed field. -/
theorem curvePolynomial_unique (rho : RationalRepresentation K V)
    (hr : IsRationalRepresentation rho) (x : Morphism (KPlus k) K)
    (l : Module.Dual k V) (v : V) (p : Polynomial k)
    (hp : ∀ t, p.eval t = l ((rho.action (x.onPoints (kPlusPoint t))).val v)) :
    p = curvePolynomial rho hr x l v := by
  apply Polynomial.funext
  intro t
  rw [hp, curvePolynomial_eval]

/-- Degree one agrees with the pre-existing first-coefficient operator. -/
theorem curveCoefficient_one (rho : RationalRepresentation K V)
    (hr : IsRationalRepresentation rho) (x : Morphism (KPlus k) K) :
    curveCoefficient rho hr x 1 = curveOperator rho hr x := rfl

/-- A scaled intertwining identity of actual curves holds in every polynomial degree. -/
theorem curveCoefficient_intertwine (rho : RationalRepresentation K V)
    (hr : IsRationalRepresentation rho) (x y : Morphism (KPlus k) K)
    (A B : Module.End k V) (c : k)
    (h : ∀ (t : k) (v : V), A ((rho.action (x.onPoints (kPlusPoint t))).val v) =
      (rho.action (y.onPoints (kPlusPoint (c * t)))).val (B v)) (m : ℕ) :
    A * curveCoefficient rho hr x m =
      c ^ m • (curveCoefficient rho hr y m * B) := by
  ext v
  apply (Module.finBasis k V).repr.injective
  ext i
  let l := (Module.finBasis k V).coord i
  have hp : curvePolynomial rho hr x (l.comp A) v =
      (curvePolynomial rho hr y l (B v)).comp (Polynomial.C c * Polynomial.X) := by
    apply Polynomial.funext
    intro t
    simp only [curvePolynomial_eval, Polynomial.eval_comp, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_X, LinearMap.comp_apply, h]
  have hc := congrArg (fun p : Polynomial k => p.coeff m) hp
  rw [← dual_curveCoefficient, Polynomial.comp_C_mul_X_coeff,
    ← dual_curveCoefficient] at hc
  change l (A (curveCoefficient rho hr x m v)) =
    l (c ^ m • curveCoefficient rho hr y m (B v))
  simpa only [LinearMap.comp_apply, map_smul, smul_eq_mul, mul_comm] using hc

/-- Rescaling the curve parameter multiplies degree `m` by `c^m`. -/
theorem curveCoefficient_rescale (rho : RationalRepresentation K V)
    (hr : IsRationalRepresentation rho) (x y : Morphism (KPlus k) K) (c : k)
    (h : ∀ t, x.onPoints (kPlusPoint t) = y.onPoints (kPlusPoint (c * t))) (m : ℕ) :
    curveCoefficient rho hr x m = c ^ m • curveCoefficient rho hr y m := by
  simpa only [one_mul, mul_one] using curveCoefficient_intertwine rho hr x y 1 1 c
    (fun t v => by simp only [Module.End.one_apply, h t]) m

/-- Any two regular parametrizations of one subgroup change the operators by
nonzero scalar powers. No compatibility between opposite parameters is assumed. -/
theorem coefficient_change_parameter (rho : RationalRepresentation K V)
    (hr : IsRationalRepresentation rho) (X : ClosedSubgroup K)
    (x y : OneParameterParametrization X.carrierVariety) :
    ∃ c : k, c ≠ 0 ∧ ∀ m : ℕ,
      curveCoefficient rho hr (X.inclusion.comp y.hom) m =
        c ^ m • curveCoefficient rho hr (X.inclusion.comp x.hom) m := by
  obtain ⟨c, hc, _⟩ := oneParameterParametrization_eq_rescale x y
  refine ⟨c, hc.1, fun m => curveCoefficient_rescale rho hr _ _ c ?_ m⟩
  intro t
  exact congrArg X.includePoint (hc.2 t)

variable [CharP k 2]

omit [IsAlgClosed k] in
/-- The regular root morphism is exactly the supplied included parametrization. -/
theorem rootCurve_apply (S : Geometry K) (a : S.roots.Root) (t : k) :
    (rootCurve S a).onPoints (kPlusPoint t) =
      (S.roots.rootSubgroup a).includePoint ((S.rootParameter a).value t) := rfl

omit [IsAlgClosed k] [FiniteDimensional k V] in
/-- The ambient ordered root product acts by the endomorphism product in the same order. -/
theorem action_orderedRootPoint (S : Geometry K) (rho : RationalRepresentation K V)
    (r : Fin 12 → S.roots.Root) (x : Fin 12 → k) :
    (rho.action (orderedRootPoint S r x)).val =
      (List.ofFn fun i => (rho.action ((rootCurve S (r i)).onPoints (kPlusPoint (x i)))).val).prod := by
  let f : Variety.Point K →* Module.End k V := (Units.coeHom _).comp rho.action
  have h := map_list_prod f (List.ofFn fun i =>
    (S.roots.rootSubgroup (r i)).includePoint ((S.rootParameter (r i)).value (x i)))
  simpa only [f, orderedRootPoint, rootCurve_apply, MonoidHom.comp_apply,
    Units.coeHom_apply, List.map_ofFn, Function.comp_def] using h

/-- The actual degree-`m` root coefficient, without division by factorials. -/
abbrev rootDividedPower (S : Geometry K) (rho : RationalRepresentation K V)
    (hr : IsRationalRepresentation rho) (a : S.roots.Root) (m : ℕ) : Module.End k V :=
  rootCoefficient S rho hr a m

/-- The divided-power operator has the specified value under every covector. -/
theorem dual_rootDividedPower (S : Geometry K) (rho : RationalRepresentation K V)
    (hr : IsRationalRepresentation rho) (a : S.roots.Root) (m : ℕ)
    (l : Module.Dual k V) (v : V) :
    l (rootDividedPower S rho hr a m v) =
      (curvePolynomial rho hr (rootCurve S a) l v).coeff m :=
  dual_curveCoefficient rho hr (rootCurve S a) m l v

/-- The degree-`m` coefficient shifts the weight by `m` times the direct root character. -/
theorem rootDividedPower_mem_weightSpace (S : Geometry K)
    (rho : RationalRepresentation K V) (hr : IsRationalRepresentation rho)
    (a : S.roots.Root) (m : ℕ) {mu : TorusWeight S.torus} {v : V}
    (hv : v ∈ weightSpace rho S.torus mu) :
    rootDividedPower S rho hr a m v ∈
      weightSpace rho S.torus (mu * (LeftWeights.leftRootCharacter S.roots a) ^ m) := by
  intro t
  let A : Module.End k V := (rho.action (S.torus.includePoint t)).val
  let c := (LeftWeights.leftRootCharacter S.roots a).pointCharacter t
  have he := curveCoefficient_intertwine rho hr (rootCurve S a) (rootCurve S a) A A c
    (by
      intro s w
      have hg := LeftWeights.direct_root_conjugation S.roots S.realized a
        (S.rootParameter a) s t
      have hh : S.torus.includePoint t * (rootCurve S a).onPoints (kPlusPoint s) =
          (rootCurve S a).onPoints (kPlusPoint (c * s)) * S.torus.includePoint t := by
        rw [rootCurve_apply, rootCurve_apply, ← hg]
        group
      have h := congrArg (fun g => (rho.action g).val w) hh
      simpa only [map_mul, Units.val_mul, Module.End.mul_apply, A] using h) m
  have he' := congrArg (fun L : Module.End k V => L v) he
  have ht := hv t
  change A v = _ at ht
  change A (rootDividedPower S rho hr a m v) =
    c ^ m • rootDividedPower S rho hr a m (A v) at he'
  rw [ht, map_smul, smul_smul, mul_comm (c ^ m)] at he'
  have hp : ((LeftWeights.leftRootCharacter S.roots a) ^ m).pointCharacter t = c ^ m := by
    clear he he'
    induction m with
    | zero => simp only [pow_zero]; rfl
    | succ m ih =>
        rw [pow_succ]
        change ((LeftWeights.leftRootCharacter S.roots a) ^ m).pointCharacter t * c = _
        rw [ih, pow_succ]
  change A (rootDividedPower S rho hr a m v) =
    (mu.pointCharacter t * ((LeftWeights.leftRootCharacter S.roots a) ^ m).pointCharacter t) • _
  rw [hp]
  exact he'

/-- Weights of operator words, with multiplication as composition in `Module.End`. -/
theorem word_mem_weightSpace (S : Geometry K)
    (rho : RationalRepresentation K V) (hr : IsRationalRepresentation rho)
    (L : List (S.roots.Root × ℕ)) {mu : TorusWeight S.torus} {v : V}
    (hv : v ∈ weightSpace rho S.torus mu) :
    (L.map fun a => rootDividedPower S rho hr a.1 a.2).prod v ∈
      weightSpace rho S.torus
        (mu * (L.map fun a => (LeftWeights.leftRootCharacter S.roots a.1) ^ a.2).prod) := by
  induction L with
  | nil => simpa using hv
  | cons a L ih =>
    simp only [List.map_cons, List.prod_cons, Module.End.mul_apply]
    rw [mul_comm ((LeftWeights.leftRootCharacter S.roots a.1) ^ a.2), ← mul_assoc]
    exact rootDividedPower_mem_weightSpace S rho hr a.1 a.2 ih

open Theory.AlgebraicGroup.StandardRootSystem D4RestrictedWeight
open scoped BigOperators

/-- Integral left-weight coordinates of an actual root. -/
@[expose] def rootWeight (S : Geometry K) (a : S.roots.Root) : Weight :=
  fun i => S.roots.pairing a (S.simpleRoot i).val

omit [IsAlgClosed k] in
/-- These coordinates represent the direct, inverse-raw root character. -/
theorem rootWeight_character (S : Geometry K) (a : S.roots.Root) :
    S.leftWeightEmbedding (rootWeight S a) = LeftWeights.leftRootCharacter S.roots a := by
  obtain ⟨b, hb⟩ := S.weight.surjective (S.roots.rootWeight a)
  have hcoord : b.toAdd = rootWeight S a := by
    funext i
    rw [← S.weight_coordinate b.toAdd i]
    change S.roots.weightPairing (S.weight b) _ = _
    rw [hb]
    exact S.realized.weightPairing_rootWeight a _
  rw [S.leftWeightEmbedding_eq_inv, ← hcoord]
  exact congrArg Inv.inv hb

private theorem model_pairing_sum (j : Fin 4) :
    (∑ i : Fin 12, (typeDRootPairing 2).pairing
      (Triality.Standard.PositiveCoordinates.rootIndex i) (typeDSimpleRootIndex 2 j)) = 2 := by
  have hc (l : Fin 4) :
      (∑ i : Fin 12, Triality.Standard.PositiveCoordinates.coefficients i l) =
        (![6,10,6,6] : Fin 4 → ℝ) l := by
    fin_cases l <;> norm_num [Triality.Standard.PositiveCoordinates.coefficients,
      Fin.sum_univ_succ]
  have hp (i : Fin 12) : (typeDRootPairing 2).pairing
      (Triality.Standard.PositiveCoordinates.rootIndex i) (typeDSimpleRootIndex 2 j) =
        ∑ l : Fin 4, Triality.Standard.PositiveCoordinates.coefficients i l *
          typeDCartanMatrix 2 l j := by
    rw [← RootPairing.root_coroot'_eq_pairing,
      Triality.Standard.PositiveCoordinates.root_expansion, map_sum]
    simp only [map_smul, RootPairing.root_coroot'_eq_pairing,
      typeDRootPairing_simpleIndex_pairing, smul_eq_mul]
  simp only [hp]
  rw [Finset.sum_comm]
  simp only [← Finset.sum_mul, hc]
  have hm : typeDCartanMatrix 2 =
      !![(2 : ℤ), -1, 0, 0; -1, 2, -1, -1; 0, -1, 2, 0; 0, -1, 0, 2] := by
    ext a b
    fin_cases a <;> fin_cases b <;> norm_num [typeDCartanMatrix] <;> decide
  rw [hm]
  fin_cases j <;> norm_num [Fin.sum_univ_succ]

omit [IsAlgClosed k] in
/-- The literal twelve-root list sums to twice the sum of the fundamental weights. -/
theorem positive_rootWeight_sum (S : Geometry K) :
    (∑ i : Fin 12, rootWeight S (positiveCoordinateRoot S i)) = fun _ => 2 := by
  funext j
  change (∑ i : Fin 12, rootWeight S (positiveCoordinateRoot S i) j) = 2
  apply Int.cast_injective (α := ℝ)
  push_cast
  have hp (i : Fin 12) : (rootWeight S (positiveCoordinateRoot S i) j : ℝ) =
      (typeDRootPairing 2).pairing (Triality.Standard.PositiveCoordinates.rootIndex i)
        (typeDSimpleRootIndex 2 j) := by
    simpa only [rootWeight, positiveCoordinateRoot, Equiv.apply_symm_apply,
      S.simpleRoot_index] using S.based.1 (positiveCoordinateRoot S i) (S.simpleRoot j).val
  simp only [hp]
  exact model_pairing_sum j

omit [IsAlgClosed k] in
/-- The character shift of the ordered positive top word is `chi^2`. -/
theorem positive_top_character (S : Geometry K) (n : ℕ) :
    (List.ofFn fun i : Fin 12 =>
      (LeftWeights.leftRootCharacter S.roots (positiveCoordinateRoot S i)) ^ (2 ^ n - 1)).prod =
      S.leftWeightEmbedding (maximalRestrictedWeight n) ^ 2 := by
  rw [List.prod_ofFn]
  simp only [← rootWeight_character, ← S.leftWeightEmbedding_nsmul]
  rw [← S.leftWeightEmbedding_sum, ← Finset.smul_sum, positive_rootWeight_sum]
  congr 1
  funext j
  simp only [Pi.smul_apply, nsmul_eq_mul, maximalRestrictedWeight]
  have hn : 1 ≤ (2 : ℕ) ^ n := Nat.one_le_pow n 2 (by decide)
  rw [Nat.cast_sub hn]
  push_cast
  ring

omit [IsAlgClosed k] in
/-- Negating precisely the same root list inverts its total character shift. -/
theorem negative_top_character (S : Geometry K) (n : ℕ) :
    (List.ofFn fun i : Fin 12 =>
      (LeftWeights.leftRootCharacter S.roots (negativeCoordinateRoot S i)) ^ (2 ^ n - 1)).prod =
      (S.leftWeightEmbedding (maximalRestrictedWeight n) ^ 2)⁻¹ := by
  have hneg (i : Fin 12) : LeftWeights.leftRootCharacter S.roots (negativeCoordinateRoot S i) =
      (LeftWeights.leftRootCharacter S.roots (positiveCoordinateRoot S i))⁻¹ := by
    exact congrArg Inv.inv (S.realized.2.2.2.1 _)
  simp only [hneg, inv_pow, List.prod_ofFn, Finset.prod_inv_distrib]
  rw [← List.prod_ofFn, positive_top_character]

/-- The literal ordered word with all twelve exponents `2^n - 1`.
The rightmost operator acts first, exactly as for `orderedRootPoint`. -/
@[expose] def topOperator (S : Geometry K) (rho : RationalRepresentation K V)
    (hr : IsRationalRepresentation rho) (r : Fin 12 → S.roots.Root) (n : ℕ) : Module.End k V :=
  (List.ofFn fun i : Fin 12 => rootDividedPower S rho hr (r i) (2 ^ n - 1)).prod

/-- The ordered top word shifts a weight by the product of its root characters. -/
theorem topOperator_mem_weightSpace (S : Geometry K)
    (rho : RationalRepresentation K V) (hr : IsRationalRepresentation rho)
    (r : Fin 12 → S.roots.Root) (n : ℕ) {mu : TorusWeight S.torus} {v : V}
    (hv : v ∈ weightSpace rho S.torus mu) :
    topOperator S rho hr r n v ∈ weightSpace rho S.torus
      (mu * (List.ofFn fun i : Fin 12 =>
        (LeftWeights.leftRootCharacter S.roots (r i)) ^ (2 ^ n - 1)).prod) := by
  simpa only [topOperator, List.map_ofFn, Function.comp_def] using word_mem_weightSpace S rho hr
    (List.ofFn fun i : Fin 12 => (r i, 2 ^ n - 1)) hv

/-- A negative top word on the positive highest weight has the inverse weight,
with no nonvanishing assertion. -/
theorem negative_top_mem_inverse_weightSpace (S : Geometry K)
    (rho : RationalRepresentation K V) (hr : IsRationalRepresentation rho)
    (n : ℕ) {v : V}
    (hv : v ∈ weightSpace rho S.torus (S.leftWeightEmbedding (maximalRestrictedWeight n))) :
    topOperator S rho hr (negativeCoordinateRoot S) n v ∈ weightSpace rho S.torus
      (S.leftWeightEmbedding (maximalRestrictedWeight n))⁻¹ := by
  have h := topOperator_mem_weightSpace S rho hr (negativeCoordinateRoot S) n hv
  rw [negative_top_character, pow_two, mul_inv_rev, ← mul_assoc, mul_inv_cancel, one_mul] at h
  exact h

/-- A positive top word on the opposite highest weight has the positive weight,
with no nonvanishing assertion. -/
theorem positive_top_mem_weightSpace (S : Geometry K)
    (rho : RationalRepresentation K V) (hr : IsRationalRepresentation rho)
    (n : ℕ) {v : V}
    (hv : v ∈ weightSpace rho S.torus (S.leftWeightEmbedding (maximalRestrictedWeight n))⁻¹) :
    topOperator S rho hr (positiveCoordinateRoot S) n v ∈ weightSpace rho S.torus
      (S.leftWeightEmbedding (maximalRestrictedWeight n)) := by
  have h := topOperator_mem_weightSpace S rho hr (positiveCoordinateRoot S) n hv
  rw [positive_top_character, pow_two, ← mul_assoc, inv_mul_cancel, one_mul] at h
  exact h

/-- Unique scalar polynomials for the literal root curves in the task contract. -/
theorem rootPolynomial_existsUnique (S : Geometry K) (rho : RationalRepresentation K V)
    (hr : IsRationalRepresentation rho) (a : S.roots.Root) (l : Module.Dual k V) (v : V) :
    ∃! p : Polynomial k, ∀ t : k, p.eval t =
      l ((rho.action ((S.roots.rootSubgroup a).includePoint ((S.rootParameter a).value t))).val v) := by
  refine ⟨curvePolynomial rho hr (rootCurve S a) l v, ?_, ?_⟩
  · intro t
    exact curvePolynomial_eval rho hr (rootCurve S a) l v t
  · intro p hp
    exact curvePolynomial_unique rho hr (rootCurve S a) l v p hp

/-- Coefficient extraction from any polynomial representing the actual scalar orbit. -/
theorem dual_rootDividedPower_eq_of_polynomial (S : Geometry K)
    (rho : RationalRepresentation K V) (hr : IsRationalRepresentation rho)
    (a : S.roots.Root) (m : ℕ) (l : Module.Dual k V) (v : V) (p : Polynomial k)
    (hp : ∀ t : k, p.eval t =
      l ((rho.action ((S.roots.rootSubgroup a).includePoint ((S.rootParameter a).value t))).val v)) :
    l (rootDividedPower S rho hr a m v) = p.coeff m := by
  rw [curvePolynomial_unique rho hr (rootCurve S a) l v p hp]
  exact dual_rootDividedPower S rho hr a m l v

end
end Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.ExtremalGrid.DividedPowerEndpoint
