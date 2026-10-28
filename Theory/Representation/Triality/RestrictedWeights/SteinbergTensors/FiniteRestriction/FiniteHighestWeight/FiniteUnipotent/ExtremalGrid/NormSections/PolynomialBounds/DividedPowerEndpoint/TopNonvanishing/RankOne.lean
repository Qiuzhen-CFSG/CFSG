module

public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.FiniteHighestWeight.FiniteUnipotent.ExtremalGrid.NormSections.PolynomialBounds.DividedPowerEndpoint.Operators
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.Exhaustivity.ClassBound.Generation.FixedOpposition.AmbientNormalizer.SimpleReflections.CorootRealization.Comparison
public import Theory.AlgebraicGroup.Representations.Algebraic.SL2HighestWeight

/-!
# The rank-one divided-power endpoint

The open SL₂ Bruhat cell gives p(t) = t^m q(t⁻¹) for scalar root-orbit
polynomials of an upper-fixed vector of diagonal weight m. Polynomial
reflection extracts the coefficient in degree m, which is the Weyl translate
of the original vector. This argument is valid in arbitrary characteristic
and requires neither irreducibility nor a bound on the ambient module.

The elementary SL₂ matrix calculations below follow the private calculations
in `Theory.AlgebraicGroup.Representations.Algebraic.SL2HighestWeight`.
Source: Steinberg, Representations of algebraic groups (1963), §4.3,
and the rank-one Bruhat relation of GLS3 §1.12.
-/

open Theory.AlgebraicGroup
namespace Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.ExtremalGrid.DividedPowerEndpoint
open AlgebraicTensor.RestrictedStep CyclicDimension
public noncomputable section
universe u v
variable {k : Type u} [Field k] [IsAlgClosed k]
variable {K : Variety k} [AlgebraicGroup K]
variable {V : Type v} [AddCommGroup V] [Module k V] [FiniteDimensional k V]

@[expose] def rankOneWeylPoint :
    Variety.Point (slVariety k 2) :=
  (slPointEquiv 2).symm
    (show Matrix.SpecialLinearGroup (Fin 2) k from
      ⟨!![0, -1; 1, 0], by simp [Matrix.det_fin_two_of]⟩)

private noncomputable def standardSL2TorusPoint (a : k) (ha : a ≠ 0) :
    Variety.Point (KMult k) :=
  (dPointEquiv 1).symm (fun _ => Units.mk0 a ha)

omit [IsAlgClosed k] in
private lemma standardSL2TorusPoint_coordinate (a : k) (ha : a ≠ 0) :
    (dPointEquiv 1 (standardSL2TorusPoint a ha) 0 : k) = a := by
  simp [standardSL2TorusPoint]

omit [IsAlgClosed k] in
private lemma standardSL2TorusPoint_inv (a : k) (ha : a ≠ 0) :
    (standardSL2TorusPoint a ha)⁻¹ =
      standardSL2TorusPoint a⁻¹ (inv_ne_zero ha) := by
  apply (dPointEquiv 1).injective
  change (fun _ : Fin 1 => Units.mk0 a ha)⁻¹ =
    fun _ : Fin 1 => Units.mk0 a⁻¹ (inv_ne_zero ha)
  funext i
  fin_cases i
  apply Units.ext
  simp

omit [IsAlgClosed k] in
private lemma standardSL2TorusPoint_inv_coordinate (a : k) (ha : a ≠ 0) :
    (dPointEquiv 1 ((standardSL2TorusPoint a ha)⁻¹) 0 : k) = a⁻¹ := by
  rw [standardSL2TorusPoint_inv, standardSL2TorusPoint_coordinate]

omit [IsAlgClosed k] in
private lemma standardSL2DiagonalEntries_zero (a : k) (ha : a ≠ 0) :
    (typeASLDiagonalEntries 1 (standardSL2TorusPoint a ha) 0 : k) = a := by
  rw [show (0 : Fin 2) = (0 : Fin 1).castSucc by rfl,
    typeASLDiagonalEntries_castSucc, standardSL2TorusPoint_coordinate]

omit [IsAlgClosed k] in
private lemma standardSL2DiagonalEntries_one (a : k) (ha : a ≠ 0) :
    (typeASLDiagonalEntries 1 (standardSL2TorusPoint a ha) 1 : k) = a⁻¹ := by
  rw [show (1 : Fin 2) = Fin.last 1 by rfl, typeASLDiagonalEntries_last]
  simp [standardSL2TorusPoint_coordinate]

omit [IsAlgClosed k] in
private lemma standardSL2DiagonalMatrix (a : k) (ha : a ≠ 0) :
    typeASLDiagonalMatrix 1 (standardSL2TorusPoint a ha) =
      !![a, 0; 0, a⁻¹] := by
  rw [typeASLDiagonalMatrix, Matrix.diagonal_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [standardSL2DiagonalEntries_zero, standardSL2DiagonalEntries_one]

private lemma standardSL2_diagonal_mul_weyl (a : k) (ha : a ≠ 0) :
    (standardSL2DiagonalMorphism (k := k)).onPoints
          (standardSL2TorusPoint a ha) * rankOneWeylPoint =
      rankOneWeylPoint *
        (standardSL2DiagonalMorphism (k := k)).onPoints
          ((standardSL2TorusPoint a ha)⁻¹) := by
  apply (slPointEquiv 2).injective
  change (slPointEquiv 2
      ((standardSL2DiagonalMorphism (k := k)).onPoints
        (standardSL2TorusPoint a ha))) *
        (slPointEquiv 2 (rankOneWeylPoint (k := k))) =
      (slPointEquiv 2 (rankOneWeylPoint (k := k))) *
        (slPointEquiv 2
          ((standardSL2DiagonalMorphism (k := k)).onPoints
            ((standardSL2TorusPoint a ha)⁻¹)))
  apply Subtype.ext
  change typeASLDiagonalMatrix 1 (standardSL2TorusPoint a ha) * !![0, -1; 1, 0] =
    !![0, -1; 1, 0] *
      typeASLDiagonalMatrix 1 ((standardSL2TorusPoint a ha)⁻¹)
  rw [standardSL2TorusPoint_inv, standardSL2DiagonalMatrix,
    standardSL2DiagonalMatrix]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two]

private lemma standardSL2_lower_bruhat (a : k) (ha : a ≠ 0) :
    (standardSL2LowerMorphism (k := k)).onPoints (kPlusPoint a) =
      (standardSL2UpperMorphism (k := k)).onPoints (kPlusPoint a⁻¹) *
        (standardSL2DiagonalMorphism (k := k)).onPoints
          (standardSL2TorusPoint a⁻¹ (inv_ne_zero ha)) *
        rankOneWeylPoint *
        (standardSL2UpperMorphism (k := k)).onPoints (kPlusPoint a⁻¹) := by
  apply (slPointEquiv 2).injective
  change Matrix.SpecialLinearGroup.transvection
        standardSL2LowerRootIndex.2 a =
      Matrix.SpecialLinearGroup.transvection
          standardSL2UpperRootIndex.2 a⁻¹ *
        (slPointEquiv 2
          ((standardSL2DiagonalMorphism (k := k)).onPoints
            (standardSL2TorusPoint a⁻¹ (inv_ne_zero ha)))) *
        (show Matrix.SpecialLinearGroup (Fin 2) k from
          ⟨!![0, -1; 1, 0], by simp [Matrix.det_fin_two_of]⟩) *
        Matrix.SpecialLinearGroup.transvection
          standardSL2UpperRootIndex.2 a⁻¹
  apply Subtype.ext
  change Matrix.transvection 1 0 a =
    Matrix.transvection 0 1 a⁻¹ *
      typeASLDiagonalMatrix 1
        (standardSL2TorusPoint a⁻¹ (inv_ne_zero ha)) *
      !![0, -1; 1, 0] * Matrix.transvection 0 1 a⁻¹
  rw [standardSL2DiagonalMatrix]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.transvection,
      Matrix.one_apply, Matrix.single_apply, ha]

omit [IsAlgClosed k] in
private lemma eval_reflect_natDegree (q : Polynomial k) (t : k) (ht : t ≠ 0) :
    (q.reflect q.natDegree).eval t = t ^ q.natDegree * q.eval t⁻¹ := by
  let _ : Invertible (t⁻¹) := invertibleOfNonzero (inv_ne_zero ht)
  have h := Polynomial.eval₂_reflect_mul_pow (RingHom.id k) (t⁻¹)
    q.natDegree q le_rfl
  have h' : (q.reflect q.natDegree).eval t * (t⁻¹) ^ q.natDegree =
      q.eval t⁻¹ := by
    simpa [invOf_eq_inv] using h
  calc
    (q.reflect q.natDegree).eval t =
        ((q.reflect q.natDegree).eval t * (t⁻¹) ^ q.natDegree) *
          t ^ q.natDegree := by
      rw [mul_assoc, inv_pow, inv_mul_cancel₀ (pow_ne_zero q.natDegree ht), mul_one]
    _ = q.eval t⁻¹ * t ^ q.natDegree := by rw [h']
    _ = t ^ q.natDegree * q.eval t⁻¹ := mul_comm _ _


/-- Reflection extracts the endpoint without any a priori degree bound. -/
theorem polynomial_endpoint_of_bruhat (p q : Polynomial k) (m : ℕ)
    (h : ∀ t : k, t ≠ 0 → p.eval t = t ^ m * q.eval t⁻¹) :
    p.coeff m = q.coeff 0 := by
  have he : Polynomial.X ^ q.natDegree * p =
      Polynomial.X ^ m * q.reflect q.natDegree := by
    apply Polynomial.eq_of_infinite_eval_eq
    apply (Set.infinite_of_finite_compl
      (by simp : ({t : k | t ≠ 0} : Set k)ᶜ.Finite)).mono
    intro t ht
    simp only [Set.mem_ofPred_eq] at ht ⊢
    rw [Polynomial.eval_mul, Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_pow, Polynomial.eval_X, h t ht, eval_reflect_natDegree q t ht]
    ring
  have hc := congrArg (fun r : Polynomial k => r.coeff (q.natDegree + m)) he
  rw [Nat.add_comm q.natDegree m, Polynomial.coeff_X_pow_mul,
    Nat.add_comm m q.natDegree, Polynomial.coeff_X_pow_mul,
    Polynomial.coeff_reflect, Polynomial.revAt_le le_rfl, Nat.sub_self] at hc
  exact hc

/-- The degree-m lower-root coefficient on an upper-fixed vector of diagonal
weight m is its actual Weyl translate. No nonzero hypothesis is needed. -/
theorem rankOne_lower_endpoint (rho : RationalRepresentation K V)
    (hr : IsRationalRepresentation rho) (f : Theory.AlgebraicGroup.Morphism (slVariety k 2) K)
    (v : V) (m : ℕ)
    (hu : ∀ t : k, (rho.action (f.onPoints
      (standardSL2UpperMorphism.onPoints (kPlusPoint t)))).val v = v)
    (hd : ∀ t : Variety.Point (KMult k),
      (rho.action (f.onPoints (standardSL2DiagonalMorphism.onPoints t))).val v =
        (dPointEquiv 1 t 0 : k) ^ m • v) :
    curveCoefficient rho hr (f.comp standardSL2LowerMorphism) m v =
      (rho.action (f.onPoints rankOneWeylPoint)).val v := by
  let wv := (rho.action (f.onPoints rankOneWeylPoint)).val v
  apply (Module.finBasis k V).repr.injective
  ext i
  let l := (Module.finBasis k V).coord i
  change l (curveCoefficient rho hr _ m v) = l wv
  rw [dual_curveCoefficient]
  let p := curvePolynomial rho hr (f.comp standardSL2LowerMorphism) l v
  let q := curvePolynomial rho hr (f.comp standardSL2UpperMorphism) l wv
  have h (t : k) (ht : t ≠ 0) : p.eval t = t ^ m * q.eval t⁻¹ := by
    dsimp only [p, q]
    rw [curvePolynomial_eval, curvePolynomial_eval]
    change l ((rho.action (f.onPoints (standardSL2LowerMorphism.onPoints (kPlusPoint t)))).val v) = _
    rw [standardSL2_lower_bruhat t ht]
    simp only [map_mul, Units.val_mul, Module.End.mul_apply]
    rw [hu]
    have hw : (rho.action (f.onPoints (standardSL2DiagonalMorphism.onPoints
        (standardSL2TorusPoint t⁻¹ (inv_ne_zero ht))))).val wv = t ^ m • wv := by
      change (rho.action (f.onPoints (standardSL2DiagonalMorphism.onPoints _))).val
        ((rho.action (f.onPoints rankOneWeylPoint)).val v) = _
      rw [← Module.End.mul_apply, ← Units.val_mul, ← map_mul, ← map_mul,
        standardSL2_diagonal_mul_weyl, map_mul, map_mul, Units.val_mul, Module.End.mul_apply,
        hd, standardSL2TorusPoint_inv_coordinate, inv_inv, map_smul]
    change l ((rho.action (f.onPoints (standardSL2UpperMorphism.onPoints
      (kPlusPoint t⁻¹)))).val ((rho.action (f.onPoints
        (standardSL2DiagonalMorphism.onPoints _))).val wv)) = _
    rw [hw, map_smul, map_smul, smul_eq_mul]
    rfl
  have hc := polynomial_endpoint_of_bruhat p q m h
  have h0 : q.coeff 0 = l wv := by
    rw [Polynomial.coeff_zero_eq_eval_zero, curvePolynomial_eval]
    have hk : kPlusPoint (0 : k) = 1 := by
      apply (additiveGroupPointEquiv k).injective
      rfl
    simp only [hk, map_one, Units.val_one, Module.End.one_apply]
  exact hc.trans h0

/-- Invertibility of the Weyl point makes the rank-one endpoint nonzero. -/
theorem rankOne_lower_endpoint_ne_zero (rho : RationalRepresentation K V)
    (hr : IsRationalRepresentation rho) (f : Theory.AlgebraicGroup.Morphism (slVariety k 2) K)
    (v : V) (m : ℕ) (hv : v ≠ 0)
    (hu : ∀ t : k, (rho.action (f.onPoints
      (standardSL2UpperMorphism.onPoints (kPlusPoint t)))).val v = v)
    (hd : ∀ t : Variety.Point (KMult k),
      (rho.action (f.onPoints (standardSL2DiagonalMorphism.onPoints t))).val v =
        (dPointEquiv 1 t 0 : k) ^ m • v) :
    curveCoefficient rho hr (f.comp standardSL2LowerMorphism) m v ≠ 0 := by
  rw [rankOne_lower_endpoint rho hr f v m hu hd]
  exact fun h => hv (((LinearMap.GeneralLinearGroup.generalLinearEquiv k V)
    (rho.action (f.onPoints rankOneWeylPoint))).injective (h.trans (map_zero _).symm))

variable [CharP k 2]

private theorem rankOneWeylPoint_square : (rankOneWeylPoint (k := k)) * rankOneWeylPoint = 1 := by
  apply (slPointEquiv 2).injective
  apply Subtype.ext
  change (!![0, -1; 1, 0] : Matrix (Fin 2) (Fin 2) k) * !![0, -1; 1, 0] = 1
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, CharTwo.neg_eq]

private def rankOneSwap : Theory.AlgebraicGroup.Morphism (slVariety k 2) (slVariety k 2) where
  toVariety := Theory.AlgebraicGroup.conjugationByMorphism _ rankOneWeylPoint
  map_one := by
    rw [Theory.AlgebraicGroup.conjugationByMorphism_apply]
    group
  map_mul := by
    intro x y
    simp only [Theory.AlgebraicGroup.conjugationByMorphism_apply]
    group

private theorem rankOneSwap_apply (g : Variety.Point (slVariety k 2)) :
    rankOneSwap.onPoints g = rankOneWeylPoint * g * rankOneWeylPoint := by
  change rankOneWeylPoint * g * rankOneWeylPoint⁻¹ = _
  rw [inv_eq_of_mul_eq_one_left rankOneWeylPoint_square]

private theorem rankOneSwap_upper (t : k) :
    rankOneSwap.onPoints (standardSL2UpperMorphism.onPoints (kPlusPoint t)) =
      standardSL2LowerMorphism.onPoints (kPlusPoint t) := by
  rw [rankOneSwap_apply]
  apply (slPointEquiv 2).injective
  apply Subtype.ext
  change (!![0, -1; 1, 0] : Matrix (Fin 2) (Fin 2) k) *
    Matrix.transvection 0 1 t * !![0, -1; 1, 0] = Matrix.transvection 1 0 t
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.vecMul, Matrix.vecHead, Matrix.vecTail, Fin.sum_univ_two, Matrix.transvection,
      Matrix.single_apply, Matrix.one_apply, CharTwo.neg_eq]

private theorem rankOneSwap_lower (t : k) :
    rankOneSwap.onPoints (standardSL2LowerMorphism.onPoints (kPlusPoint t)) =
      standardSL2UpperMorphism.onPoints (kPlusPoint t) := by
  rw [← rankOneSwap_upper, rankOneSwap_apply, rankOneSwap_apply]
  simp only [← mul_assoc, rankOneWeylPoint_square, one_mul]
  rw [mul_assoc, rankOneWeylPoint_square, mul_one]

private theorem rankOneSwap_diagonal (t : Variety.Point (KMult k)) :
    rankOneSwap.onPoints (standardSL2DiagonalMorphism.onPoints t) =
      standardSL2DiagonalMorphism.onPoints t⁻¹ := by
  rw [rankOneSwap_apply]
  obtain ⟨a, rfl⟩ := (dPointEquiv 1).symm.surjective t
  have he : (dPointEquiv 1).symm a = standardSL2TorusPoint (a 0 : k) (a 0).ne_zero := by
    apply (dPointEquiv 1).injective
    ext i
    fin_cases i
    simp [standardSL2TorusPoint]
  rw [he]
  have hc := standardSL2_diagonal_mul_weyl (a 0 : k) (a 0).ne_zero
  rw [mul_assoc]
  calc
    _ = rankOneWeylPoint * (rankOneWeylPoint *
      standardSL2DiagonalMorphism.onPoints (standardSL2TorusPoint (a 0 : k) (a 0).ne_zero)⁻¹) :=
        congrArg (fun g => rankOneWeylPoint * g) hc
    _ = _ := by rw [← mul_assoc, rankOneWeylPoint_square, one_mul]

/-- The opposite endpoint uses the inverse diagonal weight and the same Weyl
point in characteristic two. -/
theorem rankOne_upper_endpoint (rho : RationalRepresentation K V)
    (hr : IsRationalRepresentation rho) (f : Theory.AlgebraicGroup.Morphism (slVariety k 2) K)
    (v : V) (m : ℕ)
    (hl : ∀ t : k, (rho.action (f.onPoints
      (standardSL2LowerMorphism.onPoints (kPlusPoint t)))).val v = v)
    (hd : ∀ t : Variety.Point (KMult k),
      (rho.action (f.onPoints (standardSL2DiagonalMorphism.onPoints t))).val v =
        (dPointEquiv 1 t 0 : k)⁻¹ ^ m • v) :
    curveCoefficient rho hr (f.comp standardSL2UpperMorphism) m v =
      (rho.action (f.onPoints rankOneWeylPoint)).val v := by
  have hu (t : k) : (rho.action ((f.comp rankOneSwap).onPoints
      (standardSL2UpperMorphism.onPoints (kPlusPoint t)))).val v = v := by
    change (rho.action (f.onPoints (rankOneSwap.onPoints _))).val v = v
    rw [rankOneSwap_upper]
    exact hl t
  have hw : rankOneSwap.onPoints (rankOneWeylPoint (k := k)) = rankOneWeylPoint := by
    rw [rankOneSwap_apply, rankOneWeylPoint_square, one_mul]
  have he := rankOne_lower_endpoint rho hr (f.comp rankOneSwap) v m hu (by
    intro t
    change (rho.action (f.onPoints (rankOneSwap.onPoints _))).val v = _
    rw [rankOneSwap_diagonal, hd]
    have ht : (dPointEquiv 1 t⁻¹ 0 : k) = (dPointEquiv 1 t 0 : k)⁻¹ := by
      change (((dPointEquiv 1 t 0)⁻¹ : kˣ) : k) = _
      exact Units.val_inv_eq_inv_val _
    rw [ht, inv_inv])
  have hcurve : (f.comp rankOneSwap).comp standardSL2LowerMorphism =
      f.comp standardSL2UpperMorphism := by
    apply Morphism.ext
    funext t
    rw [← kPlusPoint_coordinate t]
    change f.onPoints (rankOneSwap.onPoints (standardSL2LowerMorphism.onPoints
      (kPlusPoint _))) = _
    rw [rankOneSwap_lower]
    rfl
  rw [hcurve] at he
  change _ = (rho.action (f.onPoints (rankOneSwap.onPoints rankOneWeylPoint))).val v at he
  rwa [hw] at he

/-- The opposite rank-one endpoint is nonzero on every nonzero input. -/
theorem rankOne_upper_endpoint_ne_zero (rho : RationalRepresentation K V)
    (hr : IsRationalRepresentation rho) (f : Theory.AlgebraicGroup.Morphism (slVariety k 2) K)
    (v : V) (m : ℕ) (hv : v ≠ 0)
    (hl : ∀ t : k, (rho.action (f.onPoints
      (standardSL2LowerMorphism.onPoints (kPlusPoint t)))).val v = v)
    (hd : ∀ t : Variety.Point (KMult k),
      (rho.action (f.onPoints (standardSL2DiagonalMorphism.onPoints t))).val v =
        (dPointEquiv 1 t 0 : k)⁻¹ ^ m • v) :
    curveCoefficient rho hr (f.comp standardSL2UpperMorphism) m v ≠ 0 := by
  rw [rankOne_upper_endpoint rho hr f v m hl hd]
  exact fun h => hv (((LinearMap.GeneralLinearGroup.generalLinearEquiv k V)
    (rho.action (f.onPoints rankOneWeylPoint))).injective (h.trans (map_zero _).symm))

end
end Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.ExtremalGrid.DividedPowerEndpoint
