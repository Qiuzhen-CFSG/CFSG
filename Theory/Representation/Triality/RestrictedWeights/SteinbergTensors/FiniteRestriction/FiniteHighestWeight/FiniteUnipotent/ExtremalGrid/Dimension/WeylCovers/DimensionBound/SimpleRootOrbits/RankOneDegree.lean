module

public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.FiniteHighestWeight.FiniteUnipotent.ExtremalGrid.Dimension.WeylCovers.DimensionBound.RootOperators
public import Theory.AlgebraicGroup.Representations.Algebraic.SL2HighestWeight

/-!
# Polynomial bounds on rational SL₂ highest-vector orbits

The open Bruhat identity expresses the lower orbit polynomial of an upper-fixed
vector of diagonal weight `m` as `t^m` times a polynomial in `t⁻¹`. Comparing
coefficients after clearing powers of `t` bounds its degree by `m`. The symmetric
statement retains the negative diagonal weight of a lower-fixed vector.

This extends the nonnegativity argument in `SL2HighestWeight` without changing
that module. The matrix identities below follow that argument; the reciprocal
coefficient comparison follows `ReeF4/.../NegativeCyclicity/RankOne.lean`.
Sources: GLS3 §1.14; Steinberg, Representations of Algebraic Groups (1963), §4.
-/

public noncomputable section
namespace Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.ExtremalGrid.CyclicDimension
open Theory.AlgebraicGroup AlgebraicTensor.RestrictedStep
universe u v
variable {k : Type u} [Field k] [IsAlgClosed k]
private noncomputable def standardSL2WeylPoint :
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
          (standardSL2TorusPoint a ha) * standardSL2WeylPoint =
      standardSL2WeylPoint *
        (standardSL2DiagonalMorphism (k := k)).onPoints
          ((standardSL2TorusPoint a ha)⁻¹) := by
  apply (slPointEquiv 2).injective
  change (slPointEquiv 2
      ((standardSL2DiagonalMorphism (k := k)).onPoints
        (standardSL2TorusPoint a ha))) *
        (slPointEquiv 2 (standardSL2WeylPoint (k := k))) =
      (slPointEquiv 2 (standardSL2WeylPoint (k := k))) *
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
        standardSL2WeylPoint *
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

private lemma standardSL2_upper_bruhat (a : k) (ha : a ≠ 0) :
    (standardSL2UpperMorphism (k := k)).onPoints (kPlusPoint a) =
      (standardSL2LowerMorphism (k := k)).onPoints (kPlusPoint a⁻¹) *
        (standardSL2DiagonalMorphism (k := k)).onPoints (standardSL2TorusPoint a ha) *
        standardSL2WeylPoint⁻¹ *
        (standardSL2LowerMorphism (k := k)).onPoints (kPlusPoint a⁻¹) := by
  apply (slPointEquiv 2).injective
  apply Subtype.ext
  change Matrix.transvection 0 1 a =
    Matrix.transvection 1 0 a⁻¹ * typeASLDiagonalMatrix 1 (standardSL2TorusPoint a ha) *
      (!![0, -1; 1, 0] : Matrix (Fin 2) (Fin 2) k).adjugate *
        Matrix.transvection 1 0 a⁻¹
  rw [standardSL2DiagonalMatrix, Matrix.adjugate_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.transvection,
      Matrix.one_apply, Matrix.single_apply, ha]

private lemma standardSL2_diagonal_mul_weyl_inv (a : k) (ha : a ≠ 0) :
    (standardSL2DiagonalMorphism (k := k)).onPoints (standardSL2TorusPoint a ha) *
        standardSL2WeylPoint⁻¹ =
      standardSL2WeylPoint⁻¹ * (standardSL2DiagonalMorphism (k := k)).onPoints
        ((standardSL2TorusPoint a ha)⁻¹) := by
  have h := standardSL2_diagonal_mul_weyl a⁻¹ (inv_ne_zero ha)
  rw [← standardSL2TorusPoint_inv a ha, inv_inv] at h
  calc
    _ = standardSL2WeylPoint⁻¹ *
      (standardSL2WeylPoint * (standardSL2DiagonalMorphism (k := k)).onPoints
        (standardSL2TorusPoint a ha)) * standardSL2WeylPoint⁻¹ := by group
    _ = _ := by rw [← h]; group

omit [IsAlgClosed k] in
private theorem eval_reflect (p : Polynomial k) (N : ℕ) (hN : p.natDegree ≤ N)
    (t : k) (ht : t ≠ 0) :
    (p.reflect N).eval t = t ^ N * p.eval t⁻¹ := by
  let _ : Invertible (t⁻¹) := invertibleOfNonzero (inv_ne_zero ht)
  have h := Polynomial.eval₂_reflect_mul_pow (RingHom.id k) (t⁻¹) N p hN
  have h' : (p.reflect N).eval t * (t⁻¹) ^ N = p.eval t⁻¹ := by
    simpa [invOf_eq_inv] using h
  calc
    (p.reflect N).eval t = ((p.reflect N).eval t * (t⁻¹) ^ N) * t ^ N := by
      rw [mul_assoc, inv_pow, inv_mul_cancel₀ (pow_ne_zero N ht), mul_one]
    _ = p.eval t⁻¹ * t ^ N := by rw [h']
    _ = t ^ N * p.eval t⁻¹ := mul_comm _ _

private theorem reciprocal_coeff_eq_zero (p q : Polynomial k) (m j : ℕ) (hj : m < j)
    (h : ∀ t : k, t ≠ 0 → p.eval t = t ^ m * q.eval t⁻¹) :
    p.coeff j = 0 := by
  let N := max m q.natDegree
  have hm : m ≤ N := le_max_left _ _
  have hq : q.natDegree ≤ N := le_max_right _ _
  have he : Polynomial.X ^ N * p = Polynomial.X ^ m * q.reflect N := by
    apply Polynomial.eq_of_infinite_eval_eq
    apply (Set.infinite_of_finite_compl
      (by simp : ({t : k | t ≠ 0} : Set k)ᶜ.Finite)).mono
    intro t ht
    simp only [Set.mem_ofPred_eq] at ht ⊢
    rw [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X, h t ht,
      Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X, eval_reflect q N hq t ht]
    ring
  have hc := congrArg (fun f : Polynomial k => f.coeff (j + N)) he
  rw [Polynomial.coeff_X_pow_mul, Polynomial.coeff_X_pow_mul', if_pos (by omega)] at hc
  rw [Polynomial.coeff_eq_zero_of_natDegree_lt
    (lt_of_le_of_lt (by simpa [max_eq_left hq] using
      (Polynomial.natDegree_reflect_le (p := q) (N := N)))
      (show N < j + N - m by omega))] at hc
  exact hc

variable {K : Variety k} [AlgebraicGroup K]
variable {V : Type v} [AddCommGroup V] [Module k V] [FiniteDimensional k V]

/-- In every rational representation, an upper-fixed vector of diagonal weight
`m` has lower-root orbit degree at most `m`, including after a regular pullback. -/
theorem sl2_lower_curvePolynomial_coeff_eq_zero
    (pi : Morphism (slVariety k 2) K)
    (rho : RationalRepresentation K V) (hr : IsRationalRepresentation rho)
    (v : V) (m : ℕ)
    (hu : ∀ t : k, (rho.action (pi.onPoints
      (standardSL2UpperMorphism.onPoints (kPlusPoint t)))).val v = v)
    (hd : ∀ t : Variety.Point (KMult k), (rho.action (pi.onPoints
      (standardSL2DiagonalMorphism.onPoints t))).val v =
        (dPointEquiv 1 t 0 : k) ^ m • v)
    (l : Module.Dual k V) (j : ℕ) (hj : m < j) :
    (curvePolynomial rho hr (pi.comp standardSL2LowerMorphism) l v).coeff j = 0 := by
  let w := (rho.action (pi.onPoints (standardSL2WeylPoint (k := k)))).val v
  apply reciprocal_coeff_eq_zero _
    (curvePolynomial rho hr (pi.comp standardSL2UpperMorphism) l w) m j hj
  intro t ht
  rw [curvePolynomial_eval, curvePolynomial_eval]
  change l ((rho.action (pi.onPoints (standardSL2LowerMorphism.onPoints
    (kPlusPoint t)))).val v) = _
  rw [standardSL2_lower_bruhat t ht]
  simp only [map_mul]
  change l ((rho.action _).val ((rho.action _).val
    ((rho.action _).val ((rho.action _).val v)))) = _
  rw [hu]
  change l ((rho.action _).val ((rho.action _).val w)) = _
  have hw : (rho.action (pi.onPoints (standardSL2DiagonalMorphism.onPoints
      (standardSL2TorusPoint t⁻¹ (inv_ne_zero ht))))).val w = t ^ m • w := by
    dsimp only [w]
    change ((rho.action _ * rho.action _).val) v = _
    rw [← map_mul, ← map_mul, standardSL2_diagonal_mul_weyl, map_mul, map_mul]
    change (rho.action _).val ((rho.action _).val v) = _
    rw [hd, standardSL2TorusPoint_inv_coordinate, inv_inv, map_smul]
  rw [hw, map_smul, map_smul]
  rfl

/-- The opposite statement uses inverse diagonal weight and interchanges the
upper and lower roots. No irreducibility or cyclicity is required. -/
theorem sl2_upper_curvePolynomial_coeff_eq_zero
    (pi : Morphism (slVariety k 2) K)
    (rho : RationalRepresentation K V) (hr : IsRationalRepresentation rho)
    (v : V) (m : ℕ)
    (hl : ∀ t : k, (rho.action (pi.onPoints
      (standardSL2LowerMorphism.onPoints (kPlusPoint t)))).val v = v)
    (hd : ∀ t : Variety.Point (KMult k), (rho.action (pi.onPoints
      (standardSL2DiagonalMorphism.onPoints t))).val v =
        ((dPointEquiv 1 t 0 : k) ^ m)⁻¹ • v)
    (l : Module.Dual k V) (j : ℕ) (hj : m < j) :
    (curvePolynomial rho hr (pi.comp standardSL2UpperMorphism) l v).coeff j = 0 := by
  let w := (rho.action (pi.onPoints ((standardSL2WeylPoint (k := k))⁻¹))).val v
  apply reciprocal_coeff_eq_zero _
    (curvePolynomial rho hr (pi.comp standardSL2LowerMorphism) l w) m j hj
  intro t ht
  rw [curvePolynomial_eval, curvePolynomial_eval]
  change l ((rho.action (pi.onPoints (standardSL2UpperMorphism.onPoints
    (kPlusPoint t)))).val v) = _
  rw [standardSL2_upper_bruhat t ht]
  simp only [map_mul]
  change l ((rho.action _).val ((rho.action _).val
    ((rho.action _).val ((rho.action _).val v)))) = _
  rw [hl]
  change l ((rho.action _).val ((rho.action _).val w)) = _
  have hw : (rho.action (pi.onPoints (standardSL2DiagonalMorphism.onPoints
      (standardSL2TorusPoint t ht)))).val w = t ^ m • w := by
    dsimp only [w]
    change ((rho.action _ * rho.action _).val) v = _
    rw [← map_mul, ← map_mul, standardSL2_diagonal_mul_weyl_inv,
      map_mul, map_mul]
    change (rho.action _).val ((rho.action _).val v) = _
    rw [hd, standardSL2TorusPoint_inv_coordinate, inv_pow, inv_inv, map_smul]
  rw [hw, map_smul, map_smul]
  rfl

end Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.ExtremalGrid.CyclicDimension
