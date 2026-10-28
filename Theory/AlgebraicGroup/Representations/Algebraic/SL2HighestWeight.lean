module

public import Mathlib.Algebra.Polynomial.Reverse
public import Theory.AlgebraicGroup.Representations.Operations
public import Theory.AlgebraicGroup.RootSubgroups.SL2RootCurves
public import Theory.AlgebraicGroup.RootSystems.AlgebraicGroups.TypeASLDiagonalTorus

/-!
# The algebraic SL2 highest-weight endpoint

Let `x` be a nonzero vector in a finite-dimensional rational representation of
`SL2`.  If the standard upper root curve fixes `x` and the standard diagonal
cocharacter acts on `x` with Laurent exponent `m`, then `m` is nonnegative.
The pullback theorem below packages the same conclusion after any compatible
algebraic-group morphism out of `SL2`, and hence after a central isogeny.

The proof is the characteristic-free algebraic highest-weight endpoint
argument used in the rank-one step of the GLS3 highest-weight development.
Choose a linear functional nonzero on the Weyl translate of `x`.  Rationality
turns its upper- and lower-root matrix coefficients into polynomials `q` and
`p`, with `q(0) = 1`.  The open Bruhat-cell identity gives
`p(t) = t ^ m * q(t⁻¹)` for `t ≠ 0`.  Were `m = -(n + 1)`, polynomial
reflection would give
`X ^ (n + 1 + degree q) * p = reflect (degree q) q`; the coefficient in degree
`degree q` is zero on the left and `q(0) = 1` on the right.

Only regularity of the representation and finite dimensionality enter.  In
particular, the proof assumes neither semisimplicity nor characteristic zero
and applies unchanged to Frobenius-twisted representations.
-/

universe u v

namespace Theory.AlgebraicGroup

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- The standard diagonal cocharacter `a |-> diag(a, a^-1)` of `SL2`. -/
public noncomputable abbrev standardSL2DiagonalMorphism :
    AlgebraicGroup.Morphism (KMult k) (slVariety k 2) :=
  typeASLDiagonalMorphism 1

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

private noncomputable def additiveCurveCoefficientPolynomial
    {G : Variety k} [AlgebraicGroup G]
    {V : Type v} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (rho : RationalRepresentation G V)
    (e : Module.Basis (Fin (Module.finrank k V)) k V)
    (f : AlgebraicGroup.Morphism G (glVarietyOf k V))
    (curve : AlgebraicGroup.Morphism (KPlus k) G)
    (l : Module.Dual k V) (x : V) : Polynomial k :=
  let c : Variety.PolynomialFunction (KPlus k) :=
    Variety.PolynomialFunction.pullback curve.toVariety
      (rationalRepresentationLinearMatrixCoefficient rho e f l x)
  MvPolynomial.uniqueAlgEquiv k PUnit (Classical.choose c.representedBy)

private lemma additiveCurveCoefficientPolynomial_eval
    {G : Variety k} [AlgebraicGroup G]
    {V : Type v} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (rho : RationalRepresentation G V)
    (e : Module.Basis (Fin (Module.finrank k V)) k V)
    (f : AlgebraicGroup.Morphism G (glVarietyOf k V))
    (hf : ∀ g, glPointEquivOf k V e (f.onPoints g) = rho.action g)
    (curve : AlgebraicGroup.Morphism (KPlus k) G)
    (l : Module.Dual k V) (x : V) (t : k) :
    (additiveCurveCoefficientPolynomial rho e f curve l x).eval t =
      l ((rho.action (curve.onPoints (kPlusPoint t)) : Module.End k V) x) := by
  let c : Variety.PolynomialFunction (KPlus k) :=
    Variety.PolynomialFunction.pullback curve.toVariety
      (rationalRepresentationLinearMatrixCoefficient rho e f l x)
  let r : MvPolynomial PUnit k := Classical.choose c.representedBy
  have hr := Classical.choose_spec c.representedBy (kPlusPoint t)
  calc
    (additiveCurveCoefficientPolynomial rho e f curve l x).eval t =
        (MvPolynomial.uniqueAlgEquiv k PUnit r).eval t := by rfl
    _ = MvPolynomial.eval₂ (RingHom.id k) (fun _ ↦ t) r := by
      simpa using
        (MvPolynomial.eval₂_const_uniqueAlgEquiv
          (R := k) (S := k) (f := r) (φ := RingHom.id k) (a := t))
    _ = evalPolynomial (kPlusPoint t).val r := by rfl
    _ = c (kPlusPoint t) := hr.symm
    _ = rationalRepresentationLinearMatrixCoefficient rho e f l x
        (curve.onPoints (kPlusPoint t)) := rfl
    _ = l ((rho.action (curve.onPoints (kPlusPoint t)) : Module.End k V) x) :=
      rationalRepresentationLinearMatrixCoefficient_apply rho e f hf l x _

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

/-- A nonzero upper-root-fixed vector of standard diagonal exponent `m` in a
finite-dimensional rational `SL2` representation has `0 ≤ m`. -/
public theorem standardSL2_highestWeightExponent_nonneg
    {V : Type v} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (rho : RationalRepresentation (slVariety k 2) V)
    (hrho : IsRationalRepresentation rho)
    (x : V) (m : Int) (hx : x ≠ 0)
    (hUpper : ∀ t : k,
      (rho.action ((standardSL2UpperMorphism (k := k)).onPoints
        (kPlusPoint t)) : Module.End k V) x = x)
    (hDiagonal : ∀ t : Variety.Point (KMult k),
      (rho.action ((standardSL2DiagonalMorphism (k := k)).onPoints t) :
          Module.End k V) x = (dPointEquiv 1 t 0 : k) ^ m • x) :
    0 ≤ m := by
  cases m with
  | ofNat n => exact Int.natCast_nonneg n
  | negSucc n =>
      exfalso
      obtain ⟨e, f, hf⟩ := hrho
      let wx : V := (rho.action (standardSL2WeylPoint (k := k)) : Module.End k V) x
      have hwx : wx ≠ 0 := by
        intro hzero
        apply hx
        apply ((LinearMap.GeneralLinearGroup.generalLinearEquiv k V)
          (rho.action (standardSL2WeylPoint (k := k)))).injective
        simpa [wx] using hzero
      obtain ⟨l, hl⟩ := Module.Projective.exists_dual_eq_one k hwx
      let p : Polynomial k := additiveCurveCoefficientPolynomial rho e f
        (standardSL2LowerMorphism (k := k)) l x
      let q : Polynomial k := additiveCurveCoefficientPolynomial rho e f
        (standardSL2UpperMorphism (k := k)) l wx
      have hp (t : k) : p.eval t =
          l ((rho.action ((standardSL2LowerMorphism (k := k)).onPoints
            (kPlusPoint t)) : Module.End k V) x) :=
        additiveCurveCoefficientPolynomial_eval rho e f hf _ l x t
      have hq (t : k) : q.eval t =
          l ((rho.action ((standardSL2UpperMorphism (k := k)).onPoints
            (kPlusPoint t)) : Module.End k V) wx) :=
        additiveCurveCoefficientPolynomial_eval rho e f hf _ l wx t
      have hq_zero : q.eval 0 = 1 := by
        rw [hq]
        have hk0 : kPlusPoint (0 : k) = 1 := by
          apply (additiveGroupPointEquiv k).injective
          rfl
        rw [hk0, map_one]
        change l ((rho.action 1 : Module.End k V) wx) = 1
        simpa using hl
      have hpq (t : k) (ht : t ≠ 0) :
          p.eval t = t ^ (Int.negSucc n) * q.eval t⁻¹ := by
        rw [hp, hq]
        rw [standardSL2_lower_bruhat t ht, map_mul, map_mul, map_mul]
        change l ((rho.action _ : Module.End k V)
          ((rho.action _ : Module.End k V)
            ((rho.action _ : Module.End k V)
              ((rho.action _ : Module.End k V) x)))) = _
        rw [hUpper]
        change l ((rho.action _ : Module.End k V)
          ((rho.action _ : Module.End k V) wx)) = _
        have hdiagW :
            (rho.action ((standardSL2DiagonalMorphism (k := k)).onPoints
              (standardSL2TorusPoint t⁻¹ (inv_ne_zero ht))) : Module.End k V) wx =
              t ^ (Int.negSucc n) • wx := by
          dsimp only [wx]
          change (((rho.action
              ((standardSL2DiagonalMorphism (k := k)).onPoints
                (standardSL2TorusPoint t⁻¹ (inv_ne_zero ht)))) *
              rho.action (standardSL2WeylPoint (k := k)) :
                LinearMap.GeneralLinearGroup k V) : Module.End k V) x = _
          rw [← map_mul, standardSL2_diagonal_mul_weyl]
          rw [map_mul]
          change (rho.action (standardSL2WeylPoint (k := k)) : Module.End k V)
            ((rho.action _ : Module.End k V) x) = _
          rw [hDiagonal]
          rw [standardSL2TorusPoint_inv_coordinate]
          simp only [map_smul]
          congr 1
          simp [zpow_negSucc]
        rw [hdiagW, map_smul, map_smul]
        simp [smul_eq_mul]
      let N : Nat := n + 1 + q.natDegree
      have hpoly : Polynomial.X ^ N * p = q.reflect q.natDegree := by
        apply Polynomial.eq_of_infinite_eval_eq
        apply (Set.infinite_of_finite_compl
          (by simp : ({t : k | t ≠ 0} : Set k)ᶜ.Finite)).mono
        intro t ht
        simp only [Set.mem_ofPred_eq] at ht
        simp only [Set.mem_ofPred_eq]
        rw [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X,
          hpq t ht, eval_reflect_natDegree q t ht]
        dsimp [N]
        rw [zpow_negSucc]
        field_simp
        rw [pow_add]
        ring
      have hcoeff := congrArg (fun r : Polynomial k => r.coeff q.natDegree) hpoly
      have hleft : (Polynomial.X ^ N * p).coeff q.natDegree = 0 := by
        rw [Polynomial.coeff_X_pow_mul']
        simp [N]
      have hright : (q.reflect q.natDegree).coeff q.natDegree = 1 := by
        rw [Polynomial.coeff_reflect, Polynomial.revAt_le le_rfl, Nat.sub_self]
        simpa [Polynomial.coeff_zero_eq_eval_zero] using hq_zero
      rw [hleft, hright] at hcoeff
      exact zero_ne_one hcoeff

/-- Pullback-stable form of `standardSL2_highestWeightExponent_nonneg`.
It applies in particular when `pi` is a compatible central isogeny. -/
public theorem standardSL2_highestWeightExponent_nonneg_of_pullback
    {G : Variety k} [AlgebraicGroup G]
    {V : Type v} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (pi : AlgebraicGroup.Morphism (slVariety k 2) G)
    (rho : RationalRepresentation G V) (hrho : IsRationalRepresentation rho)
    (x : V) (m : Int) (hx : x ≠ 0)
    (hUpper : ∀ t : k,
      (rho.action (pi.onPoints
        ((standardSL2UpperMorphism (k := k)).onPoints (kPlusPoint t))) :
          Module.End k V) x = x)
    (hDiagonal : ∀ t : Variety.Point (KMult k),
      (rho.action (pi.onPoints
        ((standardSL2DiagonalMorphism (k := k)).onPoints t)) :
          Module.End k V) x = (dPointEquiv 1 t 0 : k) ^ m • x) :
    0 ≤ m := by
  obtain ⟨sigma, hsigma, hsigmaRational⟩ :=
    rationalRepresentation_pullback_exists pi rho hrho
  apply standardSL2_highestWeightExponent_nonneg sigma hsigmaRational x m hx
  · intro t
    rw [hsigma]
    exact hUpper t
  · intro t
    rw [hsigma]
    exact hDiagonal t

end Theory.AlgebraicGroup
