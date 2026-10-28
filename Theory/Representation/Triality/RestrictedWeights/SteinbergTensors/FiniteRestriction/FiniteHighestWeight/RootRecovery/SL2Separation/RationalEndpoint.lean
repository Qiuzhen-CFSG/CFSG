module
public import Theory.AlgebraicGroup.Representations.Algebraic.SL2HighestWeight

/-!
# Detecting the zero rational SL2 highest weight by the Weyl element

The Bruhat and matrix-coefficient calculations below adapt the private proofs in
`Theory.AlgebraicGroup.Representations.Algebraic.SL2HighestWeight`. For exponent
zero, polynomial reflection identifies the coefficients at the two endpoints,
so the Weyl element fixes the highest vector. Conversely, Weyl fixation reverses
the exponent; nonnegativity then forces zero. No irreducibility is used.

This is the rational endpoint step for GLS3 2.8.2 / Steinberg §13.3(a),
`refs/KGroup/GLS3/Chapter2St2.tex`.
-/
universe u v
namespace Theory.AlgebraicGroup.SL2FiniteRecovery
variable {k : Type u} [Field k] [IsAlgClosed k]

@[expose] public noncomputable def weylPoint :
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
          (standardSL2TorusPoint a ha) * weylPoint =
      weylPoint *
        (standardSL2DiagonalMorphism (k := k)).onPoints
          ((standardSL2TorusPoint a ha)⁻¹) := by
  apply (slPointEquiv 2).injective
  change (slPointEquiv 2
      ((standardSL2DiagonalMorphism (k := k)).onPoints
        (standardSL2TorusPoint a ha))) *
        (slPointEquiv 2 (weylPoint (k := k))) =
      (slPointEquiv 2 (weylPoint (k := k))) *
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
        weylPoint *
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

private lemma diagonal_mul_weyl (t : Variety.Point (KMult k)) :
    standardSL2DiagonalMorphism.onPoints t * weylPoint =
      weylPoint * standardSL2DiagonalMorphism.onPoints t⁻¹ := by
  have ht : t = standardSL2TorusPoint (dPointEquiv 1 t 0 : k)
      (dPointEquiv 1 t 0).ne_zero := by
    apply (dPointEquiv 1).injective
    funext i
    fin_cases i
    simp [standardSL2TorusPoint]
  rw [ht]
  exact standardSL2_diagonal_mul_weyl _ _

omit [IsAlgClosed k] in
private lemma zero_parameter : kPlusPoint (0 : k) = 1 := by
  apply (additiveGroupPointEquiv k).injective
  rfl

/-- In a rational SL2 module, the Weyl element fixes every upper-fixed vector
on which the diagonal torus acts trivially. -/
public theorem weyl_fixed_of_exponent_zero
    {V : Type v} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (rho : RationalRepresentation (slVariety k 2) V)
    (hrho : IsRationalRepresentation rho) (x : V)
    (hUpper : ∀ t : k,
      (rho.action (standardSL2UpperMorphism.onPoints (kPlusPoint t))).1 x = x)
    (hDiagonal : ∀ t : Variety.Point (KMult k),
      (rho.action (standardSL2DiagonalMorphism.onPoints t)).1 x = x) :
    (rho.action (weylPoint (k := k))).1 x = x := by
  obtain ⟨e, f, hf⟩ := hrho
  let wx := (rho.action (weylPoint (k := k))).1 x
  apply e.eval_injective
  apply LinearMap.ext
  intro l
  change l wx = l x
  let p := additiveCurveCoefficientPolynomial rho e f standardSL2LowerMorphism l x
  let q := additiveCurveCoefficientPolynomial rho e f standardSL2UpperMorphism l wx
  have hp (t : k) : p.eval t =
      l ((rho.action (standardSL2LowerMorphism.onPoints (kPlusPoint t))).1 x) :=
    additiveCurveCoefficientPolynomial_eval rho e f hf _ l x t
  have hq (t : k) : q.eval t =
      l ((rho.action (standardSL2UpperMorphism.onPoints (kPlusPoint t))).1 wx) :=
    additiveCurveCoefficientPolynomial_eval rho e f hf _ l wx t
  have hpq (t : k) (ht : t ≠ 0) : p.eval t = q.eval t⁻¹ := by
    rw [hp, hq, standardSL2_lower_bruhat t ht, map_mul, map_mul, map_mul]
    change l ((rho.action _).1 ((rho.action _).1
      ((rho.action _).1 ((rho.action _).1 x)))) = _
    rw [hUpper]
    have hd (s : Variety.Point (KMult k)) :
        (rho.action (standardSL2DiagonalMorphism.onPoints s)).1 wx = wx := by
      change ((rho.action (standardSL2DiagonalMorphism.onPoints s) *
        rho.action weylPoint).1) x = wx
      rw [← map_mul, diagonal_mul_weyl, map_mul]
      change (rho.action weylPoint).1 ((rho.action _).1 x) = wx
      rw [hDiagonal]
    change l ((rho.action _).1 ((rho.action _).1 wx)) = _
    rw [hd]
  have hpoly : Polynomial.X ^ q.natDegree * p = q.reflect q.natDegree := by
    apply Polynomial.eq_of_infinite_eval_eq
    apply (Set.infinite_of_finite_compl
      (by simp : ({t : k | t ≠ 0} : Set k)ᶜ.Finite)).mono
    intro t ht
    simp only [Set.mem_ofPred_eq] at ht ⊢
    rw [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X,
      hpq t ht, eval_reflect_natDegree q t ht]
  have hcoeff := congrArg (fun r : Polynomial k => r.coeff q.natDegree) hpoly
  have heq : p.eval 0 = q.eval 0 := by
    simpa [Polynomial.coeff_X_pow_mul', Polynomial.coeff_reflect,
      Polynomial.revAt_le le_rfl, Polynomial.coeff_zero_eq_eval_zero] using hcoeff
  have hp0 : p.eval 0 = l x := by
    rw [hp, zero_parameter, map_one]
    simp
  have hq0 : q.eval 0 = l wx := by
    rw [hq, zero_parameter, map_one]
    simp
  exact hq0.symm.trans (heq.symm.trans hp0)

/-- A nonzero rational highest vector is fixed by the Weyl element exactly
when its diagonal exponent is zero, even in a reducible representation. -/
public theorem weyl_fixed_iff_exponent_zero
    {V : Type v} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (rho : RationalRepresentation (slVariety k 2) V)
    (hrho : IsRationalRepresentation rho) (x : V) (m : ℤ) (hx : x ≠ 0)
    (hUpper : ∀ t : k,
      (rho.action (standardSL2UpperMorphism.onPoints (kPlusPoint t))).1 x = x)
    (hDiagonal : ∀ t : Variety.Point (KMult k),
      (rho.action (standardSL2DiagonalMorphism.onPoints t)).1 x =
        (dPointEquiv 1 t 0 : k)^m • x) :
    (rho.action (weylPoint (k := k))).1 x = x ↔ m = 0 := by
  constructor
  · intro hw
    have hm := standardSL2_highestWeightExponent_nonneg rho hrho x m hx hUpper hDiagonal
    have hneg := standardSL2_highestWeightExponent_nonneg rho hrho x (-m) hx hUpper
      (fun t => show (rho.action (standardSL2DiagonalMorphism.onPoints t)).1 x =
          (dPointEquiv 1 t 0 : k)^(-m) • x from by
        calc
          _ = ((rho.action (standardSL2DiagonalMorphism.onPoints t) *
                rho.action weylPoint).1) x := by
              change _ = (rho.action _).1 ((rho.action _).1 x)
              rw [hw]
          _ = ((rho.action weylPoint *
                rho.action (standardSL2DiagonalMorphism.onPoints t⁻¹)).1) x := by
              rw [← map_mul, diagonal_mul_weyl, map_mul]
          _ = (dPointEquiv 1 t 0 : k)^(-m) • x := by
              change (rho.action weylPoint).1 ((rho.action _).1 x) = _
              rw [hDiagonal, map_smul, hw]
              congr 1
              change ((dPointEquiv 1 t 0)⁻¹ : kˣ).val ^ m = _
              simp only [Units.val_inv_eq_inv_val, inv_zpow, zpow_neg])
    omega
  · intro hm
    apply weyl_fixed_of_exponent_zero rho hrho x hUpper
    intro t
    simpa [hm] using hDiagonal t

end Theory.AlgebraicGroup.SL2FiniteRecovery
