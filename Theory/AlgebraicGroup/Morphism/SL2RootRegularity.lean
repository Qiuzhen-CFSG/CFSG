module

public import Theory.AlgebraicGroup.Morphism.SL2PrincipalOpen
public import Theory.AlgebraicGroup.RootSubgroups.SL2RootCurves
public import Theory.AlgebraicGroup.Morphism.Operations

/-!
# Regularity from the two SL₂ root curves

A homomorphism on SL₂ points is a morphism of algebraic groups whenever its
restrictions to the standard upper and lower root curves are regular.

For a determinant-one matrix `[[a,b],[c,d]]`, the charts `a ≠ 0` and `c ≠ 0`
cover SL₂. On these charts respectively the matrix is

* `L((c-1)/a) U(a-1) L(1) U((b-a+1)/a)`, and
* `U((a-1)/c) L(c) U((d-1)/c)`.

The parameters are polynomials in the affine chart coordinates, including
the adjoined inverse. Composing the given regular curves and multiplication
therefore gives regular chart maps. Principal-open descent supplies global
polynomial coordinates with the original point homomorphism. No restriction
on the characteristic is needed.

These are elementary rank-one versions of the Chevalley root words in GLS3,
§1.12 (`refs/KGroup/GLS3/Chapter1.tex`) and the big-cell description in
Steinberg, (6.2)(c) (`refs/KGroup/GLS3/Chapter2St2.tex`).
-/

noncomputable section

universe u

namespace Theory.AlgebraicGroup
variable {k : Type u} [Field k] [IsAlgClosed k]

omit [IsAlgClosed k] in
private lemma kPlus_coord (s : k) : (kPlusPoint s).val PUnit.unit = s := rfl

private abbrev upper (a : k) := (standardSL2UpperMorphism (k := k)).onPoints (kPlusPoint a)
private abbrev lower (a : k) := (standardSL2LowerMorphism (k := k)).onPoints (kPlusPoint a)

private lemma factor_c (x : Variety.Point (slVariety k 2))
    (hc : x.val (ULift.up (1, 0)) ≠ 0) :
    upper ((x.val (ULift.up (0, 0)) - 1) / x.val (ULift.up (1, 0))) *
      lower (x.val (ULift.up (1, 0))) *
      upper ((x.val (ULift.up (1, 1)) - 1) / x.val (ULift.up (1, 0))) = x := by
  have hd := slPoint_det_eq_one 2 x
  rw [Matrix.det_fin_two] at hd
  simp only [slPointMatrix] at hd
  apply (slPointEquiv 2).injective
  apply Subtype.ext
  change Matrix.transvection (0 : Fin 2) 1 _ *
    Matrix.transvection (1 : Fin 2) 0 _ *
    Matrix.transvection (0 : Fin 2) 1 _ = slPointMatrix 2 x
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.transvection,
      Matrix.single_apply, Matrix.one_apply, slPointMatrix,
      kPlus_coord] <;>
    (try field_simp) <;> grind only

private lemma factor_a (x : Variety.Point (slVariety k 2))
    (ha : x.val (ULift.up (0, 0)) ≠ 0) :
    lower ((x.val (ULift.up (1, 0)) - 1) / x.val (ULift.up (0, 0))) *
      upper (x.val (ULift.up (0, 0)) - 1) * lower (1 : k) *
      upper ((x.val (ULift.up (0, 1)) - x.val (ULift.up (0, 0)) + 1) /
        x.val (ULift.up (0, 0))) = x := by
  have hd := slPoint_det_eq_one 2 x
  rw [Matrix.det_fin_two] at hd
  simp only [slPointMatrix] at hd
  apply (slPointEquiv 2).injective
  apply Subtype.ext
  change Matrix.transvection (1 : Fin 2) 0 _ *
    Matrix.transvection (0 : Fin 2) 1 _ *
    Matrix.transvection (1 : Fin 2) 0 _ *
    Matrix.transvection (0 : Fin 2) 1 _ = slPointMatrix 2 x
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.transvection,
      Matrix.single_apply, Matrix.one_apply, slPointMatrix,
      kPlus_coord] <;>
    (try field_simp) <;> grind only

private def polyLine {V : Variety k} (p : MvPolynomial V.Coordinates k) :
    Variety.Morphism V (KPlus k) where
  toFun x := kPlusPoint (evalPolynomial x.val p)
  regular _ := ⟨p, fun _ => rfl⟩

private def curve {V H : Variety k} [AlgebraicGroup H]
    (u : Morphism (KPlus k) H) (p : MvPolynomial V.Coordinates k) :
    Variety.Morphism V H := u.toVariety.comp (polyLine p)

omit [IsAlgClosed k] in
private lemma curve_apply {V H : Variety k} [AlgebraicGroup H]
    (u : Morphism (KPlus k) H) (p : MvPolynomial V.Coordinates k)
    (x : Variety.Point V) :
    (curve u p).toFun x = u.onPoints (kPlusPoint (evalPolynomial x.val p)) := rfl

private def mulMaps {V H : Variety k} [AlgebraicGroup H]
    (f g : Variety.Morphism V H) : Variety.Morphism V H :=
  (mulMorphism H).comp (f.pair g)

omit [IsAlgClosed k] in
private lemma mulMaps_apply {V H : Variety k} [AlgebraicGroup H]
    (f g : Variety.Morphism V H) (x : Variety.Point V) :
    (mulMaps f g).toFun x = f.toFun x * g.toFun x := by
  change ((Variety.prodPointEquiv H H) ((Variety.prodPointEquiv H H).symm _)).1 *
    ((Variety.prodPointEquiv H H) ((Variety.prodPointEquiv H H).symm _)).2 = _
  rw [Equiv.apply_symm_apply]

/-- A homomorphism on SL₂ points whose two standard root curves are regular
is induced by an algebraic-group morphism with exactly that point map. -/
public theorem exists_sl2Morphism_of_regular_rootCurves {H : Variety k} [AlgebraicGroup H]
    (f : Variety.Point (slVariety k 2) →* Variety.Point H)
    (u v : Morphism (KPlus k) H)
    (hu : ∀ s, f (standardSL2UpperMorphism.onPoints s) = u.onPoints s)
    (hv : ∀ s, f (standardSL2LowerMorphism.onPoints s) = v.onPoints s) :
    ∃ F : Morphism (slVariety k 2) H, F.onPoints = f := by
  let X (i j : Fin 2) : MvPolynomial (Option (slVariety k 2).Coordinates) k :=
    MvPolynomial.X (some (ULift.up (i, j)))
  let T : MvPolynomial (Option (slVariety k 2).Coordinates) k := MvPolynomial.X none
  let Fa : Variety.Morphism
      ((slVariety k 2).principalOpenChart (sl2FirstColumnPolynomial 0)) H :=
    mulMaps (mulMaps (mulMaps
      (curve v ((X 1 0 - 1) * T)) (curve u (X 0 0 - 1)))
      (curve v 1)) (curve u ((X 0 1 - X 0 0 + 1) * T))
  let Fc : Variety.Morphism
      ((slVariety k 2).principalOpenChart (sl2FirstColumnPolynomial 1)) H :=
    mulMaps (mulMaps (curve u ((X 0 0 - 1) * T)) (curve v (X 1 0)))
      (curve u ((X 1 1 - 1) * T))
  apply Morphism.exists_of_sl2_principalOpen f Fa Fc
  · intro x
    let y : Variety.Point (slVariety k 2) := ((slVariety k 2).principalOpenChartInclusion
      (sl2FirstColumnPolynomial 0)).toFun x
    have hy : y.val (ULift.up (0, 0)) ≠ 0 :=
      by simpa only [y, sl2FirstColumnPolynomial,
        Variety.principalOpenChartInclusion, evalPolynomial_X] using
        Variety.principalOpenChart_nonzero (sl2FirstColumnPolynomial 0) x
    have ht : x.val none = (y.val (ULift.up (0, 0)))⁻¹ :=
      by simpa only [y, sl2FirstColumnPolynomial,
        Variety.principalOpenChartInclusion, evalPolynomial_X] using
        Variety.principalOpenChart_val_none (sl2FirstColumnPolynomial 0) x
    dsimp only [Fa]
    simp only [mulMaps_apply, curve_apply, X, T, evalPolynomial, MvPolynomial.eval₂_mul,
      MvPolynomial.eval₂_sub, MvPolynomial.eval₂_add, MvPolynomial.eval₂_one, MvPolynomial.eval₂_X]
    rw [ht]
    simpa only [upper, lower, div_eq_mul_inv, map_mul, hu, hv,
      y, Variety.principalOpenChartInclusion] using
      congrArg f (factor_a y hy)
  · intro x
    let y : Variety.Point (slVariety k 2) := ((slVariety k 2).principalOpenChartInclusion
      (sl2FirstColumnPolynomial 1)).toFun x
    have hy : y.val (ULift.up (1, 0)) ≠ 0 :=
      by simpa only [y, sl2FirstColumnPolynomial,
        Variety.principalOpenChartInclusion, evalPolynomial_X] using
        Variety.principalOpenChart_nonzero (sl2FirstColumnPolynomial 1) x
    have ht : x.val none = (y.val (ULift.up (1, 0)))⁻¹ :=
      by simpa only [y, sl2FirstColumnPolynomial,
        Variety.principalOpenChartInclusion, evalPolynomial_X] using
        Variety.principalOpenChart_val_none (sl2FirstColumnPolynomial 1) x
    dsimp only [Fc]
    simp only [mulMaps_apply, curve_apply, X, T, evalPolynomial, MvPolynomial.eval₂_mul,
      MvPolynomial.eval₂_sub, MvPolynomial.eval₂_one, MvPolynomial.eval₂_X]
    rw [ht]
    simpa only [upper, lower, div_eq_mul_inv, map_mul, hu, hv,
      y, Variety.principalOpenChartInclusion] using
      congrArg f (factor_c y hy)

end Theory.AlgebraicGroup
