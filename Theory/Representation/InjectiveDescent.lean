module

public import Mathlib.Algebra.CharZero.Infinite
public import Theory.Representation.ScalarDescent
public import Theory.Representation.CoefficientReduction

/-!
# Descent of injective intertwiners

An injective intertwiner between finite-dimensional representations after a
field extension descends to an injective intertwiner over an infinite base
field. Hom-space base change writes the extended map as a linear combination
of base-field intertwiners. Introduce an unrestricted generic reverse matrix
and specialize the determinant of its product with the generic intertwiner.
A linear left inverse makes this polynomial nonzero; polynomial extensionality
over an infinite field then supplies a base-field specialization.

The coordinate equivalence also identifies tensor-product scalar extension
with entrywise coefficient extension, giving the rectangular matrix version.
No finiteness hypothesis on the group or characteristic-zero hypothesis on the
fields is needed.

This is the determinant-specialization method for scalar descent, as in the
field-of-definition arguments of Serre, *Linear Representations of Finite
Groups*, Chapter 12. The Hom-space base-change input is developed in
`Theory.Representation.ScalarDescent`.
-/

public section

open scoped TensorProduct
noncomputable section

/-- The determinant of a generic reverse matrix times a generic linear combination. -/
private def genericDeterminant
    {F α β γ : Type*} [Field F]
    [Fintype α] [DecidableEq α] [Fintype β] [Fintype γ]
    (A : γ → Matrix β α F) : MvPolynomial (γ ⊕ (α × β)) F :=
  Matrix.det (Matrix.of (fun i j => MvPolynomial.X (Sum.inr (i, j))) *
    Matrix.of (fun i j => ∑ k, MvPolynomial.C (A k i j) *
      MvPolynomial.X (Sum.inl k)))

/-- Evaluation commutes with the two matrices and their product determinant. -/
private theorem eval_genericDeterminant
    {F T α β γ : Type*} [Field F] [CommRing T]
    [Fintype α] [DecidableEq α] [Fintype β] [Fintype γ]
    (A : γ → Matrix β α F) (g : F →+* T)
    (y : γ → T) (C : Matrix α β T) :
    MvPolynomial.eval₂Hom g (Sum.elim y (fun ij => C ij.1 ij.2))
      (genericDeterminant A) = (C * ∑ k, y k • (A k).map g).det := by
  classical
  unfold genericDeterminant
  rw [RingHom.map_det]
  congr 1
  change (Matrix.map (_ * _) (MvPolynomial.eval₂Hom g _)) = _
  rw [Matrix.map_mul]
  congr 1
  · ext i j
    simp [Matrix.map_apply, Matrix.of_apply]
  · ext i j
    simp [Matrix.map_apply, Matrix.of_apply, Matrix.sum_apply, Matrix.smul_apply, mul_comm]

/-- Specialize both sets of variables over the infinite base field. -/
private theorem exists_det_mul_sum_ne_zero
    {F E α β γ : Type*} [Field F] [Infinite F] [Field E]
    [Fintype α] [DecidableEq α] [Fintype β] [Fintype γ]
    (f : F →+* E) (A : γ → Matrix β α F)
    (x : γ → E) (B : Matrix α β E)
    (h : (B * ∑ k, x k • (A k).map f).det ≠ 0) :
    ∃ (y : γ → F) (C : Matrix α β F), (C * ∑ k, y k • A k).det ≠ 0 := by
  classical
  let p := genericDeterminant A
  have hp : p ≠ 0 := by
    intro hp
    apply h
    rw [← eval_genericDeterminant A f x B, show genericDeterminant A = 0 from hp, map_zero]
  obtain ⟨z, hz⟩ : ∃ z, MvPolynomial.eval z p ≠ 0 := by
    by_contra! hzero
    apply hp
    apply MvPolynomial.funext
    intro z
    simpa using hzero z
  refine ⟨fun k => z (Sum.inl k), fun i j => z (Sum.inr (i, j)), ?_⟩
  have he := eval_genericDeterminant A (RingHom.id F) (fun k => z (Sum.inl k))
    (fun i j => z (Sum.inr (i, j)))
  have hfun : Sum.elim (fun k => z (Sum.inl k))
      (fun ij : α × β => z (Sum.inr (ij.1, ij.2))) = z := by
    funext a
    cases a <;> rfl
  rw [hfun] at he
  change MvPolynomial.eval₂Hom (RingHom.id F) z (genericDeterminant A) ≠ 0 at hz
  rw [he] at hz
  simpa only [RingHom.coe_id, Matrix.map_id] using hz

namespace Representation

/-- Existence of an injective intertwiner descends along any field extension
over an infinite base field. -/
theorem exists_injective_intertwiner_of_extendScalars
    {F E G V W : Type*} [Field F] [Infinite F] [Field E] [Algebra F E]
    [Group G] [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    [AddCommGroup W] [Module F W] [FiniteDimensional F W]
    (ρ : Representation F G V) (σ : Representation F G W)
    (h : ∃ i : (extendScalars E ρ).IntertwiningMap (extendScalars E σ),
      Function.Injective i) :
    ∃ j : ρ.IntertwiningMap σ, Function.Injective j := by
  classical
  obtain ⟨i, hi⟩ := h
  let bV := Module.finBasis F V
  let bW := Module.finBasis F W
  let : Module F (ρ →ₗ σ) := RepMap.module ρ σ
  let : Module.Finite F (ρ →ₗ σ) :=
    Module.Finite.of_injective (IntertwiningMap.toLinearMapl ρ σ)
      (by
        intro f g h
        apply RepMap.toLinearMap_injective f g
        exact h)
  let b := Module.finBasis F (ρ →ₗ σ)
  let q := intertwiningMapBaseChangeEquiv (E := E) ρ σ
  obtain ⟨z, hz⟩ := q.surjective i
  let x := fun k => (b.baseChange E).repr z k
  have hsum : (∑ k, x k • extendScalars_map E (b k)) = i := by
    rw [← hz]
    calc
      (∑ k, x k • extendScalars_map E (b k)) =
          ∑ k, q (x k • (b.baseChange E k)) := by
        apply Finset.sum_congr rfl
        intro k _
        simp [q, Module.Basis.baseChange_apply, intertwiningMapBaseChangeEquiv_tmul]
      _ = q (∑ k, x k • (b.baseChange E k)) := by rw [map_sum]
      _ = q z := by rw [(b.baseChange E).sum_repr z]
  let A := fun k => LinearMap.toMatrix bV bW (b k).toLinearMap
  have hmatrix : LinearMap.toMatrix (bV.baseChange E) (bW.baseChange E) i.toLinearMap =
      ∑ k, x k • (A k).map (algebraMap F E) := by
    rw [← hsum]
    change LinearMap.toMatrix (bV.baseChange E) (bW.baseChange E)
      (IntertwiningMap.toLinearMapl _ _ (∑ k, x k • extendScalars_map E (b k))) = _
    rw [map_sum, map_sum]
    apply Finset.sum_congr rfl
    intro k _
    ext a c
    simp [A, LinearMap.toMatrix_apply, extendScalars_map_toLinearMap,
      Module.Basis.baseChange_apply, LinearMap.baseChange_tmul,
      Module.Basis.baseChange_repr_tmul, Matrix.map_apply, Matrix.smul_apply,
      Algebra.smul_def]
  obtain ⟨r, hr⟩ := i.toLinearMap.exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.mpr hi)
  have hdet : ((LinearMap.toMatrix (bW.baseChange E) (bV.baseChange E) r) *
      ∑ k, x k • (A k).map (algebraMap F E)).det ≠ 0 := by
    rw [← hmatrix, ← LinearMap.toMatrix_comp, hr, LinearMap.toMatrix_id, Matrix.det_one]
    exact one_ne_zero
  obtain ⟨y, C, hC⟩ := exists_det_mul_sum_ne_zero (algebraMap F E) A x _ hdet
  let j : ρ →ₗ σ := ∑ k, y k • b k
  have hj : LinearMap.toMatrix bV bW j.toLinearMap = ∑ k, y k • A k := by
    change LinearMap.toMatrix bV bW (IntertwiningMap.toLinearMapl _ _
      (∑ k, y k • b k)) = _
    simp only [map_sum, map_smul, IntertwiningMap.toLinearMapl_apply, A]
  let t := (Matrix.toLin bW bV C).comp j.toLinearMap
  have ht : IsUnit (LinearMap.toMatrix bV bV t).det := by
    apply isUnit_iff_ne_zero.mpr
    change (LinearMap.toMatrix bV bV
      ((Matrix.toLin bW bV C).comp j.toLinearMap)).det ≠ 0
    rw [LinearMap.toMatrix_comp bV bW bV, LinearMap.toMatrix_toLin, hj]
    exact hC
  have htinj : Function.Injective t := by
    have he := (LinearEquiv.ofIsUnitDet ht).injective
    change Function.Injective (LinearEquiv.ofIsUnitDet ht).toLinearMap at he
    rwa [LinearEquiv.coe_ofIsUnitDet] at he
  exact ⟨j, fun a c hac => htinj (congrArg (Matrix.toLin bW bV C) hac)⟩

/-- Tensor-product scalar extension agrees with entrywise coefficient extension
in the standard finite coordinate basis. -/
def extendScalarsMapCoefficientsEquiv
    {F E G ι : Type*} [Field F] [Field E] [Algebra F E] [Monoid G]
    [Fintype ι] [DecidableEq ι]
    (ρ : Representation F G (ι → F)) :
    extendScalars E ρ ≃ₗ mapCoefficients (algebraMap F E) ρ where
  toLinearEquiv := ((Pi.basisFun F ι).baseChange E).equivFun
  isIntertwining' g := by
    apply Module.Basis.ext ((Pi.basisFun F ι).baseChange E)
    intro j
    change ((Pi.basisFun F ι).baseChange E).equivFun
        (extendScalars E ρ g (((Pi.basisFun F ι).baseChange E) j)) =
      mapCoefficients (algebraMap F E) ρ g
        (((Pi.basisFun F ι).baseChange E).equivFun
          (((Pi.basisFun F ι).baseChange E) j))
    have hcoord : ((Pi.basisFun F ι).baseChange E).equivFun
        (((Pi.basisFun F ι).baseChange E) j) = Pi.single j 1 := by
      ext k
      simp [Pi.single_apply, eq_comm]
    rw [hcoord]
    ext k
    have h := congrFun (congrFun
      (mapCoefficients_toMatrix (algebraMap F E) ρ g) k) j
    simpa [LinearMap.comp_apply, Module.Basis.equivFun_apply,
      Module.Basis.baseChange_apply, extendScalars_apply, LinearMap.baseChange_tmul,
      Module.Basis.baseChange_repr_tmul, LinearMap.toMatrix'_apply,
      Matrix.map_apply, Algebra.smul_def, Pi.basisFun_apply] using h.symm

/-- An injective intertwiner between coefficient-extended finite coordinate
representations descends to the infinite base field. -/
theorem exists_injective_intertwiner_of_mapCoefficients
    {F E G ι κ : Type*} [Field F] [Infinite F] [Field E] [Group G]
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (f : F →+* E) (ρ : Representation F G (ι → F))
    (σ : Representation F G (κ → F))
    (h : ∃ i : (mapCoefficients f ρ).IntertwiningMap (mapCoefficients f σ),
      Function.Injective i) :
    ∃ j : ρ.IntertwiningMap σ, Function.Injective j := by
  let : Algebra F E := f.toAlgebra
  obtain ⟨i, hi⟩ := h
  let eρ := extendScalarsMapCoefficientsEquiv (E := E) ρ
  let eσ := extendScalarsMapCoefficientsEquiv (E := E) σ
  apply exists_injective_intertwiner_of_extendScalars (E := E) ρ σ
  refine ⟨eσ.symm.toRepMap.comp (i.comp eρ.toRepMap), ?_⟩
  exact eσ.symm.toLinearEquiv.injective.comp (hi.comp eρ.toLinearEquiv.injective)

end Representation
