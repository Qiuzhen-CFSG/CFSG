module

public import Theory.SpecificGroups.PSL3Four.FieldExtension.Basic
public import Theory.LinearAlgebra.FiniteProjectiveMatrixGroup

/-!
# The semilinear overgroup of the field extension

Entrywise Frobenius descends from `GL(3, F)` to the concrete projective group
`PGL(3, F)`. Its order-two action defines the actual semidirect product
`PΓL(3, 4) = PGL(3, 4) ⋊ C₂`. The natural map from the field extension of
`PSL(3, 4)` is injective and has index three.

The construction is the matrix quotient supplied by Mathlib; no abstract
identification of the full semilinear group is used.

Source: Aschbacher, *Sporadic Groups*, §18, especially 18.7–18.9.
-/

public section
open scoped MatrixGroups
namespace Matrix.PSL3Four
noncomputable section

/-- The projective general linear group in dimension three over `F`. -/
abbrev PGL := Matrix.ProjGenLinGroup (Fin 3) F

/-- Entrywise application of the field Frobenius on `PGL`. -/
@[expose] def pglMap : PGL →* PGL :=
  Matrix.ProjGenLinGroup.map fieldFrobenius.toRingHom

@[simp] theorem pglMap_mk (g : Matrix.GeneralLinearGroup (Fin 3) F) :
    pglMap (Matrix.ProjGenLinGroup.mk g) =
      Matrix.ProjGenLinGroup.mk (Matrix.GeneralLinearGroup.map fieldFrobenius.toRingHom g) := rfl

@[simp] theorem pglMap_involutive (g : PGL) : pglMap (pglMap g) = g := by
  induction g using Matrix.ProjGenLinGroup.induction_on with
  | mk g =>
    have hcomp : fieldFrobenius.toRingHom.comp fieldFrobenius.toRingHom = RingHom.id F := by
      ext x
      exact fieldFrobenius_involutive x
    change ((Matrix.ProjGenLinGroup.map fieldFrobenius.toRingHom).comp
      (Matrix.ProjGenLinGroup.map fieldFrobenius.toRingHom))
      (Matrix.ProjGenLinGroup.mk g) = _
    rw [← Matrix.ProjGenLinGroup.map_comp, hcomp, Matrix.ProjGenLinGroup.map_id]
    rfl

/-- The involutive projective Frobenius automorphism. -/
@[expose] def pglFrobenius : MulAut PGL where
  toFun := pglMap
  invFun := pglMap
  left_inv := pglMap_involutive
  right_inv := pglMap_involutive
  map_mul' := pglMap.map_mul

@[simp] theorem pglFrobenius_apply (g : PGL) : pglFrobenius g = pglMap g := rfl

@[simp] theorem pglFrobenius_involutive (g : PGL) :
    pglFrobenius (pglFrobenius g) = g := pglMap_involutive g

theorem pglFrobenius_sq : pglFrobenius ^ 2 = 1 := by
  ext g
  exact pglFrobenius_involutive g

@[simp] theorem pglFrobenius_toPGL (A : PSL) :
    pglFrobenius (Matrix.ProjectiveSpecialLinearGroup.toPGL A) =
      Matrix.ProjectiveSpecialLinearGroup.toPGL (pslFrobenius A) := by
  induction A using QuotientGroup.induction_on with
  | H A =>
    simp [pglFrobenius, pglMap, Matrix.ProjectiveSpecialLinearGroup.toPGL_mk,
      Matrix.ProjGenLinGroup.map_mk, pslFrobenius_mk]
    congr 1
    ext i j
    rfl

/-- The projective field action of `C₂`. -/
@[expose] def pglAction : C2 →* MulAut PGL :=
  involutionHom pglFrobenius pglFrobenius_sq

@[simp] theorem pglAction_generator :
    pglAction (Multiplicative.ofAdd (1 : ZMod 2)) = pglFrobenius :=
  involutionHom_generator _ _

/-- The full concrete projective semilinear group. -/
abbrev PGammaL := PGL ⋊[pglAction] C2

@[simp] theorem pglAction_toPGL (t : C2) (A : PSL) :
    pglAction t (Matrix.ProjectiveSpecialLinearGroup.toPGL A) =
      Matrix.ProjectiveSpecialLinearGroup.toPGL (fieldAction t A) := by
  change ZMod 2 at t
  fin_cases t
  · rfl
  · change pglAction (Multiplicative.ofAdd (1 : ZMod 2))
      (Matrix.ProjectiveSpecialLinearGroup.toPGL A) =
      Matrix.ProjectiveSpecialLinearGroup.toPGL
        (fieldAction (Multiplicative.ofAdd (1 : ZMod 2)) A)
    rw [pglAction_generator, fieldAction_generator]
    exact pglFrobenius_toPGL A

/-- The natural map from the field extension into the projective semilinear group. -/
@[expose] def fieldExtensionToPGammaL : FieldExtension →* PGammaL :=
  SemidirectProduct.map Matrix.ProjectiveSpecialLinearGroup.toPGL (MonoidHom.id C2) (by
    intro t
    ext A
    exact (pglAction_toPGL t A).symm)

@[simp] theorem fieldExtensionToPGammaL_apply (g : FieldExtension) :
    fieldExtensionToPGammaL g =
      ⟨Matrix.ProjectiveSpecialLinearGroup.toPGL g.left, g.right⟩ := rfl

@[simp] theorem fieldExtensionToPGammaL_linear (A : PSL) :
    fieldExtensionToPGammaL (linearInclusion A) =
      SemidirectProduct.inl (Matrix.ProjectiveSpecialLinearGroup.toPGL A) := by
  rw [fieldExtensionToPGammaL_apply]
  change (⟨Matrix.ProjectiveSpecialLinearGroup.toPGL A, 1⟩ : PGammaL) =
    ⟨Matrix.ProjectiveSpecialLinearGroup.toPGL A, 1⟩
  rfl

@[simp] theorem fieldExtensionToPGammaL_field (t : C2) :
    fieldExtensionToPGammaL (fieldInclusion t) = SemidirectProduct.inr t := by
  rw [fieldExtensionToPGammaL_apply]
  change (⟨Matrix.ProjectiveSpecialLinearGroup.toPGL 1, t⟩ : PGammaL) = ⟨1, t⟩
  simp

theorem fieldExtensionToPGammaL_injective :
    Function.Injective fieldExtensionToPGammaL := by
  intro g h e
  apply SemidirectProduct.ext
  · exact Matrix.ProjectiveSpecialLinearGroup.toPGL_injective (congrArg SemidirectProduct.left e)
  · exact congrArg (fun x : PGammaL => x.right) e

instance : Finite PGammaL :=
  Finite.of_equiv (PGL × C2) SemidirectProduct.equivProd.symm

theorem card_PGL : Nat.card PGL = 60480 := by
  let := Fintype.ofFinite F
  have hGL : Nat.card (Matrix.GeneralLinearGroup (Fin 3) F) = 181440 := by
    have h := Matrix.card_GL_field (𝔽 := F) 3
    have hc : Fintype.card F = 4 := by
      rw [← Nat.card_eq_fintype_card, card_F]
    norm_num [hc, Fin.prod_univ_succ] at h
    exact h
  have hUnits : Nat.card Fˣ = 3 := by
    have hc : Fintype.card F = 4 := by
      rw [← Nat.card_eq_fintype_card, card_F]
    rw [Nat.card_units]
    norm_num [hc]
  have hcenter : Nat.card (Subgroup.center (Matrix.GeneralLinearGroup (Fin 3) F)) = 3 := by
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
    have hs : Function.Injective (Matrix.GeneralLinearGroup.scalar (Fin 3) :
        Fˣ →* Matrix.GeneralLinearGroup (Fin 3) F) := by
      intro a b h
      apply Units.ext
      have hh := congrArg (fun M : Matrix.GeneralLinearGroup (Fin 3) F =>
          (M : Matrix (Fin 3) (Fin 3) F) (0 : Fin 3) (0 : Fin 3)) h
      simpa [Matrix.GeneralLinearGroup.coe_scalar] using hh
    rw [← Nat.card_congr (MonoidHom.ofInjective hs).toEquiv, hUnits]
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup
    (Subgroup.center (Matrix.GeneralLinearGroup (Fin 3) F))] at hGL
  rw [hcenter] at hGL
  change Nat.card (Matrix.GeneralLinearGroup (Fin 3) F ⧸ Subgroup.center _) = 60480
  omega

theorem card_PGammaL : Nat.card PGammaL = 120960 := by
  rw [Nat.card_congr SemidirectProduct.equivProd, Nat.card_prod, card_PGL, card_C2]

theorem fieldExtensionToPGammaL_range_index :
    fieldExtensionToPGammaL.range.index = 3 := by
  have hRange : Nat.card fieldExtensionToPGammaL.range = 40320 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective fieldExtensionToPGammaL_injective).toEquiv,
      card_FieldExtension]
  have h := fieldExtensionToPGammaL.range.card_mul_index
  rw [hRange, card_PGammaL] at h
  omega

end
end Matrix.PSL3Four
