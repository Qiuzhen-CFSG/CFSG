module

public import Theory.AlgebraicGroup.Instance.PGL2
public import Theory.AlgebraicGroup.Instance.GL

/-!
# The regular general-linear projection to PGL₂

The tensor-model PGL₂ carrier receives a genuine polynomial morphism from
GL₂. Its coordinates are entries of `(M⁻¹)ᵀ ⊗ M`; scalar multiplication cancels
between the two tensor factors. Comparison with the existing SL₂ projection
identifies the point map with the usual quotient by scalar matrices.

This supplies the regular map used for the local determinant construction of
the ordered-triple inverse in Borel, *Linear Algebraic Groups*, §10.8. No
square-root choice is used to establish regularity, including in characteristic
two.
-/

public noncomputable section
open scoped MatrixGroups
namespace Theory.AlgebraicGroup
universe u
variable {k : Type u} [Field k] [IsAlgClosed k]

omit [IsAlgClosed k] in
private lemma tensor_entry_of_projective_eq {n : ℕ} (A B : GL (Fin n) k)
    (h : Matrix.ProjGenLinGroup.mk A = Matrix.ProjGenLinGroup.mk B)
    (a b i j : Fin n) : (A⁻¹).val i a * A.val b j = (B⁻¹).val i a * B.val b j := by
  obtain ⟨r, rfl⟩ := Matrix.ProjGenLinGroup.mk_eq_mk_iff.mp h
  simp only [mul_inv_rev, ← map_inv, Units.val_mul,
    Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.diagonal_mul, Matrix.mul_diagonal]
  calc
    _ = (↑r⁻¹ * ↑r) * ((A⁻¹).val i a * A.val b j) := by simp
    _ = _ := by ring

private lemma pgl2_projection_onto : Function.Surjective (pgl2Projection (k := k)).onPoints := by
  exact (pgl2TensorMorphism (k := k)).codRestrictImageClosedSubgroup_surjective
    (fun x => ⟨x, rfl⟩)

private abbrev twoRank := Module.finrank k (Fin 2 → k)
private def rankCast : Matrix.ProjGenLinGroup (Fin (twoRank (k := k))) k ≃* PGL2 k := by
  rw [twoRank, Module.finrank_fin_fun k]

private def glPointToPGL2 (x : Variety.Point (glVariety (twoRank (k := k)) : Variety k)) :
    Variety.Point (pgl2Variety (k := k)) :=
  (pgl2PointMulEquiv (k := k)).symm (rankCast
    (Matrix.ProjGenLinGroup.mk (glPointEquiv _ x)))

private lemma pgl2_matrix_coordinate (g : Variety.Point (pgl2Variety (k := k)))
    (M : GL (Fin (twoRank (k := k))) k)
    (hM : rankCast (Matrix.ProjGenLinGroup.mk M) = pgl2PointMulEquiv g)
    (a b i j : Fin (twoRank (k := k))) :
    g.val (ULift.up (finProdFinEquiv (a, b), finProdFinEquiv (i, j))) =
      (M⁻¹).val i a * M.val b j := by
  obtain ⟨s, rfl⟩ := pgl2_projection_onto g
  rw [pgl2PointMulEquiv_projection] at hM
  have hclass : Matrix.ProjGenLinGroup.mk M =
      Matrix.SpecialLinearGroup.toPGL (slPointEquiv _ s) := by
    apply rankCast.injective
    exact hM
  change (slTensorActionMatrix _ (slPointEquiv _ s))
      (finProdFinEquiv (a, b)) (finProdFinEquiv (i, j)) = _
  rw [slTensorActionMatrix_apply]
  exact tensor_entry_of_projective_eq
    (Matrix.SpecialLinearGroup.toGL (slPointEquiv _ s)) M hclass.symm a b i j

private lemma glPointToPGL2_coordinate (x : Variety.Point (glVariety (twoRank (k := k)) : Variety k))
    (a b i j : Fin (twoRank (k := k))) :
    (glPointToPGL2 x).val (ULift.up (finProdFinEquiv (a, b), finProdFinEquiv (i, j))) =
      (x⁻¹).val (Sum.inl (i, a)) * x.val (Sum.inl (b, j)) := by
  rw [pgl2_matrix_coordinate (glPointToPGL2 x) (glPointEquiv _ x) (by simp [glPointToPGL2])]
  have hinv := (translationGLPointMulEquiv (k := k) (twoRank (k := k))).map_inv x
  exact congrArg (fun M : GL (Fin (twoRank (k := k))) k => M.val i a * x.val (Sum.inl (b, j))) hinv.symm

private def glToPGL2 : AlgebraicGroup.Morphism
    (glVariety (twoRank (k := k)) : Variety k) (pgl2Variety (k := k)) where
  toVariety :=
    { toFun := glPointToPGL2
      regular := by
        intro p
        let ab := finProdFinEquiv.symm p.down.1
        let ij := finProdFinEquiv.symm p.down.2
        refine ⟨AlgebraicGroup.invPolynomial (V := (glVariety (twoRank (k := k)) : Variety k)) (Sum.inl (ij.1, ab.1)) *
          MvPolynomial.X (Sum.inl (ab.2, ij.2)), ?_⟩
        intro x
        have hp : p = ULift.up (finProdFinEquiv (ab.1, ab.2),
            finProdFinEquiv (ij.1, ij.2)) := by
          apply ULift.ext
          change p.down = (finProdFinEquiv (finProdFinEquiv.symm p.down.1),
            finProdFinEquiv (finProdFinEquiv.symm p.down.2))
          simp only [Equiv.apply_symm_apply]
        rw [hp, glPointToPGL2_coordinate]
        rw [evalPolynomial_mul, evalPolynomial_X, AlgebraicGroup.inv_regular] }
  map_one := by
    apply (pgl2PointMulEquiv (k := k)).injective
    simp only [glPointToPGL2, MulEquiv.apply_symm_apply, map_one]
    change rankCast (Matrix.ProjGenLinGroup.mk
      ((translationGLPointMulEquiv _).toMonoidHom 1)) = 1
    simp
  map_mul x y := by
    apply (pgl2PointMulEquiv (k := k)).injective
    simp only [glPointToPGL2, MulEquiv.apply_symm_apply, map_mul]
    rw [← rankCast.map_mul, ← Matrix.ProjGenLinGroup.mk.map_mul]
    congr 2
    exact (translationGLPointMulEquiv _).map_mul x y

private def glRankChange (n : ℕ) (h : n = 2) : AlgebraicGroup.Morphism
    (glVariety 2 : Variety k) (glVariety n : Variety k) := by
  subst n
  exact .id _

omit [IsAlgClosed k] in
private lemma rankCast_glRankChange (n : ℕ) (hn : n = 2)
    (x : Variety.Point (glVariety 2 : Variety k)) :
    (show Matrix.ProjGenLinGroup (Fin n) k ≃* PGL2 k from by rw [hn])
      (Matrix.ProjGenLinGroup.mk (glPointEquiv n ((glRankChange n hn).onPoints x))) =
        Matrix.ProjGenLinGroup.mk (glPointEquiv 2 x) := by
  subst n
  rfl

def pgl2GeneralLinearProjection : AlgebraicGroup.Morphism
    (glVariety 2 : Variety k) (pgl2Variety (k := k)) :=
  glToPGL2.comp (glRankChange _ (Module.finrank_fin_fun k))

lemma pgl2GeneralLinearProjection_points (x : Variety.Point (glVariety 2 : Variety k)) :
    pgl2PointMulEquiv (pgl2GeneralLinearProjection.onPoints x) =
      Matrix.ProjGenLinGroup.mk (glPointEquiv 2 x) := by
  change pgl2PointMulEquiv (glPointToPGL2 ((glRankChange _ _).onPoints x)) = _
  rw [glPointToPGL2, MulEquiv.apply_symm_apply]
  exact rankCast_glRankChange _ (Module.finrank_fin_fun k) x

end Theory.AlgebraicGroup
