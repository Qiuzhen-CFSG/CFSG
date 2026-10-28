module

public import Theory.SpecificGroups.PSL3Four.CentralCover.ExtendedCentralizer.ResidualAction.ProjectiveFixer.Candidate
public import Theory.SpecificGroups.PSL3.CartanActions.NormalizerForm

/-!
# Linear–field–graph forms for the standard projective subgroup

Every element of the standard subgroup of `Aut(PSL₃(4))` is a `standardForm`.
Entrywise field transport moves past linear conjugation by transporting its
matrix. Inverse transpose moves past linear conjugation by taking the inverse
transpose of its matrix, and commutes with field transport. These identities
on matrix representatives discharge all the inputs of `standard_factorization`.
The two possible graph factors are then represented by the elements of `C2`.

This is the standard-form input to the projective pointwise-fixer calculation
underlying Aschbacher–Smith 15.3.38, printed pp.1136–1137,
`refs/quasithin.pdf` (manuscript of 1 March 2004). The matrix descriptions of the
standard actions are in GLS3, §2.7, `refs/KGroup/GLS3/chapter2.tex`.
-/

open scoped MatrixGroups
open Matrix.PSL3.OuterSolvable

namespace Matrix.PSL3Four.ExtendedCentralizer.ProjectiveFixer

private theorem fieldSL_toGL (σ : F ≃+* F) (x : SL) :
    SpecialLinearGroup.toGL (SpecialLinearGroup.map σ.toRingHom x) =
      GeneralLinearGroup.map σ.toRingHom (SpecialLinearGroup.toGL x) := Units.ext rfl

private theorem field_linearConj (σ : F ≃+* F) (A : GL (Fin 3) F) :
    PSL3.OuterSolvable.fieldAction F σ * linearConj F A =
      linearConj F (GeneralLinearGroup.map σ.toRingHom A) *
        PSL3.OuterSolvable.fieldAction F σ := by
  apply MulEquiv.ext
  intro y
  induction y using QuotientGroup.induction_on with
  | H x =>
    simp only [MulAut.mul_apply, fieldAction_mk, linearConj_mk]
    congr 1
    apply SpecialLinearGroup.toGL_injective
    rw [fieldSL_toGL, linearConjSL_toGL, map_mul, map_mul, map_inv,
      linearConjSL_toGL, fieldSL_toGL]

private def inverseTransposeGL : GL (Fin 3) F →* GL (Fin 3) F where
  toFun g := {
    val := g.inv.transpose
    inv := g.val.transpose
    val_inv := by rw [← Matrix.transpose_mul, g.val_inv, Matrix.transpose_one]
    inv_val := by rw [← Matrix.transpose_mul, g.inv_val, Matrix.transpose_one] }
  map_one' := Units.ext Matrix.transpose_one
  map_mul' g h := Units.ext (Matrix.transpose_mul h.inv g.inv)

private theorem graphSL_toGL (x : SL) :
    SpecialLinearGroup.toGL (graphSL F x) = inverseTransposeGL (SpecialLinearGroup.toGL x) := by
  apply Units.ext
  exact (Matrix.adjugate_transpose x.val).symm

private theorem graph_linearConj (A : GL (Fin 3) F) :
    graph F * linearConj F A = linearConj F (inverseTransposeGL A) * graph F := by
  apply MulEquiv.ext
  intro y
  induction y using QuotientGroup.induction_on with
  | H x =>
    change QuotientGroup.mk (graphSL F (linearConjSL F A x)) =
      QuotientGroup.mk (linearConjSL F (inverseTransposeGL A) (graphSL F x))
    congr 1
    apply SpecialLinearGroup.toGL_injective
    rw [graphSL_toGL, linearConjSL_toGL, map_mul, map_mul, map_inv,
      linearConjSL_toGL, graphSL_toGL]

private theorem field_commute_graph (σ : F ≃+* F) :
    Commute (PSL3.OuterSolvable.fieldAction F σ) (graph F) := by
  apply MulEquiv.ext
  intro y
  induction y using QuotientGroup.induction_on with
  | H x =>
    simp only [MulAut.mul_apply, fieldAction_mk, graph_mk]
    rw [map_inv]
    congr 2

/-- Every standard projective automorphism has a linear–field–graph form. -/
public theorem exists_standardForm (a : MulAut PSL) (ha : a ∈ PSL3.OuterSolvable.standard F) :
    ∃ A σ t, a = standardForm A σ t := by
  obtain ⟨A, σ, h | h⟩ := PSL3.CartanActions.NormalizerForm.standard_factorization F
    field_linearConj (fun A => ⟨inverseTransposeGL A, graph_linearConj A⟩)
    field_commute_graph a ha
  · exact ⟨A, σ, 1, by simpa only [standardForm, map_one, mul_one] using h⟩
  · exact ⟨A, σ, Multiplicative.ofAdd (1 : ZMod 2), by
      simpa only [standardForm, involutionHom_generator] using h⟩

end Matrix.PSL3Four.ExtendedCentralizer.ProjectiveFixer
