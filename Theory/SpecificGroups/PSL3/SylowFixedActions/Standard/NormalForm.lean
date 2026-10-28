module

public import Theory.SpecificGroups.PSL3.OuterSolvable.Actions
public import Theory.SpecificGroups.PSL3.CartanActions.NormalizerForm

/-!
# Standard automorphisms over a prime field

Field automorphisms of ZMod p are trivial. The existing factorization of the
concrete standard subgroup therefore has only a linear factor and an optional
inverse-transpose factor. The matrix compatibility proof is adapted from
`OddInvolutionFixed.NormalForm`, keeping arbitrary-automorphism coverage out
of this module's imports.

Source: GLS3, §2.7, `refs/KGroup/GLS3/chapter2.tex`, lines 1111–1115.
-/

public section
open scoped MatrixGroups
namespace Matrix.PSL3.SylowFixedActions.Standard
open Matrix.PSL3.OuterSolvable

variable {F : Type*} [Field F]

private def inverseTransposeGL : GL (Fin 3) F →* GL (Fin 3) F where
  toFun g := {
    val := g.inv.transpose
    inv := g.val.transpose
    val_inv := by rw [← Matrix.transpose_mul, g.val_inv, Matrix.transpose_one]
    inv_val := by rw [← Matrix.transpose_mul, g.inv_val, Matrix.transpose_one] }
  map_one' := Units.ext Matrix.transpose_one
  map_mul' g h := Units.ext (Matrix.transpose_mul h.inv g.inv)

private theorem graphSL_toGL (x : SL(3, F)) :
    SpecialLinearGroup.toGL (graphSL F x) = inverseTransposeGL (SpecialLinearGroup.toGL x) := by
  apply Units.ext
  exact (Matrix.adjugate_transpose x.val).symm

private theorem graph_linearConj (g : GL (Fin 3) F) :
    graph F * linearConj F g = linearConj F (inverseTransposeGL g) * graph F := by
  ext y
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center SL(3, F)) y
  change QuotientGroup.mk (graphSL F (linearConjSL F g x)) =
    QuotientGroup.mk (linearConjSL F (inverseTransposeGL g) (graphSL F x))
  congr 1
  apply SpecialLinearGroup.toGL_injective
  rw [graphSL_toGL, linearConjSL_toGL, map_mul, map_mul, map_inv,
    linearConjSL_toGL, graphSL_toGL]

/-- Standardness alone gives the linear/graph normal form over a prime field.
No assertion of coverage of arbitrary automorphisms is used. -/
theorem normal_form (p : ℕ) [Fact p.Prime]
    (α : MulAut PSL(3, ZMod p)) (hα : α ∈ standard (ZMod p)) :
    ∃ g : GL (Fin 3) (ZMod p),
      α = linearConj (ZMod p) g ∨ α = linearConj (ZMod p) g * graph (ZMod p) := by
  obtain ⟨g, σ, ha⟩ := CartanActions.NormalizerForm.standard_factorization (ZMod p)
    (by intro σ m; rw [Subsingleton.elim σ 1, map_one, one_mul, mul_one]; rfl)
    (fun g => ⟨inverseTransposeGL g, graph_linearConj g⟩)
    (by intro σ; rw [Subsingleton.elim σ 1, map_one]; exact Commute.one_left _)
    α hα
  exact ⟨g, by simpa only [Subsingleton.elim σ 1, map_one, mul_one] using ha⟩

end Matrix.PSL3.SylowFixedActions.Standard
