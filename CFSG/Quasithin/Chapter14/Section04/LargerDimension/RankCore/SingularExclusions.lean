module

public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.RankCore.Action
public import Theory.LinearAlgebra.QuadraticRankOneDisplacement
public import Theory.Representation.BinaryPermutation.FiveTensorSingular
public import Theory.SpecificGroups.ClassicalOrthogonal.SplitOdd.Geometry

/-!
# The two singular/nonsingular exclusions of 14.4.6

Apply the quadratic rank-one argument over a degree-two binary field to the
actual quotient module. In the tensor alternative, contraction to the
orthogonal A₅ core separates the singular marked vector from the displacement
of a transposition. Each conclusion is `Ṽ₂ ≰ [Ũ,a*]`, with `Ṽ₂` formed by
the literal central quotient map in `SourceAction.image`.

The branch inspection still has to supply the larger-field linearity or
transposition marking and the corresponding marked-vector coordinates.
These results do not assert that every low-rank involution has that form.

Source: Aschbacher--Smith, combined manuscript of 1 March 2004, 14.4.6(a),(b),
printed p.1008.
-/

public section
namespace CFSG.Quasithin.Chapter14.Section04.LargerDimension.RankCore
open Module Subgroup TensorProduct ClassicalOrthogonal

variable {H V : Type*} [Group H] (U : Subgroup H) [U.Normal]
  [AddCommGroup V] [Module (ZMod 2) V]

/-- The orthogonal exceptional branch: a nonzero singular marked vector
cannot lie in a moved F₄-point. Binary rank at most two supplies field rank
at most one; no nonsingularity conclusion is assumed. -/
theorem SourceAction.orthogonal_line_not_le_moved
    (d : SourceAction H U V)
    {F : Type*} [Field F] [Algebra (ZMod 2) F]
    (hdegree : finrank (ZMod 2) F = 2)
    (e : V ≃ₗ[ZMod 2] VectorD 2 F)
    (a : H ⧸ pCore 2 H) (t : VectorD 2 F ≃ₗ[F] VectorD 2 F)
    (he : ∀ v, e (d.representation a v) = t (e v))
    (ht : ∀ x, formD 2 F (t x) = formD 2 F x)
    (hr : d.movedRank a ≤ 2)
    (V₂ : Subgroup H) (s : U) (hs : (s : H) ∈ V₂)
    (hne : e (d.vector s) ≠ 0) (hsing : formD 2 F (e (d.vector s)) = 0) :
    ¬ d.image V₂ ≤ d.moved a := by
  have hsmall : finrank (ZMod 2)
      (LinearMap.range ((t.restrictScalars (ZMod 2)).toLinearMap - LinearMap.id)) ≤ 2 := by
    rw [← d.movedRank_eq_of_equivariant a e (t.restrictScalars (ZMod 2)).toLinearMap he]
    exact hr
  have hnot := QuadraticForm.singular_not_mem_displacement_degree_two hdegree
    (formD 2 F) polarD_nondegenerate.1 t ht hsmall (e (d.vector s)) hne hsing
  intro hle
  apply hnot
  rw [← d.moved_map a e (t.restrictScalars (ZMod 2)).toLinearMap he]
  exact ⟨d.vector s, hle (d.vector_mem_image V₂ s hs), rfl⟩

/-- The tensor exceptional branch, with the marked quotient vector expressed
in its two A₅ copies as the singular tensor `u ⊗ w`. -/
theorem SourceAction.tensor_line_not_le_moved
    (d : SourceAction H U V)
    {D W : Type*} [Group D] [AddCommGroup W] [Module (ZMod 2) W]
    (σ : Representation (ZMod 2) D W)
    (e : V ≃ₗ[ZMod 2] (BinaryPermutation.core (Fin 5) ⊗[ZMod 2] W))
    (a : H ⧸ pCore 2 H) (i j : Fin 5)
    (he : ∀ v, e (d.representation a v) =
      BinaryPermutation.FiveTensorQuadratic.tensorAction σ (Equiv.swap i j, 1) (e v))
    (V₂ : Subgroup H) (s : U) (hs : (s : H) ∈ V₂)
    (u : BinaryPermutation.core (Fin 5)) (hu : u ≠ 0)
    (hsing : BinaryPermutation.FiveGeometry.form u = 0)
    (w : W) (hw : w ≠ 0) (hmark : e (d.vector s) = u ⊗ₜ[ZMod 2] w) :
    ¬ d.image V₂ ≤ d.moved a := by
  intro hle
  apply BinaryPermutation.FiveTensorSingular.singular_tensor_not_mem_displacement σ i j u hu hsing w hw
  rw [← d.moved_map a e _ he, ← hmark]
  exact ⟨d.vector s, hle (d.vector_mem_image V₂ s hs), rfl⟩

end CFSG.Quasithin.Chapter14.Section04.LargerDimension.RankCore
