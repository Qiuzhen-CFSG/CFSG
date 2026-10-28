module

public import Theory.SpecificGroups.PSL3.SevenAction.Block
public import Theory.SpecificGroups.PSL3.OuterSolvable.OddPrimeCoverage
public import Theory.SpecificGroups.PSL3.CartanActions.NormalizerForm
public import Theory.AtlasPort.ExceptionalIsomorphisms.Simplicity


/-!
# Linear and graph normal forms for automorphisms of PSL₃(7)

The existing odd-prime coverage theorem supplies all automorphisms. Over the
prime field ZMod 7 the field factor is trivial. Inverse transpose normalizes
the actual GL₃ conjugation image, leaving a linear factor and at most one
graph factor. All identities use the same canonical central projection.

Source: GLS3, Theorem 2.5.12(a), and its matrix actions in §2.7; the calculation
is used in Aschbacher--Smith 15.3.38, printed p.1137. The imported ATLAS
simplicity and perfectness proofs retain their original license and attribution.
-/

public section

open scoped MatrixGroups
open Subgroup Matrix.PSL3.OuterSolvable
namespace Matrix.PSL3.SevenAction

local instance : Fact (Nat.Prime 7) := ⟨by decide⟩

/-- The inverse-transpose automorphism on invertible matrices. -/
@[expose] def inverseTransposeGL {F : Type*} [Field F] : GL (Fin 3) F →* GL (Fin 3) F where
  toFun g := {
    val := g.inv.transpose
    inv := g.val.transpose
    val_inv := by rw [← Matrix.transpose_mul, g.val_inv, Matrix.transpose_one]
    inv_val := by rw [← Matrix.transpose_mul, g.inv_val, Matrix.transpose_one] }
  map_one' := Units.ext Matrix.transpose_one
  map_mul' g h := Units.ext (Matrix.transpose_mul h.inv g.inv)

/-- Inverse transpose on SL₃ agrees with the GL₃ formula. -/
theorem graphSL_toGL {F : Type*} [Field F] (x : SL(3,F)) :
    SpecialLinearGroup.toGL (graphSL F x) = inverseTransposeGL (SpecialLinearGroup.toGL x) := by
  apply Units.ext
  exact (Matrix.adjugate_transpose x.val).symm

/-- The graph automorphism normalizes the concrete linear conjugation image. -/
theorem graph_linearConj (g : GL (Fin 3) (ZMod 7)) :
    graph (ZMod 7) * linearConj (ZMod 7) g =
      linearConj (ZMod 7) (inverseTransposeGL g) * graph (ZMod 7) := by
  ext y
  obtain ⟨x,rfl⟩ := projection_surjective (ZMod 7) y
  change QuotientGroup.mk (graphSL (ZMod 7) (linearConjSL (ZMod 7) g x)) =
    QuotientGroup.mk (linearConjSL (ZMod 7) (inverseTransposeGL g) (graphSL (ZMod 7) x))
  congr 1
  apply SpecialLinearGroup.toGL_injective
  rw [graphSL_toGL, linearConjSL_toGL, map_mul, map_mul, map_inv,
    linearConjSL_toGL, graphSL_toGL]

/-- Every automorphism is linear conjugation or linear conjugation followed
by inverse transpose; there is no nontrivial field automorphism of ZMod 7. -/
theorem automorphism_normal_form (α : MulAut Model) :
    ∃ g : GL (Fin 3) (ZMod 7), α = linearConj (ZMod 7) g ∨
      α = linearConj (ZMod 7) g * graph (ZMod 7) := by
  let : IsSimpleGroup Model := Atlas.psl_simple_high_rank 3 (by decide)
  let : Group.IsPerfect Model := Atlas.psl_perfect 3 (by decide)
  have hc := standard_eq_top_of_odd_prime_card (ZMod 7)
    (Group.IsPerfect.not_isSolvable Model) (by decide : Nat.Prime 7)
    (by decide : Odd 7) (Nat.card_zmod 7)
  obtain ⟨g, σ, h⟩ := Matrix.PSL3.CartanActions.NormalizerForm.standard_factorization (ZMod 7)
    (by intro σ m; rw [Subsingleton.elim σ 1, map_one, one_mul, mul_one]; rfl)
    (fun g => ⟨inverseTransposeGL g, graph_linearConj g⟩)
    (by intro σ; rw [Subsingleton.elim σ 1, map_one]; exact Commute.one_left _)
    α (hc ▸ mem_top α)
  refine ⟨g, ?_⟩
  simpa only [Subsingleton.elim σ 1, map_one, mul_one] using h

end Matrix.PSL3.SevenAction
