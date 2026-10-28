module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.RankTwo.FieldDual
public import Theory.SpecificGroups.PSL3.OuterSolvable.Actions
public import Mathlib.Algebra.Module.ZMod

/-!
# Field and graph comparisons for the odd-degree natural module

Entrywise field transport intertwines the binary natural actions. The dot
product identifies the inverse-transpose twist with the defining-field dual;
composing with trace gives the binary dual. The projective comparison uses
the actual SL₃-to-PSL₃ map and keeps its original component marking.

Source: Aschbacher–Smith, proof of 13.8.20, printed pp.954–955. These are
explicit comparisons; arbitrary-automorphism coverage and the B.4.2 sieve
remain separate steps.
-/

@[expose] public noncomputable section

open Representation Representation.HigherFieldBorelFixedSpaces
open Matrix Matrix.PSL3.OuterSolvable
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.RankTwo
variable {F E : Type*} [Field F] [Field E] [Algebra (ZMod 2) F] [Algebra (ZMod 2) E]

/-- Apply the coefficient-field equivalence in each coordinate. -/
def fieldCoordinates (d : ℕ) (e : F ≃+* E) : (Fin d → F) ≃ₗ[ZMod 2] (Fin d → E) where
  toFun v := fun i => e (v i)
  invFun v := fun i => e.symm (v i)
  left_inv v := by ext i; exact e.symm_apply_apply (v i)
  right_inv v := by ext i; exact e.apply_symm_apply (v i)
  map_add' v w := by ext i; exact e.map_add (v i) (w i)
  map_smul' c v := by
    ext i
    exact ZMod.map_smul e.toAddMonoidHom c (v i)

/-- The natural action commutes with entrywise field transport. -/
theorem fieldCoordinates_intertwines (d : ℕ) (e : F ≃+* E) (g : SL(d,F)) (v : Fin d → F) :
    fieldCoordinates d e (binaryNatural d g v) =
      binaryNatural d (Atlas.fieldEquivSL d e g) (fieldCoordinates d e v) := by
  ext i
  change e (∑ j, g.val i j * v j) = ∑ j, e (g.val i j) * e (v j)
  simp only [map_sum, map_mul]

omit [Algebra (ZMod 2) F] in
private theorem graphSL_matrix (g : SL(3,F)) :
    (graphSL F g).val = g⁻¹.val.transpose := by
  have he : SpecialLinearGroup.transpose g⁻¹ = (SpecialLinearGroup.transpose g)⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    apply Subtype.ext
    change g⁻¹.val.transpose * g.val.transpose = 1
    rw [← Matrix.transpose_mul]
    have h : g.val * g⁻¹.val = 1 := congrArg Subtype.val (mul_inv_cancel g)
    rw [h, Matrix.transpose_one]
  exact congrArg (fun x : SL(3,F) => x.val) he.symm

variable [Finite F]

/-- The actual graph twist is the binary dual, through dot product and trace. -/
def graphNaturalBinaryDual : Representation.Equiv
    ((binaryNatural (F := F) 3).comp (graphSL F).toMonoidHom)
    (binaryNatural (F := F) 3).dual where
  toLinearEquiv := ((dotProductEquiv F (Fin 3)).restrictScalars (ZMod 2)).trans (traceDualEquiv 3)
  isIntertwining' g := by
    apply LinearMap.ext
    intro v
    apply LinearMap.ext
    intro w
    change Algebra.trace (ZMod 2) F (((graphSL F g).val *ᵥ v) ⬝ᵥ w) =
      Algebra.trace (ZMod 2) F (v ⬝ᵥ (g⁻¹.val *ᵥ w))
    rw [graphSL_matrix, ← Matrix.vecMul_transpose, Matrix.dotProduct_mulVec,
      Matrix.transpose_transpose]

variable [CharP F 2]

/-- Descend the same comparison through the odd-degree projection equivalence. -/
def projectiveGraphNaturalBinaryDual {n : ℕ} (hn : Odd n) (hF : Nat.card F = 2 ^ n) :
    Representation.Equiv ((projectiveBinaryNatural hn hF).comp (graph F).toMonoidHom)
      (projectiveBinaryNatural hn hF).dual where
  toLinearEquiv := graphNaturalBinaryDual.toLinearEquiv
  isIntertwining' g := by
    obtain ⟨g,rfl⟩ := Matrix.PSL3.projection_surjective F g
    apply LinearMap.ext
    intro v
    have he : graph F (Matrix.PSL3.projection F g) =
        Matrix.PSL3.projection F (graphSL F g) := rfl
    change graphNaturalBinaryDual.toLinearEquiv
        (projectiveBinaryNatural hn hF (graph F (Matrix.PSL3.projection F g)) v) = _
    rw [he, projectiveBinaryNatural_projection]
    apply LinearMap.ext
    intro w
    change _ = Algebra.trace (ZMod 2) F
      (v ⬝ᵥ (projectiveBinaryNatural hn hF (Matrix.PSL3.projection F g)⁻¹ w))
    rw [← map_inv, projectiveBinaryNatural_projection]
    exact LinearMap.congr_fun
      (LinearMap.congr_fun (graphNaturalBinaryDual.isIntertwining' g) v) w

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.RankTwo
