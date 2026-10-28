module

public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.VectorStabilizer.Shear.Parameters
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.OrbitCover.KernelEquations.FiniteRestriction.QuadraticRelations.LinearMembership.FiniteAlgebra.Linear

/-!
# Linear coordinates of the two shear tests

The coefficient of each entry of Sᵀ T + Tᵀ S is computed for the exhaustive
symmetric parameter S. Packed linear forms also evaluate the thirteen actual
radical generators. These algebraic identities connect the elimination
witnesses to matrices, without any numerical rank assumption.

Source: VectorStabilizer/source/README.md and Shear/source/README.md.
-/

@[expose] public section
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false
open scoped Matrix
namespace Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound.VectorStabilizer.Shear.KernelCertificate
open OrbitCoverCoordinates OrbitCoverCoordinates.LinearMembership
open GeneratorCertificates FiniteAlgebra

attribute [local irreducible] symmetricEntry pairingInverse testIU

abbrev Position := Fin 50 × Fin 50

def radicalWord (p : Position) : ℕ :=
  xorList (List.ofFn (fun t : Fin 13 =>
    if ((radicalKRows.get t).get p.1).testBit p.2.val then 2 ^ t.val else 0))

theorem radicalWord_spec (p : Position) (t : Fin 13) :
    bit (radicalWord p) t.val = radicalKGenerator t p.1 p.2 := by
  simp only [radicalWord, bit_xorList, List.map_ofFn, List.sum_ofFn]
  rw [Finset.sum_eq_single t]
  · cases h : ((radicalKRows.get t).get p.1).testBit p.2.val <;>
      simp [h, bit, Nat.testBit_two_pow, radicalKGenerator, decodeRestrictionRows]
  · intro a _ hat
    cases h : ((radicalKRows.get a).get p.1).testBit p.2.val <;>
      simp [h, bit, Nat.testBit_two_pow, hat, Fin.val_inj]
  · simp

def coefficientWord (rows : Vector ℕ 50) (p : Position) : ℕ :=
  xorList (List.ofFn (fun a : Fin 50 =>
    (if (rows.get a).testBit p.2.val
      then 2 ^ (symmetricEntry a p.1).val else 0) ^^^
    (if (rows.get a).testBit p.1.val
      then 2 ^ (symmetricEntry a p.2).val else 0)))

theorem ev_cond_unit {n : ℕ} (x : Fin n → ZMod 2) (b : Bool) (i : Fin n) :
    ev x (if b then 2 ^ i.val else 0) = (if b then 1 else 0) * x i := by
  cases b <;> simp [ev_zero, ev_unit]

theorem coefficientWord_spec (x : Parameter) (rows : Vector ℕ 50) (p : Position) :
    ev x (coefficientWord rows p) =
      ((symmetricMatrix x)ᵀ * decodeRestrictionRows rows +
        (decodeRestrictionRows rows)ᵀ * symmetricMatrix x) p.1 p.2 := by
  simp only [coefficientWord, ev_xorList, List.map_ofFn, List.sum_ofFn,
    Function.comp_def, ev_xor, ev_cond_unit, Matrix.add_apply, Matrix.mul_apply,
    Matrix.transpose_apply, Finset.sum_add_distrib, symmetricMatrix, decodeRestrictionRows]
  apply congrArg₂ (· + ·)
  · apply Finset.sum_congr rfl
    intro a _
    exact mul_comm _ _
  · rfl

theorem effect_twisted (t : Fin 2) (x : Parameter) (rows : Vector ℕ 50)
    (hr : decodeRestrictionRows rows = pairingInverseᵀ * testIU t) :
    testEffect t x = (symmetricMatrix x)ᵀ * decodeRestrictionRows rows +
      (decodeRestrictionRows rows)ᵀ * symmetricMatrix x := by
  simp only [testEffect, shearOfParameter, hr, Matrix.transpose_mul,
    Matrix.transpose_transpose, Matrix.mul_assoc]

end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound.VectorStabilizer.Shear.KernelCertificate
