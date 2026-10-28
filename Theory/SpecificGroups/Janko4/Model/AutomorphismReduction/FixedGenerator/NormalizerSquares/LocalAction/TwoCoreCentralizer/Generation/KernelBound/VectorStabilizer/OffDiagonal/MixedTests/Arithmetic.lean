module
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.VectorStabilizer.CoordinatesData
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.OrbitCover.KernelEquations.FiniteRestriction.QuadraticRelations.LinearMembership.FiniteAlgebra.Linear

/-!
# Linear forms for the mixed-generator tests

Each upper-triangular coordinate of Dᵀ M + Mᵀ D is a linear form in
the 600 actual entries of D. We identify its packed coefficient word and
also the word of values on the thirteen literal radical-K generators.
These identities connect the finite certificates to the actual matrices.

Source: VectorStabilizer/source/README.md and the unchanged ATLAS matrices.
-/

@[expose] public section
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false
open scoped Matrix
namespace Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound.VectorStabilizer.OffDiagonal.MixedTestCertificate
open OrbitCoverCoordinates OrbitCoverCoordinates.LinearMembership
open GeneratorCertificates FiniteAlgebra

abbrev Position := Fin 50 × Fin 50

def radicalWord (p : Position) : ℕ :=
  xorList (List.ofFn (fun t : Fin 13 =>
    if ((radicalKRows.get t).get p.1).testBit p.2.val then 2 ^ t.val else 0))

lemma radicalWord_spec (p : Position) (t : Fin 13) :
    bit (radicalWord p) t.val = radicalKGenerator t p.1 p.2 := by
  simp only [radicalWord, bit_xorList, List.map_ofFn, List.sum_ofFn]
  rw [Finset.sum_eq_single t]
  · cases h : ((radicalKRows.get t).get p.1).testBit p.2.val <;>
      simp [h, bit, Nat.testBit_two_pow, radicalKGenerator, decodeRestrictionRows]
  · intro a _ hat
    cases h : ((radicalKRows.get a).get p.1).testBit p.2.val <;>
      simp [h, bit, Nat.testBit_two_pow, hat, Fin.val_inj]
  · simp

def coefficientWord (m : Fin 40) (p : Position) : ℕ :=
  xorList (List.ofFn (fun a : Fin 12 =>
    (if ((mixedGeneratorRows.get m).get a).testBit p.2.val
      then 2 ^ (finProdFinEquiv (a,p.1)).val else 0) ^^^
    (if ((mixedGeneratorRows.get m).get a).testBit p.1.val
      then 2 ^ (finProdFinEquiv (a,p.2)).val else 0)))

lemma ev_cond_unit {n : ℕ} (x : Fin n → ZMod 2) (b : Bool) (i : Fin n) :
    ev x (if b then 2 ^ i.val else 0) = (if b then 1 else 0) * x i := by
  cases b <;> simp [ev_zero, ev_unit]

lemma coefficientWord_spec (D : MixedMatrix) (m : Fin 40) (p : Position) :
    ev (flat D) (coefficientWord m p) =
      (Dᵀ * mixedGenerator m + (mixedGenerator m)ᵀ * D) p.1 p.2 := by
  simp only [coefficientWord, ev_xorList, List.map_ofFn, List.sum_ofFn,
    Function.comp_def, ev_xor, ev_cond_unit, Matrix.add_apply, Matrix.mul_apply, Matrix.transpose_apply,
    Finset.sum_add_distrib]
  simp only [flat, Equiv.symm_apply_apply, mixedGenerator]
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  exact mul_comm _ _

end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound.VectorStabilizer.OffDiagonal.MixedTestCertificate
