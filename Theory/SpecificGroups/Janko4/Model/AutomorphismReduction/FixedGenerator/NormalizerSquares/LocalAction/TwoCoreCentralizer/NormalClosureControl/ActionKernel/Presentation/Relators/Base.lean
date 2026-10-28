module

public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.NormalClosureControl.ActionKernel.Presentation.Reduction

/-!
# Certified lifts of the max2 quotient relators

Shared subwords factor the explicit words in `Presentation.Data`. The original
ATLAS max2 matrices and thirteen normal-closure generators are already checked
in `CentralizerReduction`. Each additional product is checked by kernel reduction
of the proved packed arithmetic; Python supplies witnesses only. The resulting
relator lifts are actual words in the relative normal closure, with no local
identification or order assumed. See `Presentation/source/README.md`.
-/

@[expose] public section
namespace Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.NormalClosureControl.ActionKernel.Presentation.Relators
open Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.NormalClosureControl.Certificates Janko4.GeneratorCertificates

set_option maxRecDepth 10000
set_option maxHeartbeats 1600000

lemma decoded_product {a b c : Vector ℕ 112} (hp : packedMul a b = c) :
    decodeRows a * decodeRows b = decodeRows c := by rw [← decode_packedMul, hp]

lemma eval_inv {G M : Type*} [_root_.Group G] [Monoid M] (f : G →* M)
    {g : G} {A B : M} (ha : f g = A) (hab : A * B = 1) : f g⁻¹ = B := by
  calc
    f g⁻¹ = f g⁻¹ * (A * B) := by rw [hab, mul_one]
    _ = B := by rw [← ha, ← mul_assoc, ← map_mul, inv_mul_cancel, map_one, one_mul]

def wordEval (w : List (Bool × Bool)) : BinaryMatrix :=
  representation (FreeGroup.lift localGenerators (FreeGroup.mk w))
lemma wordEval_append (u v : List (Bool × Bool)) :
    wordEval (u ++ v) = wordEval u * wordEval v := by
  simp only [wordEval, ← FreeGroup.mul_mk, map_mul]
lemma wordEval_positive (b : Bool) :
    wordEval [(b, true)] = representation (localGenerators b) := by
  simp only [wordEval, FreeGroup.lift_mk, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, Bool.cond_true, mul_one]
lemma wordEval_negative (b : Bool) {A B : BinaryMatrix}
    (ha : representation (localGenerators b) = A)
    (hab : A * B = 1) : wordEval [(b, false)] = B := by
  simpa only [wordEval, FreeGroup.lift_mk, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, Bool.cond_false, mul_one] using eval_inv representation ha hab
lemma wordEval_product {u v : List (Bool × Bool)} {a b c : Vector ℕ 112}
    (hu : wordEval u = decodeRows a) (hv : wordEval v = decodeRows b)
    (hp : packedMul a b = c) : wordEval (u ++ v) = decodeRows c := by
  rw [wordEval_append, hu, hv, decoded_product hp]

def matrixProduct (m : ℕ) : BinaryMatrix :=
  maskProduct (fun i => decodeRows (basisRows i)) m

lemma representation_maskProduct (m : ℕ) : representation (maskProduct basis m) =
    matrixProduct m := by
  simp only [map_maskProduct, representation_basis, matrixProduct]

lemma relator_mem_of_matrix_evaluation (i : Fin 29)
    (heval : representation (localRelator i) = matrixProduct (relatorMask i)) :
    localRelator i ∈ localNormalClosure := by
  have he : localRelator i = maskProduct basis (relatorMask i) :=
    representation_injective (heval.trans (representation_maskProduct _).symm)
  rw [he]
  exact maskProduct_mem localNormalClosure basis basis_mem_normalClosure _

end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.NormalClosureControl.ActionKernel.Presentation.Relators
