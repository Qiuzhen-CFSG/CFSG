module
public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalOrder.QuotientCount.UpperBound.Reduction

/-!
# Evaluating factored signed words

Evaluation of concatenated lists is multiplicative. These lemmas transfer the
packed matrix certificates for the words of `UpperBound.Data` to the actual
local subgroup, using the certified ATLAS local-generator evaluations.
-/

@[expose] public section
namespace Janko4.Cardinality.QuotientCount.UpperBound.RelatorCertificates
open KernelCount KernelCount.Relations Janko4.GeneratorCertificates
variable (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1)
def wordEval (w : List (Bool × Bool)) : BinaryMatrix :=
  representation hA hB (FreeGroup.lift (localGenerators hA hB) (FreeGroup.mk w))
lemma wordEval_append (u v : List (Bool × Bool)) :
    wordEval hA hB (u ++ v) = wordEval hA hB u * wordEval hA hB v := by
  simp only [wordEval, ← FreeGroup.mul_mk, map_mul]
lemma wordEval_positive (b : Bool) :
    wordEval hA hB [(b, true)] = representation hA hB (localGenerators hA hB b) := by
  simp only [wordEval, FreeGroup.lift_mk, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, Bool.cond_true, mul_one]
lemma wordEval_negative (b : Bool) {A B : BinaryMatrix}
    (ha : representation hA hB (localGenerators hA hB b) = A)
    (hab : A * B = 1) : wordEval hA hB [(b, false)] = B := by
  simpa only [wordEval, FreeGroup.lift_mk, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, Bool.cond_false, mul_one] using eval_inv (representation hA hB) ha hab
lemma wordEval_product {u v : List (Bool × Bool)} {a b c : Vector ℕ 112}
    (hu : wordEval hA hB u = decodeRows a) (hv : wordEval hA hB v = decodeRows b)
    (hp : packedMul a b = c) : wordEval hA hB (u ++ v) = decodeRows c := by
  rw [wordEval_append, hu, hv, decoded_product hp]
end Janko4.Cardinality.QuotientCount.UpperBound.RelatorCertificates
