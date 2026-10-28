module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.RecognitionGeometry.LocalA5.EdgeIndexed

/-!
# Scalar certificates for the edge A₅ embedding

All large loops use only packed point maps and word lists. Small separate
bridges compare those maps with the genuine A₅ and degree-100 permutations.
The resulting word and generator-transition equalities are the inputs to
the actual embedding. Source: retained ATLAS local words and `source/`.
-/

public section
namespace Sporadic.LeechRelated.J2.RecognitionGeometry.LocalA5.EdgeChecks
open Theory.GroupTheory InnerInvolutionCores.NoncentralData
open GeneratorPair.SecondOrbitCertificate
open EdgeIndexed

set_option Elab.async false

private theorem checkedAt {n : Nat} {f : Fin n → Bool}
    (h : checkFin f = true) (i : Fin n) : f i = true := by
  have hi := List.all_eq_true.mp h i.val (List.mem_range.mpr i.isLt)
  simpa only [dif_pos i.isLt] using hi

set_option maxRecDepth 20000 in
theorem word_eq (j : Fin 60) : EdgeData.word (simpleEnum j) = word j := by
  have h : checkFin (fun j : Fin 60 => decide (EdgeData.word (simpleEnum j) = word j)) = true := by
    decide +kernel
  exact of_decide_eq_true (checkedAt h j)

set_option maxRecDepth 20000 in
private theorem packed_eq (j : Fin 60) : EdgeData.packed (simpleEnum j) = row j := by
  have h : checkFin (fun j : Fin 60 => decide (EdgeData.packed (simpleEnum j) = row j)) = true := by
    decide +kernel
  exact of_decide_eq_true (checkedAt h j)

theorem value_eq (j : Fin 60) (i : Fin 100) : EdgeData.value (simpleEnum j) i = value j i := by
  exact congrArg (fun r => unpack r i) (packed_eq j)

set_option maxRecDepth 20000 in
theorem letterValue_eq (s : Fin 2) (i : Fin 100) : letterValue s i = EdgeData.table s i := by
  have h : checkFin (fun s : Fin 2 => checkFin (fun i : Fin 100 =>
      decide (letterValue s i = EdgeData.table s i))) = true := by decide +kernel
  exact of_decide_eq_true (checkedAt (checkedAt h s) i)

theorem wordValue_eq (w : List (Fin 2)) (i : Fin 100) :
    wordValue w i = evalWord EdgeData.table w i := by
  induction w with
  | nil => rfl
  | cons s w ih => rw [wordValue, ih, letterValue_eq]; rfl

set_option maxRecDepth 20000 in
theorem words_checked (j : Fin 60) (i : Fin 100) : wordValue (word j) i = value j i := by
  have h : checkFin (fun j : Fin 60 => checkFin (fun i : Fin 100 =>
      decide (wordValue (word j) i = value j i))) = true := by decide +kernel
  exact of_decide_eq_true (checkedAt (checkedAt h j) i)

set_option maxRecDepth 20000 in
theorem steps_checked (s : Fin 2) (j : Fin 60) (i : Fin 100) :
    value (step s j) i = letterValue s (value j i) := by
  have h : checkFin (fun s : Fin 2 => checkFin (fun j : Fin 60 => checkFin (fun i : Fin 100 =>
      decide (value (step s j) i = letterValue s (value j i))))) = true := by decide +kernel
  exact of_decide_eq_true (checkedAt (checkedAt (checkedAt h s) j) i)

set_option maxRecDepth 20000 in
theorem model_step (s : Fin 2) (j : Fin 60) :
    EdgeData.model s * simpleEnum j = simpleEnum (step s j) := by
  have h : checkFin (fun s : Fin 2 => checkFin (fun j : Fin 60 => checkFin (fun i : Fin 5 =>
      decide ((EdgeData.model s).val (simpleMap j i) = simpleMap (step s j) i)))) = true := by
    decide +kernel
  apply Subtype.ext
  apply Equiv.ext
  intro i
  exact of_decide_eq_true (checkedAt (checkedAt (checkedAt h s) j) i)

set_option maxRecDepth 20000 in
theorem model_words (j : Fin 60) : evalWord EdgeData.model (word j) = simpleEnum j := by
  have h : checkFin (fun j : Fin 60 => checkFin (fun i : Fin 5 =>
      decide ((evalWord EdgeData.model (word j)).val i = simpleMap j i))) = true := by
    decide +kernel
  exact Subtype.ext (Equiv.ext (fun i => of_decide_eq_true (checkedAt (checkedAt h j) i)))

set_option maxRecDepth 20000 in
theorem pair_injective {i j : Fin 60} (h0 : value i 0 = value j 0)
    (h1 : value i 1 = value j 1) : i = j := by
  have h : checkFin (fun i : Fin 60 => checkFin (fun j : Fin 60 =>
      decide (value i 0 = value j 0 → value i 1 = value j 1 → i = j))) = true := by
    decide +kernel
  exact of_decide_eq_true (checkedAt (checkedAt h i) j) h0 h1

end Sporadic.LeechRelated.J2.RecognitionGeometry.LocalA5.EdgeChecks
