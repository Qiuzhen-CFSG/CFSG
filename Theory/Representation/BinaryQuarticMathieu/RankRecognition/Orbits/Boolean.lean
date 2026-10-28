module

public import Theory.Representation.BinaryQuarticMathieu.RankRecognition.Orbits.Evaluation
/-!
# Boolean evaluation with a proof of equality to the actual quartic

Boolean XOR and conjunction map to addition and multiplication in `ZMod 2`.
The six-minor determinant formula from `Evaluation.lean` therefore gives a
Boolean evaluator whose decoded value is the actual alternating form for every
four packed words. Literal indices avoid repeated reduction through `List.ofFn`
during kernel checking; equality with that enumeration is itself checked.
-/

@[expose] public section

namespace BinaryQuarticMathieu.RankRecognition.Orbits

def bitField (b : Bool) : F := if b then 1 else 0

theorem bitField_xor : ∀ a b, bitField (Bool.xor a b) = bitField a + bitField b := by
  decide +kernel

theorem bitField_and : ∀ a b, bitField (a && b) = bitField a * bitField b := by
  decide +kernel

def det4Bool (m : Fin 4 → Fin 4 → Bool) : Bool :=
  Bool.xor (Bool.xor (Bool.xor (Bool.xor (Bool.xor ((Bool.xor (m 0 0 && m 1 1) (m 0 1 && m 1 0) &&
    Bool.xor (m 2 2 && m 3 3) (m 2 3 && m 3 2))) (Bool.xor (m 0 0 && m 1 2) (m 0 2 && m 1 0) &&
    Bool.xor (m 2 1 && m 3 3) (m 2 3 && m 3 1))) (Bool.xor (m 0 0 && m 1 3) (m 0 3 && m 1 0) &&
    Bool.xor (m 2 1 && m 3 2) (m 2 2 && m 3 1))) (Bool.xor (m 0 1 && m 1 2) (m 0 2 && m 1 1) &&
    Bool.xor (m 2 0 && m 3 3) (m 2 3 && m 3 0))) (Bool.xor (m 0 1 && m 1 3) (m 0 3 && m 1 1) &&
    Bool.xor (m 2 0 && m 3 2) (m 2 2 && m 3 0))) (Bool.xor (m 0 2 && m 1 3) (m 0 3 && m 1 2) &&
    Bool.xor (m 2 0 && m 3 1) (m 2 1 && m 3 0))

theorem bitField_det4Bool (m : Fin 4 → Fin 4 → Bool) :
    bitField (det4Bool m) = det4Fast (fun r c => bitField (m r c)) := by
  simp only [det4Bool, det4Fast, bitField_xor, bitField_and]

theorem bitField_fold (l : List Bool) :
    bitField (l.foldr Bool.xor false) = (l.map bitField).sum := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.foldr_cons, List.map_cons, List.sum_cons, bitField_xor, ih]

def evaluationIndices : List (Fin 210) := [
  0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209
]

private theorem evaluationIndices_eq : evaluationIndices = List.ofFn id := by
  decide +kernel

def boolQuartic (v : Fin 4 → Nat) : Bool :=
  (evaluationIndices.map (fun i : Fin 210 => coefficientWord.testBit i.val &&
    det4Bool (fun r c => (v r).testBit (fastQuad i c).val))).foldr Bool.xor false

theorem bitField_boolQuartic (v : Fin 4 → Nat) :
    bitField (boolQuartic v) = quartic (fun r => vector (v r)) := by
  rw [← evalQuartic_eq, boolQuartic, evaluationIndices_eq, List.map_ofFn, bitField_fold, List.map_ofFn, List.sum_ofFn]
  unfold evalQuartic
  apply Finset.sum_congr rfl
  intro i _
  change bitField (coefficientWord.testBit i.val && _) = _
  cases hc : coefficientWord.testBit i.val
  · rfl
  · exact bitField_det4Bool (fun r c => (v r).testBit (fastQuad i c).val)

end BinaryQuarticMathieu.RankRecognition.Orbits
