module

public import Theory.SpecificGroups.PSL3Two.UnitaryGenerators

/-!
# A faithful unitary representation of SL₃(2)

This constructs an injective homomorphism from the actual binary matrix group
into SL₃ over `FiniteField.Nine`. Every image matrix preserves the identity
Hermitian form. The elementary matrix `1 + E₀₁` maps to `unitaryInvolution`,
and the coordinate three-cycle maps to `unitaryCycle`.

The finite certificates come from simultaneously multiplying these two pairs
of matrices, beginning at the identity. A binary matrix is indexed by its nine
entries in row order, interpreted as the digits of a base-two integer (the
first entry is the least significant digit). The first table gives the image
matrix: its nine base-nine digits encode `a + bi` as `a + 3b`. Zero entries are
unused indices, whose binary matrix has determinant zero. The second table
records generator words for all determinant-one binary matrices.

The kernel checks determinant one, the unitary equation, a left inverse, the
word evaluations, and compatibility with left multiplication by each generator.
Induction on words then proves the homomorphism law. Thus the tables are
certificates checked against matrix arithmetic, not assumed multiplication
laws or a replacement group model.

Source: direct calculations with the matrices in `UnitaryGenerators`.
-/

namespace Matrix.PSL3Two
open FiniteField
private abbrev SL := SpecialLinearGroup (Fin 3) (ZMod 2)
private def binaryCode (a : SL) : Nat :=
  (a 0 0).val + 2 * (a 0 1).val + 4 * (a 0 2).val +
  8 * (a 1 0).val + 16 * (a 1 1).val + 32 * (a 1 2).val +
  64 * (a 2 0).val + 128 * (a 2 1).val + 256 * (a 2 2).val
set_option maxRecDepth 10000 in
private def table : Array Nat := #[
  0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 86094918, 120789800, 23693816, 94058600,
  0, 0, 0, 0, 111237304, 1180989, 382766002, 225894916,
  0, 0, 590499, 67599044, 0, 0, 210521444, 311454164,
  0, 0, 77152180, 43047468, 0, 0, 21685258, 51838648,
  0, 0, 306697276, 56595290, 98815408, 221138354, 0, 0,
  0, 0, 191396212, 40810736, 42818968, 363640604, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 4783779, 346605364, 220968724, 94859044,
  0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 306944036, 191448698, 538164, 77534480,
  0, 1076166, 0, 312265768, 0, 210585688, 0, 68502880,
  0, 111313424, 0, 55794850, 52048508, 0, 120344986, 0,
  0, 226290392, 0, 9567477, 0, 348718754, 0, 98605364,
  0, 382713512, 0, 176590900, 174477548, 0, 363576544, 0,
  0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 176531140, 9624988, 55347498, 312011848,
  0, 0, 0, 0, 40817864, 56409282, 43059845, 67735244,
  0, 0, 0, 0, 0, 0, 0, 0,
  0, 121112624, 220580668, 0, 0, 311483170, 68263706, 0,
  0, 86100005, 94725162, 0, 21561482, 0, 0, 120584036,
  0, 93664098, 4901068, 0, 348790258, 0, 0, 221109040,
  0, 23686364, 346665160, 0, 0, 174406168, 42943052, 0,
  0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 9684038, 346652120, 0, 0, 99515016, 225389720,
  0, 43053283, 0, 23804452, 0, 50558292, 0, 77829724,
  0, 77301100, 225918416, 0, 0, 307202474, 111018178, 0,
  0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 98453304, 42824962, 0, 0, 86106565, 111546604,
  0, 51619428, 0, 174419210, 0, 4842020, 0, 306674120,
  0, 21679588, 348777056, 0, 0, 176544344, 40699756, 0,
  0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 176604104, 4784589, 0, 0, 307476242, 50985716,
  0, 67968460, 0, 93796234, 99668336, 0, 78068738, 0,
  0, 544644, 382714898, 0, 225758258, 0, 0, 110778968,
  0, 0, 363574996, 221500858, 0, 0, 1069524, 120879280,
  0, 0, 0, 0, 0, 0, 0, 0,
  0, 311733562, 174464506, 0, 9566829, 0, 0, 56857804,
  0, 210587056, 0, 348731956, 346592324, 0, 191447168, 0,
  0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 311988368, 95121554, 50775676, 225360730, 0, 0,
  0, 40692628, 0, 86094180, 0, 110704810, 0, 99878200,
  0, 191394682, 1121949, 0, 77684026, 0, 0, 307231804,
  0, 363642152, 0, 120257954, 0, 649557, 0, 220603844,
  0, 42937058, 68131538, 0, 43048188, 0, 0, 55532480,
  0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 210520076, 21567152, 23811904, 382767388, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 55398888, 220857884, 307600132, 99450576, 0, 0,
  0, 56462868, 0, 120743464, 110633696, 0, 50622156, 0,
  0, 307069456, 111164084, 0, 0, 77755796, 225634288, 0,
  0, 221388632, 120212428, 0, 0, 67646020, 312376544, 0,
  0, 98386524, 0, 68176408, 77224760, 0, 94674492, 0,
  0, 0, 51686784, 311845868, 226165036, 93609792, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0
]
private def matrixOfCode (n : Nat) : Matrix (Fin 3) (Fin 3) Nine :=
  fun i j => let k := n / 9 ^ (3 * i.val + j.val)
             ⟨(k % 3 : Nat), (k / 3 % 3 : Nat)⟩
private def representationMatrix (a : SL) : Matrix (Fin 3) (Fin 3) Nine :=
  matrixOfCode (table[binaryCode a]?.getD 0)
set_option maxRecDepth 10000 in
private theorem representation_det : ∀ a : SL, (representationMatrix a).det = 1 := by
  decide +kernel

private def representationFunction (a : SL) : SpecialLinearGroup (Fin 3) Nine :=
  ⟨representationMatrix a, representation_det a⟩
set_option maxRecDepth 10000 in
private theorem representation_one : representationFunction 1 = 1 := by decide +kernel

set_option maxRecDepth 10000 in
private theorem representation_unitary : ∀ a : SL,
    ((representationFunction a).val.map star).transpose * (representationFunction a).val = 1 := by
  decide +kernel


private def nineCode (a : SpecialLinearGroup (Fin 3) Nine) : Nat :=
  let digit (i j : Fin 3) := (a i j).re.val + 3 * (a i j).im.val
  digit 0 0 + 9 * digit 0 1 + 81 * digit 0 2 +
  729 * digit 1 0 + 6561 * digit 1 1 + 59049 * digit 1 2 +
  531441 * digit 2 0 + 4782969 * digit 2 1 + 43046721 * digit 2 2
private def recover (a : SpecialLinearGroup (Fin 3) Nine) : Matrix (Fin 3) (Fin 3) (ZMod 2) :=
  let n := table.toList.idxOf (nineCode a)
  fun i j => (n / 2 ^ (3 * i.val + j.val) % 2 : Nat)
set_option maxRecDepth 10000 in
private theorem recover_representation : ∀ a : SL,
    recover (representationFunction a) = a.val := by decide +kernel

private theorem representation_injective : Function.Injective representationFunction := by
  intro a b h
  apply Subtype.ext
  rw [← recover_representation a, ← recover_representation b, h]

open scoped Matrix

private def sourceGen : Bool → SL
  | false => ⟨!![1,1,0; 0,1,0; 0,0,1], by decide⟩
  | true => ⟨!![0,1,0; 0,0,1; 1,0,0], by decide⟩
private def targetGen : Bool → SpecialLinearGroup (Fin 3) Nine
  | false => unitaryInvolution
  | true => unitaryCycle
set_option maxRecDepth 10000 in
private theorem representation_generator_mul : ∀ a : SL, ∀ s : Bool,
    representationFunction (sourceGen s * a) = targetGen s * representationFunction a := by
  decide +kernel

set_option maxRecDepth 10000 in
private def wordTable : Array (List Bool) := #[
  [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [],
  [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [],
  [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [],
  [], [], [], [false, true, false, true, false, true, true, false, true, false, true, false, true],
  [true, false, true, false, true, false, true, true, false, true, false],
  [true, false, true, false, true, true, false, true, false, true, false, true],
  [false, true, false, true, false, true, false, true, true, false, true, false], [], [], [], [],
  [false, true, false, true, true, false, true, false, true, false],
  [false, true, false, true, false, true, true, false, true, true, false, true],
  [true, false, true, false, true, true, false, true, true, false, true],
  [true, false, true, true, false, true, false, true, false], [], [], [true],
  [false, true, true, false, true, false, true, true, false, true, true], [], [], [false, true],
  [true, true, false, true, false, true, true, false, true, true], [], [], [true, true, false, true, true],
  [false, true, true, false, true, false, true], [], [], [true, true, false, true, false, true],
  [false, true, true, false, true, true], [], [],
  [true, false, true, false, true, true, false, true, false, true, true],
  [false, true, false, true, true, false, true, true, false, true, false],
  [false, true, false, true, false, true, true, false, true, false, true, true],
  [true, false, true, true, false, true, true, false, true, false], [], [], [], [],
  [true, false, true, false, true, true, false],
  [true, false, true, true, false, true, false, true, false, true, true, false, true],
  [false, true, false, true, true, false, true, false, true, false, true, true, false, true],
  [false, true, false, true, false, true, true, false], [], [], [], [], [], [], [], [], [], [], [], [], [],
  [], [true, true], [false, true, true], [false, true, true, false, true, false, true, true, false],
  [true, true, false, true, false, true, true, false], [], [], [], [], [], [], [], [], [], [], [], [],
  [true, true, false], [true, true, false, true, false, true, true],
  [false, true, true, false, true, false, true, true], [false, true, true, false], [],
  [true, false, true, false, true, false, true, true, false, true, false, true, false], [],
  [true, false, true, false, true, false, true, true, false, true, false, true], [],
  [true, false, true, false, true, true, false, true, false, true, false, true, true], [],
  [false, true, false, true, false, true, false, true, true, false, true, false, true], [],
  [false, true, false, true, false, true, true, false, true, false], [],
  [true, false, true, true, false, true, true, false, true, false, true],
  [true, false, true, false, true, true, false, true, false], [],
  [false, true, false, true, true, false, true, true, false, true, false, true], [], [],
  [false, true, false, true, true, false, true, false, true, false, true], [],
  [false, true, false, true, true, false, true, false, true, false, true, false], [],
  [true, false, true, true, false, true, false, true, false, true, false], [],
  [true, false, true, true, false, true, false, true, false, true], [],
  [true, false, true, true, false, true, true, false, true, false, true, false], [],
  [false, true, false, true, false, true, true, false, true],
  [true, false, true, false, true, true, false, true], [],
  [false, true, false, true, true, false, true, true, false, true, false, true, false], [], [], [], [], [],
  [], [], [], [], [], [], [], [], [false, true, false, true, true, false, true, false, true],
  [true, false, true, true, false, true, false, true],
  [true, false, true, false, true, true, false, true, true, false, true, false],
  [false, true, false, true, false, true, true, false, true, true, false, true, false], [], [], [], [],
  [true, true, false, true, false, true, false, true, true, false, true, false, true],
  [false, true, false, true, false, true, false, true, true, false, true],
  [true, false, true, false, true, true, false, true, false, true, false, true, false],
  [true, false, true, false, true, false, true, true, false, true], [], [], [], [], [], [], [], [], [],
  [false, true, true, false, true, false, true, true, false, true, true, false], [true, false], [], [],
  [true, true, false, true, false, true, true, false, true, true, false], [false, true, false], [], [],
  [true, false, true, true, false, true, false, true, false, true, true, false, true, false],
  [true, false, true, false, true, true], [],
  [false, true, false, true, true, false, true, false, true, false, true, true, false, true, false], [], [],
  [false, true, false, true, false, true, true], [],
  [false, true, false, true, true, false, true, true, false, true],
  [true, true, false, true, true, false, true, false, true, true], [],
  [false, true, true, false, true, true, false, true, false, true, true], [], [],
  [true, false, true, true, false, true, true, false, true], [],
  [false, true, true, false, true, false, true, false], [true, true, false, true, true, false], [], [],
  [false, true, true, false, true, true, false], [true, true, false, true, false, true, false], [], [], [],
  [], [], [], [], [], [], [], [],
  [false, true, false, true, false, true, true, false, true, false, true, false],
  [true, false, true, false, true, true, false, true, false, true, false], [], [],
  [true, false, true, false, true, false, true, true, false, true, false, true, true],
  [false, true, false, true, false, true, false, true, true, false, true, false, true, true], [], [], [],
  [false], [], [false, true, true, false, true, false, true, true, false, true], [],
  [true, true, false, true, false, true, true, false, true], [],
  [true, false, true, false, true, true, false, true, false, true],
  [false, true, false, true, false, true, true, false, true, false, true], [], [],
  [false, true, false, true, true, false, true, true, false, true, false, true, true],
  [true, false, true, true, false, true, true, false, true, false, true, true], [], [], [], [], [], [], [],
  [], [], [], [], [false, true, false, true, true, false, true, false, true, false, true, true],
  [true, false, true, false, true, true, false, true, true, false], [], [],
  [false, true, false, true, false, true, true, false, true, true, false],
  [true, false, true, true, false, true, false, true, false, true, true], [], [true, true, false, true], [],
  [true, true, false, true, false], [], [false, true, true, false, true, false], [],
  [false, true, true, false, true], [], [true, false, true, false, true, true, false, true, true],
  [false, true, false, true, true, false, true, false, true, false, true, true, false], [], [],
  [true, false, true, true, false, true, false, true, false, true, true, false],
  [false, true, false, true, false, true, true, false, true, true], [], [], [], [], [], [], [], [], [], [],
  [], [true, true, false, true, false, true, false, true, true, false, true, false],
  [false, true, true, false, true, false, true, false, true, true, false, true, false], [], [],
  [false, true, false, true, false, true, false, true, true, false],
  [true, false, true, false, true, false, true, true, false], [], [true, false, true, true], [],
  [false, true, false, true, true],
  [false, true, true, false, true, true, false, true, false, true, false, true, false], [],
  [true, true, false, true, true, false, true, false, true, false, true, false], [], [],
  [true, true, false, true, true, false, true, false, true],
  [false, true, true, false, true, true, false, true, false, true], [],
  [false, true, false, true, true, false, true, true, false], [], [],
  [true, false, true, true, false, true, true, false], [], [],
  [false, true, false, true, true, false, true, false],
  [false, true, true, false, true, true, false, true, false, true, false, true, true, false], [], [],
  [true, false, true, true, false, true, false],
  [true, true, false, true, true, false, true, false, true, false, true, true, false], [], [], [], [], [],
  [], [], [], [], [true, false, true, false, true],
  [false, true, true, false, true, false, true, false, true, true, false, true, true, false], [],
  [true, true, false, true, false, true, false, true, true, false, true, true, false], [], [],
  [false, true, false, true, false, true], [], [true, true, false, true, true, false, true, true], [],
  [true, true, false, true, false, true, false, true, true],
  [false, true, true, false, true, false, true, false, true, true], [],
  [true, false, true, false, true, false, true, false], [], [], [], [], [], [], [], [], [], [], [],
  [false, true, true, false, true, false, true, true, false, true, true, false, true],
  [true, true, false, true, false, true, true, false, true, true, false, true], [true, false, true],
  [false, true, false, true], [], [], [], [false, true, false, true, true, false, true, false, true, true],
  [], [true, false, true, true, false, true, false, true, true], [],
  [true, false, true, false, true, true, false, true, true, false, true, false, true], [],
  [false, true, false, true, false, true, true, false, true, true, false, true, false, true], [],
  [true, true, false, true, false, true, true, false, true, true, false, true, false],
  [false, true, true, false, true, false, true, true, false, true, true, false, true, false], [],
  [true, false, true, false], [], [], [false, true, false, true, false], [],
  [false, true, false, true, false, true, false, true, true, false, true, true, false], [],
  [false, true, false, true, false, true, false, true, true, false, true, true], [],
  [true, false, true, false, true, false, true, true, false, true, true, false], [],
  [true, false, true, false, true, false, true, true, false, true, true], [],
  [false, true, true, false, true, true, false, true, false],
  [false, true, true, false, true, false, true, false, true, false], [],
  [true, true, false, true, true, false, true, false], [], [],
  [true, true, false, true, false, true, false, true, false], [], [], [], [], [], [], [], [], [], [],
  [false, true, true, false, true, false, true, false, true],
  [false, true, true, false, true, true, false, true], [true, true, false, true, true, false, true],
  [true, true, false, true, false, true, false, true], [], [], [], [], [], [], [], [], [], [], [], [],
  [false, true, true, false, true, true, false, true, false, true, false],
  [true, true, false, true, true, false, true, false, true, false],
  [false, true, false, true, true, false, true, true], [true, false, true, true, false, true, true], [], [],
  [], [false, true, false, true, true, false], [], [true, false, true, true, false],
  [false, true, true, false, true, true, false, true, false, true, false, true], [],
  [true, true, false, true, true, false, true, false, true, false, true], [], [],
  [false, true, true, false, true, false, true, false, true, true, false, true],
  [true, true, false, true, false, true, false, true, true, false, true], [], [],
  [true, false, true, false, true, false, true, true],
  [false, true, false, true, false, true, false, true, true], [], [],
  [false, true, true, false, true, true, false, true, false, true, false, true, true],
  [false, true, false, true, true, false, true], [], [],
  [true, true, false, true, true, false, true, false, true, false, true, true],
  [true, false, true, true, false, true], [], [],
  [true, true, false, true, false, true, false, true, true, false], [],
  [false, true, false, true, false, true, false, true],
  [false, true, true, false, true, false, true, false, true, true, false], [],
  [true, false, true, false, true, false, true], [], [], [],
  [false, true, true, false, true, false, true, false, true, true, false, true, true],
  [true, false, true, false, true, false],
  [true, true, false, true, false, true, false, true, true, false, true, true],
  [false, true, false, true, false, true, false], [], [], [], [], [], [], [], [], [], []
]
private def word (a : SL) : List Bool := wordTable[binaryCode a]?.getD []
set_option maxRecDepth 10000 in
private theorem word_result : ∀ a : SL, ((word a).map sourceGen).prod = a := by
  decide +kernel

private theorem word_mul (w : List Bool) (a : SL) :
    representationFunction ((w.map sourceGen).prod * a) =
      (w.map targetGen).prod * representationFunction a := by
  induction w with
  | nil => simp
  | cons s w ih =>
    simp only [List.map_cons, List.prod_cons, mul_assoc]
    rw [representation_generator_mul, ih]

private theorem representation_mul (a b : SL) :
    representationFunction (a*b) = representationFunction a * representationFunction b := by
  have hw := word_mul (word a) 1
  simp only [mul_one, representation_one, word_result] at hw
  calc
    representationFunction (a*b) =
        representationFunction (((word a).map sourceGen).prod * b) := by rw [word_result]
    _ = ((word a).map targetGen).prod * representationFunction b := word_mul _ _
    _ = representationFunction a * representationFunction b := by rw [hw]

/-- The faithful three-dimensional unitary representation of the binary linear group. -/
public def unitaryRepresentation : SpecialLinearGroup (Fin 3) (ZMod 2) →*
    SpecialLinearGroup (Fin 3) Nine where
  toFun := representationFunction
  map_one' := representation_one
  map_mul' := representation_mul

public theorem unitaryRepresentation_injective : Function.Injective unitaryRepresentation :=
  representation_injective

/-- Every matrix in the representation preserves the identity Hermitian form. -/
public theorem unitaryRepresentation_unitary (a : SpecialLinearGroup (Fin 3) (ZMod 2)) :
    ((unitaryRepresentation a).val.map star).transpose * (unitaryRepresentation a).val = 1 :=
  representation_unitary a

end Matrix.PSL3Two
