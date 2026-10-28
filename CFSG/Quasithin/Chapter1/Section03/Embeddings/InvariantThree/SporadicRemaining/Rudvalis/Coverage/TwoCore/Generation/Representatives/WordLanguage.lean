module
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicRemaining.Rudvalis.Coverage.TwoCore.Generation.FixedSylow

/-!
# Words for prospective Rudvalis double-coset representatives

The alphabet is `a, b, a⁻¹, b⁻¹` in the original degree-4060 model.
The two max4 words are expanded by the preserved ATLAS straight-line
program, so local words also give explicit words in the standard generators.
Evaluation uses the already kernel-certified standard and max4 point maps.
The bridges below are algebraic induction on words; no external computation
is used as proof evidence.

Sources: the ATLAS programs and action convention in
`Rudvalis.Model.SylowOvergroups.Definitions` and `Model.PermutationData`.
The application is Aschbacher--Smith, printed p.511 (PDF p.528), citing
Aschbacher, *Overgroups of Sylow subgroups in sporadic groups* (1986), no.343.
-/

namespace Rudvalis.SylowOvergroups.TwoCore.Generation.Representatives
open RadicalCoverage.SylowCertificate
set_option maxRecDepth 4096

/-- Standard letters, with positive generators followed by their inverses. -/
@[expose] public def letter (i : Fin 4) : Model := ![a,b,a⁻¹,b⁻¹] i
/-- Inversion of a letter in either four-letter alphabet. -/
@[expose] public def inverseLetter (i : Fin 4) : Fin 4 := ![2,3,0,1] i
/-- Evaluate a standard-generator word, with the first letter on the left. -/
@[expose] public def wordValue (w : List (Fin 4)) : Model := (w.map letter).prod
/-- Reverse the word and invert each letter. -/
@[expose] public def inverseWord (w : List (Fin 4)) : List (Fin 4) :=
  (w.map inverseLetter).reverse
/-- The certified left-action maps of the standard letters. -/
@[expose] public def letterMap (i : Fin 4) : Fin 4060 → Fin 4060 :=
  ![Data.aMap, Data.bMap, Data.aMap, fun x => Data.bMap (Data.bMap (Data.bMap x))] i
/-- Pure point-map evaluation in the standard letters. -/
@[expose] public def wordMap (w : List (Fin 4)) : Fin 4060 → Fin 4060 :=
  LocalOrder.evalWord letterMap w

public theorem letter_smul (i : Fin 4) (x : Fin 4060) : letter i • x = letterMap i x := by
  fin_cases i <;> rfl
public theorem wordValue_smul (w : List (Fin 4)) (x : Fin 4060) :
    wordValue w • x = wordMap w x :=
  LocalOrder.prod_smul letter letterMap letter_smul w x
public theorem wordValue_append (u v : List (Fin 4)) :
    wordValue (u ++ v) = wordValue u * wordValue v := by
  simp only [wordValue, List.map_append, List.prod_append]
public theorem letter_inverseLetter (i : Fin 4) : letter (inverseLetter i) = (letter i)⁻¹ := by
  fin_cases i <;> simp [letter, inverseLetter]
public theorem wordValue_inverseWord (w : List (Fin 4)) :
    wordValue (inverseWord w) = (wordValue w)⁻¹ := by
  simp only [wordValue, inverseWord, List.map_reverse, List.map_map,
    List.prod_inv_reverse, Function.comp_def, letter_inverseLetter]

/-- The literal ATLAS max4 words and their inverses, in standard letters. -/
@[expose] public def max4Words : Fin 4 → List (Fin 4) :=
  let r3 := [0,1]
  let r4 := r3 ++ [1]
  let r5 := r3 ++ r4
  let r6 := r3 ++ r5
  let r8 := r6 ++ r5
  let r9 := r3 ++ r8
  let r8' := r9 ++ r9
  let x := inverseWord r8' ++ [1,1] ++ r8'
  let y := inverseWord r6 ++ (r8 ++ r8 ++ r8 ++ r8 ++ r8) ++ r6
  ![x,y,inverseWord x,inverseWord y]
public theorem max4Words_value (i : Fin 4) : wordValue (max4Words i) = candidateLetter i := by
  have hx : wordValue (max4Words 0) = max4Generators.1 := by
    simp only [max4Words, Matrix.cons_val_zero, wordValue_append, wordValue_inverseWord]
    simp only [wordValue, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
      mul_one, letter, Matrix.cons_val_zero, Matrix.cons_val_one]
    simp only [max4Generators]
  have hy : wordValue (max4Words 1) = max4Generators.2 := by
    simp only [max4Words, Matrix.cons_val_one, Matrix.cons_val_zero,
      wordValue_append, wordValue_inverseWord]
    simp only [wordValue, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
      mul_one, letter, Matrix.cons_val_zero, Matrix.cons_val_one]
    simp only [max4Generators, pow_succ, pow_zero, one_mul]
  fin_cases i
  · exact hx
  · exact hy
  · exact (wordValue_inverseWord _).trans (congrArg Inv.inv hx)
  · exact (wordValue_inverseWord _).trans (congrArg Inv.inv hy)

/-- Expand each max4 letter into its explicit standard-generator word. -/
@[expose] public def expandLocalWord (w : List (Fin 4)) : List (Fin 4) :=
  w.flatMap max4Words
public theorem expandLocalWord_value (w : List (Fin 4)) :
    wordValue (expandLocalWord w) = (w.map candidateLetter).prod := by
  induction w with
  | nil => simp only [expandLocalWord, List.flatMap_nil, wordValue, List.map_nil, List.prod_nil]
  | cons i w ih =>
    simp only [expandLocalWord, List.flatMap_cons, wordValue_append, max4Words_value,
      List.map_cons, List.prod_cons]
    exact congrArg (candidateLetter i * ·) ih

/-- Evaluate a word in the exact max4 generators and their inverses. -/
@[expose] public def localValue (w : List (Fin 4)) : Model :=
  (w.map candidateLetter).prod

/-- Evaluate using the four existing, certified max4 point tables. -/
@[expose] public def localMap (w : List (Fin 4)) : Fin 4060 → Fin 4060 :=
  LocalOrder.evalWord LocalOrder.letterMap w

public theorem localValue_smul (w : List (Fin 4)) (x : Fin 4060) :
    localValue w • x = localMap w x :=
  LocalOrder.prod_smul candidateLetter LocalOrder.letterMap LocalOrder.letter_smul w x

private theorem localLetter_inverseLetter (i : Fin 4) :
    candidateLetter (inverseLetter i) = (candidateLetter i)⁻¹ := by
  fin_cases i <;> simp [candidateLetter, inverseLetter]

public theorem localValue_inverseWord (w : List (Fin 4)) :
    localValue (inverseWord w) = (localValue w)⁻¹ := by
  simp only [localValue, inverseWord, List.map_reverse, List.map_map,
    List.prod_inv_reverse, Function.comp_def, localLetter_inverseLetter]

end Rudvalis.SylowOvergroups.TwoCore.Generation.Representatives
