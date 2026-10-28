module

public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23InFi24Prime.WordSetup
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23InFi24Prime.Comparison.AmbientActions.GeneratorData
public import Mathlib.Tactic.FinCases

/-!
# Word evaluation for the exact Fi₂₃ candidates

`wordMap` evaluates in the left-action order. In inverse mode it reverses
composition and interchanges each letter with its inverse. Induction proves
agreement with `WordSetup.evaluateWord` for any correct letter evaluator.
The five copied lists are identified with the original words by reflexivity.
Iteration then proves the exact powers and conjugation in both candidates.

The specialized packed evaluators still require comparison of their four
letter maps with the original ambient generators. Their numerical action on
the relabeling is a separate finite certificate; neither premise is assumed
by a carrier definition. Source: ATLAS F24G1-p306936B0, GLS3 Table 5.3v,
and the exact words in `WordSetup`.
-/

@[expose] public section
namespace Sporadic.Fischer.Fi24Prime.Fi23Lift.Certificate.Ambient

def inverseLetter (c : Fin 4) : Fin 4 :=
  if c = 0 then 2 else if c = 1 then 3 else if c = 2 then 0 else 1

def letterValue (c : Fin 4) : Carrier :=
  if c = 0 then a else if c = 1 then b else if c = 2 then a⁻¹ else b⁻¹

theorem inverseLetter_value (c : Fin 4) :
    letterValue (inverseLetter c) = (letterValue c)⁻¹ := by
  fin_cases c <;> simp [inverseLetter, letterValue]

def wordMap (f : Fin 4 → Fin 306936 → Fin 306936) (rev : Bool) :
    List (Fin 4) → Fin 306936 → Fin 306936
  | [], x => x
  | c :: cs, x =>
    if rev then wordMap f rev cs (f (inverseLetter c) x)
    else f c (wordMap f rev cs x)

theorem wordMap_correct (f : Fin 4 → Fin 306936 → Fin 306936)
    (hf : ∀ c x, f c x = (letterValue c).val x)
    (letters : List (Fin 4)) (rev : Bool) (x : Fin 306936) :
    wordMap f rev letters x =
      (if rev then (evaluateWord letters)⁻¹ else evaluateWord letters).val x := by
  induction letters generalizing x with
  | nil => cases rev <;> rfl
  | cons c cs ih =>
    cases rev with
    | false =>
      change f c (wordMap f false cs x) =
        (letterValue c * evaluateWord cs).val x
      rw [hf, ih]
      rfl
    | true =>
      change wordMap f true cs (f (inverseLetter c) x) =
        ((letterValue c * evaluateWord cs)⁻¹).val x
      rw [mul_inv_rev, ih, hf, inverseLetter_value]
      rfl


def uLetters : List (Fin 4) :=
  [3, 0, 3, 0, 1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 0, 3, 0, 3, 0, 3, 0, 1,
    0, 3, 2, 1, 2, 1, 2, 1, 2, 3, 2, 3, 2, 3, 2, 3, 2, 3, 2, 3, 2, 3, 2, 1, 2, 3, 2, 3, 2, 1,
    2, 1, 2]

theorem uLetters_spec : evaluateWord uLetters = u := rfl

def vLetters : List (Fin 4) :=
  [0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 0, 1, 0, 3, 0, 1, 0, 1, 0, 1, 0, 1, 0, 3, 0,
    3, 0, 1, 0, 3, 0, 3, 0, 3, 2, 1, 2, 3, 2, 3, 2, 3, 2, 1, 2, 1, 2, 3, 2, 1, 2, 3, 2, 3, 2,
    3, 2, 1, 2, 3, 2, 3, 2, 1, 2, 1, 2, 3, 2, 1, 2, 3, 2]

theorem vLetters_spec : evaluateWord vLetters = v := rfl

def wLetters : List (Fin 4) :=
  [0, 3, 0, 1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 3, 0, 3, 0, 3, 0, 3, 0, 1, 0,
    1, 0, 3, 0, 1, 0, 1, 0, 3, 0, 3, 2, 3, 2, 1, 2, 1, 2, 1, 2, 1, 2, 3, 2, 3, 2, 3, 2, 3, 2,
    3, 2, 1, 2, 1, 2, 3, 2, 3, 2, 1, 2, 1, 2, 3, 2, 1, 2, 3]

theorem wLetters_spec : evaluateWord wLetters = w := rfl

def rLetters : List (Fin 4) :=
  [0, 1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 0, 1, 0,
    1, 0, 1, 0, 1, 0, 1, 0, 3, 2, 3, 2, 1, 2, 1, 2, 3, 2, 1, 2, 3, 2, 3, 2, 1, 2, 1, 2, 1, 2,
    3, 2, 3, 2, 1, 2, 1, 2, 3, 2, 3, 2, 3, 2, 1, 2]

theorem rLetters_spec : evaluateWord rLetters = r := rfl

def sLetters : List (Fin 4) :=
  [1, 0, 1, 0, 1, 0, 3, 0, 3, 0, 1, 0, 1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 3,
    0, 3, 0, 1, 2, 3, 2, 3, 2, 3, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 3, 2, 1, 2, 1, 2, 3, 2, 1,
    2, 1, 2, 3, 2, 1, 2, 3]

theorem sLetters_spec : evaluateWord sLetters = s := rfl

def iterateMap (f : Fin 306936 → Fin 306936) : Nat → Fin 306936 → Fin 306936
  | 0, x => x
  | k + 1, x => f (iterateMap f k x)

theorem iterateMap_correct (f : Fin 306936 → Fin 306936) (g : Carrier)
    (hf : ∀ x, f x = g.val x) (k : Nat) (x : Fin 306936) :
    iterateMap f k x = (g ^ k).val x := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [iterateMap, hf, ih, pow_succ']
    rfl

def candidateAMapWith (f : Fin 4 → Fin 306936 → Fin 306936) : Fin 306936 → Fin 306936 :=
  iterateMap (fun x => wordMap f true wLetters
    (wordMap f false rLetters (wordMap f true vLetters x))) 30

def candidateBMapWith (f : Fin 4 → Fin 306936 → Fin 306936) (x : Fin 306936) : Fin 306936 :=
  wordMap f false uLetters (wordMap f false sLetters (wordMap f false wLetters
    (iterateMap (fun y => wordMap f true uLetters
      (wordMap f false vLetters (wordMap f false vLetters y))) 6
      (wordMap f true wLetters (wordMap f true sLetters (wordMap f true uLetters x))))))

theorem wordMap_forward (f : Fin 4 → Fin 306936 → Fin 306936)
    (hf : ∀ c x, f c x = (letterValue c).val x) (ls : List (Fin 4)) :
    wordMap f false ls = (evaluateWord ls).val :=
  funext (wordMap_correct f hf ls false)

theorem wordMap_inverse (f : Fin 4 → Fin 306936 → Fin 306936)
    (hf : ∀ c x, f c x = (letterValue c).val x) (ls : List (Fin 4)) :
    wordMap f true ls = (evaluateWord ls)⁻¹.val :=
  funext (wordMap_correct f hf ls true)

private theorem triple_apply (g h k : Carrier) (x : Fin 306936) :
    (g * h * k).val x = g.val (h.val (k.val x)) := rfl

private theorem mul_square_apply (g h : Carrier) (x : Fin 306936) :
    (g * h ^ 2).val x = g.val (h.val (h.val x)) := by
  rw [pow_two]
  rfl

private theorem conjugate_triple_apply (g h k q : Carrier) (x : Fin 306936) :
    ((g * h * k) * q * (g * h * k)⁻¹).val x =
      g.val (h.val (k.val (q.val (k⁻¹.val (h⁻¹.val (g⁻¹.val x)))))) := by
  simp only [mul_inv_rev, Subgroup.coe_mul, Equiv.Perm.mul_apply]

theorem candidateAMapWith_correct (f : Fin 4 → Fin 306936 → Fin 306936)
    (hf : ∀ c x, f c x = (letterValue c).val x) (x : Fin 306936) :
    candidateAMapWith f x = candidateA.val x := by
  unfold candidateAMapWith
  rw [wordMap_inverse f hf, wordMap_forward f hf, wordMap_inverse f hf,
    wLetters_spec, rLetters_spec, vLetters_spec]
  exact iterateMap_correct _ (w⁻¹ * r * v⁻¹)
    (fun y => (triple_apply w⁻¹ r v⁻¹ y).symm) 30 x

theorem candidateBMapWith_correct (f : Fin 4 → Fin 306936 → Fin 306936)
    (hf : ∀ c x, f c x = (letterValue c).val x) (x : Fin 306936) :
    candidateBMapWith f x = candidateB.val x := by
  unfold candidateBMapWith
  rw [wordMap_forward f hf, wordMap_forward f hf, wordMap_forward f hf,
    wordMap_inverse f hf, wordMap_forward f hf, wordMap_inverse f hf,
    wordMap_inverse f hf, uLetters_spec, sLetters_spec, wLetters_spec, vLetters_spec]
  rw [iterateMap_correct _ (u⁻¹ * v ^ 2) (fun y => (mul_square_apply u⁻¹ v y).symm)]
  rw [candidateB, conjugate_triple_apply]
/-- Packed evaluation of the literal first candidate. -/
def candidateAMap : Fin 306936 → Fin 306936 := candidateAMapWith letterMap

/-- Packed evaluation of the literal second candidate. -/
def candidateBMap : Fin 306936 → Fin 306936 := candidateBMapWith letterMap

/-- The four generator comparisons supply the signed-letter interpretation. -/
theorem letterMap_correct_of_generators
    (ha : ∀ x, aMap x = generatorA x)
    (hb : ∀ x, bMap x = generatorB x)
    (hai : ∀ x, aInvMap x = generatorA⁻¹ x)
    (hbi : ∀ x, bInvMap x = generatorB⁻¹ x) :
    ∀ c x, letterMap c x = (letterValue c).val x := by
  intro c x
  fin_cases c
  · exact ha x
  · exact hb x
  · exact hai x
  · exact hbi x

/-- The packed first candidate evaluates the actual carrier word once its
signed generators have been identified. -/
theorem candidateAMap_correct
    (hf : ∀ c x, letterMap c x = (letterValue c).val x) (x : Fin 306936) :
    candidateAMap x = candidateA.val x :=
  candidateAMapWith_correct letterMap hf x

/-- The packed second candidate preserves the exact conjugation and sixth power. -/
theorem candidateBMap_correct
    (hf : ∀ c x, letterMap c x = (letterValue c).val x) (x : Fin 306936) :
    candidateBMap x = candidateB.val x :=
  candidateBMapWith_correct letterMap hf x

end Sporadic.Fischer.Fi24Prime.Fi23Lift.Certificate.Ambient
