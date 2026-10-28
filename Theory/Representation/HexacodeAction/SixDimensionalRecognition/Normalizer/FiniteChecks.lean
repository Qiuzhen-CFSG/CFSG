module
public import Theory.Representation.HexacodeAction.SixDimensionalRecognition.Normalizer.FiniteData
public import Mathlib.Tactic.FinCases
/-!
# Kernel checks for the even-image normalizer

The 1080 matrices are literal words in the two model generators. Closure under
both generators and their inverses proves coverage, rather than inferring it
from an order. Each order-four member comes with an internal conjugator.
After that normalization, commutation with the first matrix leaves three field
parameters; checking these 64 possibilities finishes the normalizer calculation.

Source: Aschbacher–Smith, K.1.3, printed p.453 (PDF p.464).
-/
@[expose] public section
namespace Representation.Hexacode.SixDimensional.NormalizerData
open EvenImage.PairData
set_option maxRecDepth 4096 in
private theorem block_checks_0 : ∀ b : Fin 9, ∀ k : Fin 40,
    let j : Fin 1080 := ⟨0 + b.val * 40 + k.val, by omega⟩
    word (entryWord j) = entry j ∧ listed (entry j) = true ∧
    (∀ t : Fin 4, mm (letter t) (entry j) = entry (step j t)) ∧
    (fourth (entry j) = ident → mm (entry j) (entry j) ≠ ident →
      mm (entry (conjugating j)) first = mm (entry j) (entry (conjugating j))) := by
  intro b
  fin_cases b <;> decide +kernel

set_option maxRecDepth 4096 in
private theorem block_checks_1 : ∀ b : Fin 9, ∀ k : Fin 40,
    let j : Fin 1080 := ⟨360 + b.val * 40 + k.val, by omega⟩
    word (entryWord j) = entry j ∧ listed (entry j) = true ∧
    (∀ t : Fin 4, mm (letter t) (entry j) = entry (step j t)) ∧
    (fourth (entry j) = ident → mm (entry j) (entry j) ≠ ident →
      mm (entry (conjugating j)) first = mm (entry j) (entry (conjugating j))) := by
  intro b
  fin_cases b <;> decide +kernel

set_option maxRecDepth 4096 in
private theorem block_checks_2 : ∀ b : Fin 9, ∀ k : Fin 40,
    let j : Fin 1080 := ⟨720 + b.val * 40 + k.val, by omega⟩
    word (entryWord j) = entry j ∧ listed (entry j) = true ∧
    (∀ t : Fin 4, mm (letter t) (entry j) = entry (step j t)) ∧
    (fourth (entry j) = ident → mm (entry j) (entry j) ≠ ident →
      mm (entry (conjugating j)) first = mm (entry j) (entry (conjugating j))) := by
  intro b
  fin_cases b <;> decide +kernel

set_option maxRecDepth 4096 in
private theorem block_checks : ∀ b : Fin 27, ∀ k : Fin 40,
    let j : Fin 1080 := ⟨b.val * 40 + k.val, by omega⟩
    word (entryWord j) = entry j ∧ listed (entry j) = true ∧
    (∀ t : Fin 4, mm (letter t) (entry j) = entry (step j t)) ∧
    (fourth (entry j) = ident → mm (entry j) (entry j) ≠ ident →
      mm (entry (conjugating j)) first = mm (entry j) (entry (conjugating j))) := by
  intro b
  fin_cases b
  · exact block_checks_0 0
  · exact block_checks_0 1
  · exact block_checks_0 2
  · exact block_checks_0 3
  · exact block_checks_0 4
  · exact block_checks_0 5
  · exact block_checks_0 6
  · exact block_checks_0 7
  · exact block_checks_0 8
  · exact block_checks_1 0
  · exact block_checks_1 1
  · exact block_checks_1 2
  · exact block_checks_1 3
  · exact block_checks_1 4
  · exact block_checks_1 5
  · exact block_checks_1 6
  · exact block_checks_1 7
  · exact block_checks_1 8
  · exact block_checks_2 0
  · exact block_checks_2 1
  · exact block_checks_2 2
  · exact block_checks_2 3
  · exact block_checks_2 4
  · exact block_checks_2 5
  · exact block_checks_2 6
  · exact block_checks_2 7
  · exact block_checks_2 8

/-- Word witnesses, membership tests, generator transitions and order-four conjugators. -/
theorem entry_checks (j : Fin 1080) :
    word (entryWord j) = entry j ∧ listed (entry j) = true ∧
    (∀ t : Fin 4, mm (letter t) (entry j) = entry (step j t)) ∧
    (fourth (entry j) = ident → mm (entry j) (entry j) ≠ ident →
      mm (entry (conjugating j)) first = mm (entry j) (entry (conjugating j))) := by
  have h := block_checks ⟨j.val / 40, by omega⟩ ⟨j.val % 40, by omega⟩
  have he : (⟨j.val / 40 * 40 + j.val % 40, by omega⟩ : Fin 1080) = j := by
    apply Fin.ext
    dsimp
    omega
  simpa only [he] using h

/-- Invertible centralizing matrices which preserve the second image are model words. -/
theorem central_checks : ∀ g h i : Q,
    let c := central g h i
    fourth c ≠ zero →
    mm c (eleventh c) = ident ∧ mm (eleventh c) c = ident ∧
    (listed (mm (mm c second) (eleventh c)) = true → c = entry (centralWord g h i)) := by
  decide +kernel
end Representation.Hexacode.SixDimensional.NormalizerData
