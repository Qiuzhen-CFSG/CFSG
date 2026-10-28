module

public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.Subgroup

/-!
# A valid coset-certificate context in the original presentation

Two auxiliary letters denote the fixed subgroup words. The context contains
the six original relators and the two defining equations for these letters.
Every equation is proved in `Presentation.Presented`; no permutation quotient
or finiteness assumption enters the context.

An acyclic representative tree and checked signed transitions for the original
letters give the precise 364-coset cover used by `PresentationBound`.
Source: the ATLAS presentation and max3 words documented in `Subgroup`.
-/

@[expose] public section

namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound

open Subgroup.CosetWordCertificate

namespace Certificate

abbrev Alphabet := Bool ⊕ Bool

def generators : Alphabet → Presentation.Presented
  | .inl s => Presentation.generator s
  | .inr s => boundGenerator s

def original (w : Word Bool) : Word Alphabet := w.map fun a => (.inl a.1, a.2)

theorem eval_original (w : Word Bool) :
    eval generators (original w) = eval Presentation.generator w := by
  induction w with
  | nil => simp [original]
  | cons a w ih =>
    simp only [original, List.map_cons, eval_cons] at *
    rw [ih]
    rfl

/-- Six source words, two defining words, and harmless empty words thereafter. -/
def relators (r : Nat) : Word Alphabet :=
  if h : r < 6 then original (relatorLetters ⟨r, h⟩) else
  if r = 6 then original (boundLetters false) ++ [(.inr false, false)] else
  if r = 7 then original (boundLetters true) ++ [(.inr true, false)] else []

theorem relators_ok (r : Nat) : eval generators (relators r) = 1 := by
  unfold relators
  split
  · rw [eval_original, relatorLetters_eq_one]
  · split
    · rw [eval_append, eval_original, eval_boundLetters, eval_letter]
      exact mul_inv_cancel (boundGenerator false)
    · split
      · rw [eval_append, eval_original, eval_boundLetters, eval_letter]
        exact mul_inv_cancel (boundGenerator true)
      · exact eval_nil _

def allowed (a : Letter Alphabet) : Bool :=
  match a with
  | (.inr _, true) => true
  | _ => false

theorem allowed_ok (a : Letter Alphabet) (h : allowed a = true) :
    eval generators [a] ∈ boundSubgroup := by
  rcases a with ⟨s, sign⟩
  cases s with
  | inl s => cases sign <;> simp [allowed] at h
  | inr s =>
    cases sign
    · simp [allowed] at h
    · simpa [generators] using boundGenerator_mem s

def context (D : Definitions Alphabet) : Context Alphabet :=
  ⟨D.parent, D.letter, relators, allowed⟩

/-- All source and subgroup premises of the general checker are discharged. -/
theorem valid (D : Definitions Alphabet) :
    Valid (context D) boundSubgroup generators (D.repr generators) :=
  D.valid relators allowed allowed_ok relators_ok

/-- Only original signed letters need output transitions. -/
def coverOfOriginalTransitions (D : Definitions Alphabet)
    (index : Fin 364 → Nat) (initial : Fin 364) (hzero : index initial = 0)
    (dest : Fin 364 → Letter Bool → Fin 364)
    (transitions : ∀ i a, Holds boundSubgroup generators (D.repr generators)
      ⟨index i, [(.inl a.1, a.2)], index (dest i a)⟩) :
    Subgroup.GeneratorCosetCover boundSubgroup Presentation.generator (Fin 364) where
  repr i := D.repr generators (index i)
  initial := initial
  initial_eq := by rw [hzero, D.repr_zero]
  step i s := by
    obtain ⟨h, he⟩ := transitions i (s, true)
    exact ⟨h, dest i (s, true), by simpa [generators] using he⟩
  inv_step i s := by
    obtain ⟨h, he⟩ := transitions i (s, false)
    exact ⟨h, dest i (s, false), by simpa [generators] using he⟩

end Certificate

end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound
