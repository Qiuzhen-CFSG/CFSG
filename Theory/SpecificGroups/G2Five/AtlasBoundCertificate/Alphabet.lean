module

public import Theory.SpecificGroups.G2Five.AtlasBoundSubgroup
public import Theory.GroupTheory.CosetWordCertificate

/-!
# A sound auxiliary alphabet for the fixed ATLAS subgroup

The left copy of `Bool` names the original presentation generators; the right
copy names the two literal subgroup words. The relations consist of the original
22 words followed by two defining equations for the added letters. They all hold
in the original `Model`, so an enumeration on this alphabet does not change the
presented group or assume that its permutation image is faithful.

An acyclic representative tree therefore gives a valid coset-word certificate
context. Checked signed transitions for the original letters alone suffice for
the requested cover; the auxiliary letters provide single-letter subgroup loops.

Source: the literal data in `AtlasPresentation` and `AtlasBoundSubgroup`;
certificate semantics from `Theory.GroupTheory.CosetWordCertificate`.
-/

@[expose] public section

open Subgroup.CosetWordCertificate
namespace G2Five.AtlasPresentation.BoundCertificate
/-- Original letters on the left, fixed subgroup words on the right. -/
abbrev Alphabet := Bool ⊕ Bool

/-- Evaluation takes place in the unchanged 22-relator presentation. -/
def generators : Alphabet → Model
  | .inl b => generator b
  | .inr b => boundGenerator b

def original (w : Word Bool) : Word Alphabet := w.map fun a => (.inl a.1, a.2)

theorem eval_original (w : Word Bool) : eval generators (original w) = eval generator w := by
  induction w with
  | nil => simp [original]
  | cons a w ih =>
    simp only [original, List.map_cons, eval_cons] at *
    rw [ih]
    rfl

/-- The retained relators, then the two word-defining equations, then empty words. -/
def relators (r : Nat) : Word Alphabet :=
  if h : r < 22 then original (boundLetters (word ⟨r,h⟩)) else
  if r = 22 then original (boundLetters (boundWord false)) ++ [(.inr false, false)] else
  if r = 23 then original (boundLetters (boundWord true)) ++ [(.inr true, false)] else []

theorem relators_ok (r : Nat) : eval generators (relators r) = 1 := by
  unfold relators
  split
  · rw [eval_original]
    exact boundLetters_relator_eq_one _
  · split
    · rw [eval_append, eval_original, eval_letter]
      exact mul_inv_cancel (boundGenerator false)
    · split
      · rw [eval_append, eval_original, eval_letter]
        exact mul_inv_cancel (boundGenerator true)
      · exact eval_nil _

def allowed (a : Letter Alphabet) : Bool :=
  match a with
  | (.inr _, true) => true
  | _ => false

theorem allowed_ok (a : Letter Alphabet) (h : allowed a = true) :
    eval generators [a] ∈ boundSubgroup := by
  rcases a with ⟨b,s⟩
  cases b with
  | inl b => cases s <;> simp [allowed] at h
  | inr b =>
    cases s
    · simp [allowed] at h
    · simpa [generators] using boundGenerator_mem b

def context (D : Definitions Alphabet) : Context Alphabet :=
  ⟨D.parent, D.letter, relators, allowed⟩

theorem valid (D : Definitions Alphabet) :
    Valid (context D) boundSubgroup generators (D.repr generators) :=
  D.valid relators allowed allowed_ok relators_ok

/-- Forget auxiliary transitions after a complete enumeration. -/
def restrictCover {ι : Type*}
    (C : Subgroup.GeneratorCosetCover boundSubgroup generators ι) :
    Subgroup.GeneratorCosetCover boundSubgroup generator ι where
  repr := C.repr
  initial := C.initial
  initial_eq := C.initial_eq
  step i b := C.step i (.inl b)
  inv_step i b := C.inv_step i (.inl b)

/-- Only signed original-letter transitions are required by final assembly. -/
def coverOfOriginalTransitions (D : Definitions Alphabet)
    (index : Fin 3906 → Nat) (initial : Fin 3906) (hzero : index initial = 0)
    (dest : Fin 3906 → Letter Bool → Fin 3906)
    (transitions : ∀ i a, Holds boundSubgroup generators (D.repr generators)
      ⟨index i, [(.inl a.1, a.2)], index (dest i a)⟩) :
    Subgroup.GeneratorCosetCover boundSubgroup generator (Fin 3906) where
  repr i := D.repr generators (index i)
  initial := initial
  initial_eq := by rw [hzero, D.repr_zero]
  step i b := by
    obtain ⟨h, he⟩ := transitions i (b, true)
    exact ⟨h, dest i (b, true), by simpa [generators] using he⟩
  inv_step i b := by
    obtain ⟨h, he⟩ := transitions i (b, false)
    exact ⟨h, dest i (b, false), by simpa [generators] using he⟩

end G2Five.AtlasPresentation.BoundCertificate

namespace G2Five.AtlasPresentation

/-- The finite transition interface that final certificate checking must produce.
Every transition is an equation modulo `boundSubgroup` in `Model`. -/
structure BoundCosetTransitions where
  definitions : Definitions BoundCertificate.Alphabet
  index : Fin 3906 → Nat
  initial : Fin 3906
  initial_zero : index initial = 0
  dest : Fin 3906 → Letter Bool → Fin 3906
  transitions : ∀ i a,
    Holds boundSubgroup BoundCertificate.generators
      (definitions.repr BoundCertificate.generators)
      ⟨index i, [(.inl a.1, a.2)], index (dest i a)⟩

end G2Five.AtlasPresentation
