module

public import Theory.SpecificGroups.ONan.ProjectiveOrder.CosetIndex.UpperBound.WordModel
public import Theory.SpecificGroups.ONan.ProjectiveOrder.CosetIndex.UpperBound.Positive

/-!
# Matrix certificates for the O'Nan coset cover

The numerical input consists of representative words, positive transition
endpoints, local factor words, and nonzero scalars. Only full linear matrix
identities validate the transitions. The word-model lemmas project these
identities to the actual O'Nan model, and finiteness supplies inverse steps.
An orbit table can suggest these data but cannot discharge the identities.

The fixed matrices and local words are the ATLAS data attributed in
`refs/original/onan/` and `ProjectiveOrder/source/`.
-/

namespace ONan.OrderCertificate.UpperBound

open Subgroup.CosetWordCertificate

/-- Untrusted data for a cover; no group equality is assumed by this type. -/
public structure MatrixCosetData where
  representative : Fin 122760 → Word (Fin 4)
  initial : Fin 122760
  destination : Fin 122760 → Bool → Fin 122760
  factor : Fin 122760 → Bool → Word (Fin 4)
  scalar : Fin 122760 → Bool → (ZMod 7)ˣ

/-- Embed either ambient generator in the four-letter alphabet. -/
@[expose] public def ambientLetter : Bool → Fin 4
  | false => 0
  | true => 1

/-- The exact obligations on a numerical matrix certificate. -/
public structure MatrixCosetData.Valid (C : MatrixCosetData) : Prop where
  root : C.representative C.initial = []
  localFactor : ∀ i a b, b ∈ C.factor i a → allowed b = true
  transition : ∀ i a,
    (eval linearGenerators (C.representative i) * linearGenerators (ambientLetter a)) *
        Matrix.GeneralLinearGroup.scalar (Fin 45) (C.scalar i a) =
      eval linearGenerators (C.factor i a) *
        eval linearGenerators (C.representative (C.destination i a))

/-- Full matrix identities yield all signed transitions in the projective model. -/
public def MatrixCosetData.cover (C : MatrixCosetData) (hC : C.Valid) :
    Subgroup.GeneratorCosetCover localSubgroup cosetGenerators (Fin 122760) := by
  apply coverOfPositive (fun i => eval generators (C.representative i)) C.initial
  · rw [hC.root, eval_nil]
  · intro i a
    obtain ⟨h, hh⟩ := step_of_scalar (C.representative i)
      (C.representative (C.destination i a)) (C.factor i a) (ambientLetter a)
      (hC.localFactor i a) (C.scalar i a) (hC.transition i a)
    refine ⟨h, C.destination i a, ?_⟩
    cases a <;> exact hh

end ONan.OrderCertificate.UpperBound
