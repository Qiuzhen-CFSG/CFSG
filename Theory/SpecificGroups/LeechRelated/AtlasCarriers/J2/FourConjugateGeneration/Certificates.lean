module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.FourConjugateGeneration.Data
import Mathlib.Tactic.FinCases

/-!
# Checked four-conjugate word identities for the Hall--Janko group

Scalar checks establish each conjugation identity on all one hundred points
and then express both defining generators as words in the four conjugates.
The bridges below identify these scalar computations with multiplication in
the actual permutation extension. No group-order oracle is used.
Source: retained ATLAS J2G1-p100B0; Guralnick--Malle, Classification of
2F-modules I, (2.5)--(2.6), Proposition 5.1 (J₂ paragraph). The outer row
supplies the additional uniform extension bound required by the application.
-/

public section
namespace Sporadic.LeechRelated.J2.FourConjugateGeneration
open Theory.GroupTheory GeneratorPair GeneratorPair.FirstFusion ExceptionalParabolics Data

/-- The three exhaustive involution representatives in the permutation extension. -/
@[expose] def representative : Fin 3 → Extension :=
  ![intoExtension a, intoExtension t, extensionInvolution]

/-- All certificate conjugators are words in the inner carrier. -/
def conjugator (j : Fin 3) (i : Fin 4) : Carrier :=
  evalWord letter (conjugatorWord j i)

/-- The four certified conjugates for each representative. -/
@[expose] def conjugate (j : Fin 3) (i : Fin 4) : Extension :=
  intoExtension (conjugator j i) * representative j * (intoExtension (conjugator j i))⁻¹

set_option maxRecDepth 20000 in
private theorem alphabet_eq : ∀ (j : Fin 3) (p : Fin 100),
    alphabet j p = permLetter j p := by decide +kernel

private theorem wordValue_eq {H : Type*} [Group H] {n : Nat}
    (f : H →* Equiv.Perm (Fin 100)) (gen : Fin n → H)
    (v : Fin n → Fin 100 → Fin 100)
    (hv : ∀ j p, v j p = f (gen j) p) (w : List (Fin n)) (p : Fin 100) :
    wordValue v w p = f (evalWord gen w) p := by
  induction w with
  | nil => simp only [wordValue, evalWord, map_one, Equiv.Perm.one_apply]
  | cons j w ih =>
    rw [wordValue, ih, hv, evalWord, map_mul, Equiv.Perm.mul_apply]

private theorem conjugator_value (j : Fin 3) (i : Fin 4) (p : Fin 100) :
    wordValue alphabet (conjugatorWord j i) p = inclusion (conjugator j i) p :=
  wordValue_eq inclusion letter alphabet
    (fun j p => (alphabet_eq j p).trans (congrArg (fun q => q p) (inclusion_letter j).symm)) _ _

set_option maxRecDepth 20000 in
private theorem representativeValue_eq (j : Fin 3) (p : Fin 100) :
    representativeValue j p = extension.subtype (representative j) p := by
  have h : ∀ (j : Fin 3) (p : Fin 100),
      representativeValue j p = (![tableA, tPerm, involution] j) p := by decide +kernel
  rw [h]
  fin_cases j
  · exact congrArg (fun q => q p) generatorA_eq_table.symm
  · exact congrArg (fun q => q p) inclusion_t.symm
  · rfl

set_option maxRecDepth 20000 in
private theorem conjugates_checked : ∀ (j : Fin 3) (i : Fin 4) (p : Fin 100),
    wordValue alphabet (conjugatorWord j i) (representativeValue j p) =
      conjugateValue j i (wordValue alphabet (conjugatorWord j i) p) := by
  decide +kernel

private theorem conjugate_value (j : Fin 3) (i : Fin 4) (p : Fin 100) :
    conjugateValue j i p = extension.subtype (conjugate j i) p := by
  obtain ⟨q, rfl⟩ := (inclusion (conjugator j i)).surjective p
  change _ = inclusion (conjugator j i)
    (extension.subtype (representative j)
      ((inclusion (conjugator j i))⁻¹ (inclusion (conjugator j i) q)))
  rw [Equiv.Perm.inv_def, Equiv.symm_apply_apply]
  have h := conjugates_checked j i q
  rw [conjugator_value, conjugator_value, representativeValue_eq] at h
  exact h.symm

set_option maxRecDepth 20000 in
private theorem generators_checked : ∀ (j : Fin 3) (k : Fin 2) (p : Fin 100),
    wordValue (conjugateValue j) (generatorWord j k) p =
      alphabet (Fin.castLE (by decide) k) p := by decide +kernel

/-- Checked words express both defining generators in every four-conjugate subgroup. -/
theorem generator_word (j : Fin 3) (k : Fin 2) :
    evalWord (conjugate j) (generatorWord j k) = intoExtension (![a, b] k) := by
  apply extension.subtype_injective
  apply Equiv.ext
  intro p
  rw [← wordValue_eq extension.subtype (conjugate j) (conjugateValue j)
    (conjugate_value j), generators_checked, alphabet_eq]
  fin_cases k
  · exact congrArg (fun q => q p) generatorA_eq_table.symm
  · exact congrArg (fun q => q p) generatorB_eq_table.symm

end Sporadic.LeechRelated.J2.FourConjugateGeneration
