module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.LocalAnalysisData
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.CharacterOrder.ExceptionalData
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.CharacterOrder.NormalizerInduction.Transporters

/-!
# The local character-table input for normalizer induction

This records only the part of the actual normalizer character table consumed
by the five special inductions: twelve distinct irreducible characters, their
five special columns, and cancellation of the five prescribed combinations
on the remaining classes. Its existence is a representation-theoretic proof
obligation. It includes no assertions about induction to the ambient group.

The numerical columns were checked against the page image of Janko's table.
Their multiplication by the five fixed coefficient vectors gives the required
special values, by kernel evaluation. A table of numbers alone does not
construct an inhabitant of `NormalizerCharacterData`.

Source: Z. Janko, *A characterization of the Mathieu simple groups, I*,
J. Algebra 9 (1968), Section 6, pp.11–12.
-/

open scoped BigOperators
open Subgroup
noncomputable section
attribute [local instance] Fintype.ofFinite

namespace Theory.GroupTheory.HeldM22A10.M22Identification.CharacterOrder
open LocalModelDichotomy

/-- The twelve irreducible rows on z₁, cz₁, z₂bd, z₄a, z₂d. -/
@[expose] public def normalizerCharacterValues : Fin 12 → Fin 5 → ℤ :=
  ![![1, 1, 1, 1, 1], ![9, 0, 1, 1, 1], ![10, 1, 0, -2, -2],
    ![8, -1, 0, 0, 0], ![8, -1, 0, 0, 0], ![5, 2, -1, 1, 1],
    ![5, -1, -1, 1, 1], ![-3, 0, 1, -3, 1], ![-3, 0, -1, 1, 1],
    ![-2, 1, 0, 2, -2], ![-1, -1, 1, 3, -1], ![-1, -1, -1, -1, -1]]

/-- The five fixed combinations of the special columns. -/
public theorem exceptionalCoefficients_mul_normalizerValues : ∀ i r,
    (∑ j : Fin 12, exceptionalCoefficients i j * normalizerCharacterValues j r) =
      exceptionalValues i r := by
  decide +kernel

variable {G : Type*} [Group G] (D : LocalData G)
    (k : TwistedModel ≃* D.centralizer)

/-- The actual local combinations before induction. -/
@[expose] public def normalizerCombination
    (χ : Fin 12 → ClassFunction (normalizer (CaseII.E D k : Set G)))
    (i : Fin 5) : ClassFunction (normalizer (CaseII.E D k : Set G)) :=
  ∑ r : Fin 12, (exceptionalCoefficients i r : ℂ) • χ r

/-- The precise local table facts still needed for the construction. In
particular `support` must be proved in the actual N(E), using its actual
action and class structure. It is not a claim about ambient induction. -/
public structure NormalizerCharacterData where
  character : Fin 12 → ClassFunction (normalizer (CaseII.E D k : Set G))
  irreducible : ∀ r, IsIrreducibleCharacter (character r)
  injective : Function.Injective character
  principal : character 0 = 1
  values : ∀ j r, character j (normalizerRepresentative D k r) =
    (normalizerCharacterValues j r : ℂ)
  support : ∀ i, supportedOn (normalizerCombination D k character i)
    (normalizerSpecialSupport D k)

variable {D k}

/-- The local table gives the five exceptional values before induction. -/
public theorem NormalizerCharacterData.combination_values
    (T : NormalizerCharacterData D k) (i r : Fin 5) :
    normalizerCombination D k T.character i (normalizerRepresentative D k r) =
      (exceptionalValues i r : ℂ) := by
  simp only [normalizerCombination, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    T.values, ← Int.cast_mul, ← Int.cast_sum, exceptionalCoefficients_mul_normalizerValues]

end Theory.GroupTheory.HeldM22A10.M22Identification.CharacterOrder
