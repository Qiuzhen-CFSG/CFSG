module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.CharacterOrder.NormalizerInduction.CharacterConstruction.InertiaSubgroup
public import Theory.Character.SymmetricFour
public import Theory.Character.SurjectiveInflation
public import Theory.Character.LinearTwist
public import Theory.Character.NilpotentBrauerIdeal
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.CharacterOrder.NormalizerInduction.CharacterConstruction.Blocks
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.CharacterOrder.NormalizerInduction.CharacterConstruction.Quotient
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.CharacterOrder.NormalizerInduction.Action
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.CharacterOrder.NormalizerInduction.CharacterConstruction.ClassConstruction.FixedClasses

/-!
# Actual characters induced from the marked inertia subgroup

Inflate each of the five constructed S4 characters through the literal inertia
projection and twist by the extension of the nonprincipal E-character. These
are actual irreducible characters of the inertia subgroup, with the original
vector and actor marking. Induction gives actual normalizer characters with
degrees 45,45,30,15,15. The three classes outside the marked centralizer give
zero values by the induction formula and internal class separation.

Irreducibility after induction and the remaining marked values are separate
obligations. This construction does not yet assert the induced character block.
In particular it uses no claimed placement of the marked actors in the arbitrary
A6 complement supplied by local analysis.

Source: Z. Janko, *A characterization of the Mathieu simple groups, I*,
J. Algebra 9 (1968), Section 6, pp.10–11. This uses inertia induction to construct
the five characters whose degrees the source obtains by orthogonality.
-/

open Subgroup
open scoped BigOperators
noncomputable section
attribute [local instance] Fintype.ofFinite
namespace Theory.GroupTheory.HeldM22A10.M22Identification.CharacterOrder
open LocalModelDichotomy
universe u
variable {G : Type u} [Group G] [Finite G] (D : LocalData G)
    (k : TwistedModel ≃* D.centralizer) (L : LocalAnalysisData D k)
/-- S4 labels in the source order: standard, sign-standard, degree two, sign, trivial. -/
@[expose] public def normalizerInertiaCharacterIndex : Fin 5 → Fin 5 := ![3, 4, 2, 1, 0]
/-- The actual irreducible inertia character, extended and twisted with the given marking. -/
@[expose] public def normalizerInertiaCharacter (j : Fin 5) : ClassFunction (normalizerInertia D k) := fun x =>
  normalizerInertiaExtension D k L x *
    SymmetricFourCharacters.character (normalizerInertiaCharacterIndex j)
      (ConjClasses.mk (normalizerInertiaProjection D k L x))
private theorem fromConj {H : Type*} [Group H] [Finite H]
    {χ : ConjClassFunction H} (hχ : IsIrreducibleConjCharacter χ) :
    IsIrreducibleCharacter (ofConjClassFunction χ) := by
  obtain ⟨n, ρ, hρ⟩ := hχ.1
  refine ⟨n, ρ, (irreducible_iff_character_norm_one ρ).mpr ?_, ?_⟩
  · simpa [hρ] using hχ.2
  · rw [hρ]
    rfl
/-- Surjective inflation and a linear twist preserve irreducibility in the inertia subgroup. -/
public theorem normalizerInertiaCharacter_irreducible (j : Fin 5) : IsIrreducibleCharacter (normalizerInertiaCharacter D k L j) := by
  have hi := (fromConj (SymmetricFourCharacters.character_irreducible (normalizerInertiaCharacterIndex j))).comp_surjective
    (normalizerInertiaProjection D k L) (normalizerInertiaProjection_surjective D k L)
  obtain ⟨n, ρ, hirr, he⟩ := hi
  have ht := (isIrreducibleCharacter_characterClassFunction ρ hirr).linearTwist
    (normalizerInertiaExtension D k L)
  convert fromConj ht using 1
  funext x
  exact congrArg (fun z : ℂ => normalizerInertiaExtension D k L x * z) (congrFun he x)

/-- Evaluation retains the original binary coordinate and S4 actor. -/
public theorem normalizerInertiaCharacter_apply (j : Fin 5) (x : TwistedModel) :
    normalizerInertiaCharacter D k L j (normalizerInertiaEquiv D k L x) =
      binaryParityCharacter x.left *
        (SymmetricFourCharacters.table (normalizerInertiaCharacterIndex j)
          (SymmetricFourClasses.classIndex x.right) : ℂ) := by
  rw [normalizerInertiaCharacter, normalizerInertiaExtension_apply,
    normalizerInertiaProjection_apply, SymmetricFourCharacters.character_apply]

/-- The five normalizer characters are ordinary induction of the constructed inertia characters. -/
@[expose] public def normalizerInducedCharacter (j : Fin 5) :
    ClassFunction (normalizer (CaseII.E D k : Set G)) :=
  inducedClassFunction (normalizerInertia D k) (normalizerInertiaCharacter D k L j)

/-- Every constructed induced function is afforded by an actual complex representation. -/
public theorem normalizerInducedCharacter_isCharacter (j : Fin 5) :
    IsCharacter (normalizerInducedCharacter D k L j) := by
  obtain ⟨n, ρ, _, he⟩ := normalizerInertiaCharacter_irreducible D k L j
  exact BrauerInduction.inducedClassFunction_isCharacter _ ⟨n, ρ, he⟩

/-- Conjugacy invariance uses conjugation internal to the actual normalizer. -/
public theorem normalizerInducedCharacter_isClassFunction (j : Fin 5) :
    IsClassFunction (normalizerInducedCharacter D k L j) :=
  inducedClassFunction_isClassFunction _ _

private theorem normalizerInertiaCharacter_one (j : Fin 5) :
    normalizerInertiaCharacter D k L j 1 = (![3, 3, 2, 1, 1] j : ℂ) := by
  rw [normalizerInertiaCharacter, map_one, map_one, one_mul,
    SymmetricFourCharacters.character_apply]
  have h : ∀ j : Fin 5, SymmetricFourCharacters.table (normalizerInertiaCharacterIndex j)
      (SymmetricFourClasses.classIndex 1) = (![3, 3, 2, 1, 1] j : ℤ) := by decide +kernel
  rw [h]
  fin_cases j <;> norm_num

/-- The degrees of the actual induced characters in Janko's row order. -/
public theorem normalizerInducedCharacter_one (j : Fin 5) :
    normalizerInducedCharacter D k L j 1 = (![45, 45, 30, 15, 15] j : ℂ) := by
  unfold normalizerInducedCharacter inducedClassFunction
  simp only [mul_one, inv_mul_cancel, Subgroup.one_mem, dite_true]
  change (Nat.card (normalizerInertia D k) : ℂ)⁻¹ *
    (∑ _x : normalizer (CaseII.E D k : Set G), normalizerInertiaCharacter D k L j 1) = _
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    ← Nat.card_eq_fintype_card, normalizerInertia_card D k L, normalizer_E_card D k L,
    normalizerInertiaCharacter_one]
  fin_cases j <;> norm_num

include L in
/-- None of the three remaining class representatives has a conjugate in the inertia subgroup. -/
public theorem normalizerInertia_no_free_conjugate (Q : NormalizerClassData D k)
    (r : Fin 3) (x : normalizer (CaseII.E D k : Set G)) :
    x⁻¹ * Q.representative (normalizerFreeIndex r) * x ∉ normalizerInertia D k := by
  intro hx
  rw [normalizerInertia_eq_range D k L] at hx
  obtain ⟨t, ht⟩ := hx
  obtain ⟨i, hi⟩ := normalizerCentralizer_fixedRepresentative_covers D k L t
  have hconj : IsConj (Q.representative (normalizerFreeIndex r))
      (normalizerFixedRepresentative D k i) :=
    (isConj_iff.mpr ⟨x⁻¹, by simpa only [inv_inv] using ht.symm⟩).trans hi
  have hrep : normalizerFixedRepresentative D k i =
      Q.representative (normalizerFixedIndex i) :=
    (normalizerFullRepresentative_fixed D k Q.otherThree Q.five i).symm
  rw [hrep] at hconj
  have he := Q.distinct (ConjClasses.mk_eq_mk_iff_isConj.mpr hconj)
  have hne : ∀ (r : Fin 3) (i : Fin 9), normalizerFreeIndex r ≠ normalizerFixedIndex i := by
    decide +kernel
  exact hne r i he

/-- The three columns c₁, μ, μ² vanish for every constructed induced character. -/
public theorem normalizerInducedCharacter_free (Q : NormalizerClassData D k)
    (j : Fin 5) (r : Fin 3) :
    normalizerInducedCharacter D k L j (Q.representative (normalizerFreeIndex r)) = 0 :=
  inducedClassFunction_supportedOn _ _ _ (normalizerInertia_no_free_conjugate D k L Q r)

/-- These are exactly the prescribed zero columns of the published numerical table. -/
public theorem normalizerInducedCharacter_free_values (Q : NormalizerClassData D k)
    (j : Fin 5) (r : Fin 3) :
    normalizerInducedCharacter D k L j (Q.representative (normalizerFreeIndex r)) =
      normalizerFullValues 0 (Fin.natAdd 7 j) (normalizerFreeIndex r) := by
  rw [normalizerInducedCharacter_free]
  fin_cases j <;> fin_cases r <;>
    simp [normalizerFreeIndex, normalizerFullValues, normalizerNonspecialValues,
      normalizerIntegralValues, normalizerFiveValues, Fin.append, Fin.addCases]

/-- The identity column also agrees with the published table. -/
public theorem normalizerInducedCharacter_identity_values (Q : NormalizerClassData D k)
    (j : Fin 5) :
    normalizerInducedCharacter D k L j (Q.representative 5) =
      normalizerFullValues 0 (Fin.natAdd 7 j) 5 := by
  change normalizerInducedCharacter D k L j 1 = _
  rw [normalizerInducedCharacter_one]
  change (![45, 45, 30, 15, 15] j : ℂ) =
    (normalizerIntegralValues (Fin.natAdd 7 j) 0 : ℂ)
  have h : ∀ j : Fin 5, normalizerIntegralValues (Fin.natAdd 7 j) 0 =
      (![45, 45, 30, 15, 15] j : ℤ) := by decide +kernel
  rw [h]
  fin_cases j <;> norm_num

end Theory.GroupTheory.HeldM22A10.M22Identification.CharacterOrder
