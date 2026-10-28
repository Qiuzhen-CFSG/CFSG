module
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.LocalAnalysisData
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.CharacterOrder.ExceptionalData
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.CharacterOrder.NormalizerInduction.CharacterData
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.CharacterOrder.NormalizerInduction.CharacterConstruction
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.CharacterOrder.NormalizerInduction.Columns
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.CharacterOrder.NormalizerInduction.Action
public import Theory.Character.ScalarProductMultiplicity

/-!
# Special induction from Janko's normalizer character table

The twelve actual normalizer characters are constructed from the local
analysis. The genuine transporter argument makes induction an isometry on
the five special combinations.
Ordinary orthogonality gives their Gram matrix and principal coefficients.
Frobenius reciprocity gives integral multiplicities, and normalized special
class indicators recover all five reciprocity columns.

`specialInductionData_of_normalizerCharacters` retains the conditional
assembly API. `nonempty_specialInductionData` discharges its character-table
input and constructs `SpecialInductionData` from local analysis alone.
No ambient simplicity, order or identification is used here.

Source: Z. Janko, *A characterization of the Mathieu simple groups, I*,
J. Algebra 9 (1968), Section 6, pp.11–12.
-/

open scoped BigOperators
open Subgroup
noncomputable section
attribute [local instance] Fintype.ofFinite
namespace Theory.GroupTheory.HeldM22A10.M22Identification.CharacterOrder
open LocalModelDichotomy
universe u
variable {G : Type u} [Group G] [Finite G]

private theorem irreducible_class {H : Type*} [Group H] {f : ClassFunction H}
    (hf : IsIrreducibleCharacter f) : IsClassFunction f := by
  obtain ⟨n, ρ, _, rfl⟩ := hf
  exact ρ.char_conj

private theorem scalar_sum_left {H J : Type*} [Fintype H] [Fintype J]
    (f : J → ClassFunction H) (g : ClassFunction H) :
    scalarProduct H (∑ j, f j) g = ∑ j, scalarProduct H (f j) g := by
  simp only [scalarProduct, Finset.sum_apply, Finset.sum_mul]
  rw [Finset.sum_comm, Finset.mul_sum]

private theorem scalar_sum_right {H J : Type*} [Fintype H] [Fintype J]
    (f : ClassFunction H) (g : J → ClassFunction H) :
    scalarProduct H f (∑ j, g j) = ∑ j, scalarProduct H f (g j) := by
  simp only [scalarProduct, Finset.sum_apply, star_sum, Finset.mul_sum]
  rw [Finset.sum_comm]

variable (D : LocalData G) (k : TwistedModel ≃* D.centralizer)
    (T : NormalizerCharacterData D k)

private theorem local_orthonormal (r s : Fin 12) :
    scalarProduct (normalizer (CaseII.E D k : Set G)) (T.character r) (T.character s) =
      if r = s then 1 else 0 := by
  have hp : scalarProduct (normalizer (CaseII.E D k : Set G))
      (T.character r) (T.character s) =
        characterProduct (normalizer (CaseII.E D k : Set G)) (T.character r) (T.character s) := by
    obtain ⟨n, ρ, _, hρ⟩ := T.irreducible s
    rw [hρ]
    simp only [scalarProduct, characterProduct,
      Representation.representation_character_inv_eq_star_character]
  rw [hp]
  split
  · next h => subst s; exact irreducibleCharacter_self (T.irreducible r)
  · next h =>
    exact irreducibleCharacters_orthogonal
      (T.irreducible r) (T.irreducible s) (fun he => h (T.injective he))

variable {D k}

omit [Finite G] in
/-- Each local exceptional combination is conjugacy invariant. -/
public theorem NormalizerCharacterData.combination_isClassFunction (i : Fin 5) :
    IsClassFunction (normalizerCombination D k T.character i) := by
  intro x g
  simp only [normalizerCombination, Finset.sum_apply, Pi.smul_apply,
    irreducible_class (T.irreducible _) x g]

/-- The coefficient of a local irreducible is the specified integer. -/
public theorem NormalizerCharacterData.combination_scalar_character (i : Fin 5) (r : Fin 12) :
    scalarProduct (normalizer (CaseII.E D k : Set G))
      (normalizerCombination D k T.character i) (T.character r) =
        (exceptionalCoefficients i r : ℂ) := by
  rw [normalizerCombination, scalar_sum_left]
  simp only [scalarProduct_smul_left, local_orthonormal D k T, mul_ite, mul_one, mul_zero]
  simp

/-- Orthogonality gives the source Gram matrix before induction. -/
public theorem NormalizerCharacterData.combination_gram (i j : Fin 5) :
    scalarProduct (normalizer (CaseII.E D k : Set G))
      (normalizerCombination D k T.character i) (normalizerCombination D k T.character j) =
        (exceptionalGram i j : ℂ) := by
  conv_lhs => arg 3; unfold normalizerCombination
  rw [scalar_sum_right]
  simp only [scalarProduct_smul_right, T.combination_scalar_character, star_intCast,
    ← Int.cast_mul, ← Int.cast_sum, ← exceptionalGram_eq]

/-- Induction preserves all five special values. -/
public theorem NormalizerCharacterData.induced_values (i r : Fin 5) :
    exceptionalInduction D k T.character i (CaseII.into D k (specialRepresentative r)) =
      (exceptionalValues i r : ℂ) := by
  have he := inducedClassFunction_eq_on_specialSupport
    (normalizer (CaseII.E D k : Set G)) (normalizerSpecialSupport D k)
    (normalizerSpecialSupport_transporters D k)
    (normalizerCombination D k T.character i) (T.combination_isClassFunction i) (T.support i)
    (normalizerRepresentative D k r) ⟨r, IsConj.refl _⟩
  exact he.trans (T.combination_values i r)

/-- The induced combinations vanish outside the five ambient special classes. -/
public theorem NormalizerCharacterData.induced_support (i : Fin 5) (g : G)
    (hg : ∀ r, ¬ IsConj g (CaseII.into D k (specialRepresentative r))) :
    exceptionalInduction D k T.character i g = 0 := by
  classical
  unfold exceptionalInduction inducedClassFunction
  apply mul_eq_zero_of_right
  apply Finset.sum_eq_zero
  intro x _
  split
  · next hx =>
    apply T.support i
    rintro ⟨r, hr⟩
    have hr' := (normalizer (CaseII.E D k : Set G)).subtype.map_isConj hr
    apply hg r
    apply IsConj.trans _ hr'
    exact isConj_iff.mpr ⟨x⁻¹, by simp only [inv_inv]; rfl⟩
  · rfl

/-- The identity belongs to none of the five special classes. -/
public theorem NormalizerCharacterData.induced_degree_zero (i : Fin 5) :
    exceptionalInduction D k T.character i 1 = 0 := by
  apply T.induced_support i 1
  intro r hr
  have hr' : CaseII.into D k (specialRepresentative r) = 1 := by
    exact isConj_one_right.mp hr
  have hp : D.z = 1 := by
    calc
      D.z = CaseII.into D k (specialRepresentative r ^ (![1, 3, 4, 2, 2] r : ℕ)) := by
        rw [specialRepresentative_power, CaseII.into_z_zero]
      _ = 1 := by rw [map_pow, hr', one_pow]
  have hz := D.z_order
  rw [hp, orderOf_one] at hz
  omega

/-- Special-set induction preserves the exceptional Gram matrix. -/
public theorem NormalizerCharacterData.induced_gram (i j : Fin 5) :
    scalarProduct G (exceptionalInduction D k T.character i)
      (exceptionalInduction D k T.character j) = (exceptionalGram i j : ℂ) := by
  exact (scalarProduct_inducedClassFunction_of_specialSupport
    (normalizer (CaseII.E D k : Set G)) (normalizerSpecialSupport D k)
    (normalizerSpecialSupport_transporters D k)
    (normalizerCombination D k T.character i) (normalizerCombination D k T.character j)
    (T.combination_isClassFunction j) (T.support i) (T.support j)).trans (T.combination_gram i j)

/-- Frobenius reciprocity gives the principal multiplicities. -/
public theorem NormalizerCharacterData.induced_principal_multiplicity (i : Fin 5) :
    scalarProduct G (exceptionalInduction D k T.character i) 1 =
      (exceptionalCoefficients i 0 : ℂ) := by
  classical
  change scalarProduct G (inducedClassFunction _ (normalizerCombination D k T.character i)) 1 = _
  rw [scalarProduct_inducedClassFunction _ _ (fun _ _ => rfl)]
  have h := T.combination_scalar_character i 0
  rw [T.principal] at h
  convert h using 1
  exact congrArg (fun h : Fintype (normalizer (CaseII.E D k : Set G)) =>
    @scalarProduct _ h (normalizerCombination D k T.character i) 1) (Subsingleton.elim _ _)

/-- Every ambient irreducible has integral exceptional multiplicities, by restriction. -/
public theorem NormalizerCharacterData.induced_multiplicities_integral
    (χ : ClassFunction G) (hχ : IsIrreducibleCharacter χ) :
    ∃ c : Fin 5 → ℤ, ∀ i,
      scalarProduct G (exceptionalInduction D k T.character i) χ = (c i : ℂ) := by
  classical
  let N := normalizer (CaseII.E D k : Set G)
  have hres : IsCharacter (fun x : N => χ (x : G)) := by
    obtain ⟨n, ρ, _, rfl⟩ := hχ
    exact ⟨n, ρ.comp N.subtype, rfl⟩
  have hm (r : Fin 12) : ∃ m : ℕ,
      scalarProduct N (T.character r) (fun x => χ (x : G)) = (m : ℂ) := by
    obtain ⟨n, ρ, _, hρ⟩ := T.irreducible r
    have h := IsCharacter.scalarProduct_nat ⟨n, ρ, hρ⟩ hres
    rw [Subsingleton.elim (Fintype.ofFinite N) (inferInstance : Fintype N)] at h
    exact h
  choose m hm using hm
  refine ⟨fun i => ∑ r, exceptionalCoefficients i r * (m r : ℤ), fun i => ?_⟩
  change scalarProduct G (inducedClassFunction N (normalizerCombination D k T.character i)) χ = _
  rw [scalarProduct_inducedClassFunction _ _ (irreducible_class hχ),
    normalizerCombination, scalar_sum_left]
  simp only [scalarProduct_smul_left, hm, Int.cast_sum, Int.cast_mul, Int.cast_natCast]

/-- Complete induction conclusions, conditional on construction of the actual local characters. -/
public def specialInductionData_of_normalizerCharacters (L : LocalAnalysisData D k) :
    SpecialInductionData D k where
  character := T.character
  irreducible := T.irreducible
  injective := T.injective
  principal := T.principal
  degree_zero := T.induced_degree_zero
  gram := T.induced_gram
  principal_multiplicity := T.induced_principal_multiplicity
  values := T.induced_values
  support := T.induced_support
  columns := by
    intro χ hχ
    obtain ⟨c, hc⟩ := T.induced_multiplicities_integral χ hχ
    exact ⟨c, hc, columns_of_supported_values D k L
      (exceptionalInduction D k T.character) (fun _ => inducedClassFunction_isClassFunction _ _)
      T.induced_values T.induced_support χ (irreducible_class hχ) c hc⟩

/-- Janko's five special inductions, including their Gram matrix, principal
multiplicities, support, values and all five reciprocity columns. The actual
normalizer characters and every induction obligation are constructed from
the given local analysis. -/
public theorem nonempty_specialInductionData (D : LocalData G)
    (k : TwistedModel ≃* D.centralizer) (L : LocalAnalysisData D k) :
    Nonempty (SpecialInductionData D k) := by
  obtain ⟨T⟩ := nonempty_normalizerCharacterData D k L
  exact ⟨specialInductionData_of_normalizerCharacters T L⟩

end Theory.GroupTheory.HeldM22A10.M22Identification.CharacterOrder
