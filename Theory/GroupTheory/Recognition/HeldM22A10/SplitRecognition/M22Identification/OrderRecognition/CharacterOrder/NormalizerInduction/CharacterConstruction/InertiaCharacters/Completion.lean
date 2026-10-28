module
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.CharacterOrder.NormalizerInduction.CharacterConstruction.InertiaCharacters.ClassSums
public import Theory.Character.InnerProductByClasses
public import Theory.Character.Multiplicity

/-!
# From internal fusion and centralizer orders to the induced character block

The class-intersection formula calculates every entry of the five actual
induced characters. The three remaining classes have zero values. Summing the
squares of these entries with reciprocal centralizer weights gives norm one,
so each already constructed representation character is irreducible.

The only extra premises below are group-theoretic: the exact internal fusion
of seventeen marked local classes and nine centralizer orders. Their producers
must discharge these premises before this gives the unconditional induced
block required in Janko's normalizer table.

Source: Z. Janko, *A characterization of the Mathieu simple groups, I*,
J. Algebra 9 (1968), Section 6, pp.10–11.
-/
open Subgroup
open scoped BigOperators
noncomputable section
attribute [local instance] Fintype.ofFinite
namespace Theory.GroupTheory.HeldM22A10.M22Identification.CharacterOrder
open LocalModelDichotomy CaseII.Distribution
universe u
variable {G : Type u} [Group G] [Finite G] (D : LocalData G)
    (k : TwistedModel ≃* D.centralizer) (L : LocalAnalysisData D k)
    (Q : NormalizerClassData D k)

private theorem sum_partition (f : Fin 12 → ℂ) :
    ∑ r, f r = (∑ i : Fin 9, f (normalizerFixedIndex i)) +
      ∑ i : Fin 3, f (normalizerFreeIndex i) := by
  simp [Fin.sum_univ_succ, normalizerFixedIndex, normalizerFreeIndex]
  ring

include Q in
private theorem induced_norm (j : Fin 5)
    (hc : ∀ i : Fin 9, Nat.card (centralizer ({normalizerFixedRepresentative D k i} :
      Set (normalizer (CaseII.E D k : Set G)))) = normalizerFixedCentralizerOrders i) :
    scalarProduct _ (normalizerInducedCharacter D k L j) (normalizerInducedCharacter D k L j) =
      ∑ i : Fin 9,
        normalizerInducedCharacter D k L j (normalizerFixedRepresentative D k i) *
          star (normalizerInducedCharacter D k L j (normalizerFixedRepresentative D k i)) /
            (normalizerFixedCentralizerOrders i : ℂ) := by
  let χ := toConjClassFunction (normalizerInducedCharacter D k L j)
    (normalizerInducedCharacter_isClassFunction D k L j)
  change classFunctionInner χ χ = _
  have hrep : Function.Bijective (fun i => ConjClasses.mk (Q.representative i)) := by
    refine ⟨Q.distinct, ?_⟩
    intro c
    obtain ⟨x, rfl⟩ := ConjClasses.exists_rep c
    obtain ⟨i, hi⟩ := Q.covers x
    exact ⟨i, ConjClasses.mk_eq_mk_iff_isConj.mpr hi.symm⟩
  rw [classFunctionInner_eq_sum_div_centralizer Q.representative hrep, sum_partition]
  simp only [χ, toConjClassFunction_apply, normalizerInducedCharacter_free D k L Q,
    zero_mul, zero_div, Finset.sum_const_zero, add_zero]
  apply Finset.sum_congr rfl
  intro i _
  rw [NormalizerClassData.representative, normalizerFullRepresentative_fixed, hc]

include Q in
/-- The complete norm calculation, including the impossible alternative fusion assignment. -/
public theorem normalizerInducedCharacter_norm_of_fusion_centralizers
    (swap : Bool)
    (hf : ∀ i : Fin 17, IsConj (normalizerCentralizer D k (localRepresentative i))
      (normalizerFixedRepresentative D k (normalizerInertiaFusionIndex swap i)))
    (hc : ∀ i : Fin 9, Nat.card (centralizer ({normalizerFixedRepresentative D k i} :
      Set (normalizer (CaseII.E D k : Set G)))) = normalizerFixedCentralizerOrders i)
    (j : Fin 5) :
    scalarProduct _ (normalizerInducedCharacter D k L j) (normalizerInducedCharacter D k L j) =
      if swap then 1 else (![3/4, 7/4, 1, 3/4, 7/4] j : ℂ) := by
  rw [induced_norm D k L Q j hc]
  simp_rw [normalizerInducedCharacter_fixed_class_sum, hc,
    normalizerInertiaClassSum_of_fusion D k L swap hf]
  cases swap <;> fin_cases j <;>
    norm_num [Fin.sum_univ_succ, normalizerFixedCentralizerOrders,
      normalizerInertiaExpectedClassSum]

include L Q in
/-- The false fusion assignment would give an actual character squared norm 3/4. -/
public theorem normalizerInertiaFusion_true_of_centralizers
    (swap : Bool)
    (hf : ∀ i : Fin 17, IsConj (normalizerCentralizer D k (localRepresentative i))
      (normalizerFixedRepresentative D k (normalizerInertiaFusionIndex swap i)))
    (hc : ∀ i : Fin 9, Nat.card (centralizer ({normalizerFixedRepresentative D k i} :
      Set (normalizer (CaseII.E D k : Set G)))) = normalizerFixedCentralizerOrders i) :
    swap = true := by
  cases swap
  · have hn := normalizerInducedCharacter_norm_of_fusion_centralizers D k L Q false hf hc 0
    obtain ⟨n, he⟩ := (normalizerInducedCharacter_isCharacter D k L 0).scalarProduct_eq_nat
      (normalizerInducedCharacter_isCharacter D k L 0)
    rw [he] at hn
    have heq : (4 : ℂ) * n = 3 := by norm_num at hn; linear_combination 4 * hn
    have : 4 * n = 3 := by exact_mod_cast heq
    omega
  · rfl

/-- The precise group-theoretic inputs give all twelve columns of each constructed character. -/
public theorem normalizerInducedCharacter_values_of_fusion_centralizers
    (swap : Bool)
    (hf : ∀ i : Fin 17, IsConj (normalizerCentralizer D k (localRepresentative i))
      (normalizerFixedRepresentative D k (normalizerInertiaFusionIndex swap i)))
    (hc : ∀ i : Fin 9, Nat.card (centralizer ({normalizerFixedRepresentative D k i} :
      Set (normalizer (CaseII.E D k : Set G)))) = normalizerFixedCentralizerOrders i)
    (j : Fin 5) (r : Fin 12) :
    normalizerInducedCharacter D k L j (Q.representative r) =
      normalizerFullValues 0 (Fin.natAdd 7 j) r := by
  have hswap := normalizerInertiaFusion_true_of_centralizers D k L Q swap hf hc
  subst swap
  rcases normalizerIndex_cases r with ⟨i, rfl⟩ | ⟨i, rfl⟩
  · rw [NormalizerClassData.representative, normalizerFullRepresentative_fixed,
      normalizerInducedCharacter_fixed_class_sum, hc,
      normalizerInertiaClassSum_of_fusion D k L true hf]
    fin_cases j <;> fin_cases i <;>
      norm_num [normalizerFixedCentralizerOrders, normalizerInertiaExpectedClassSum,
        normalizerFixedIndex, normalizerFullValues, normalizerNonspecialValues,
        normalizerCharacterValues, normalizerIntegralValues, normalizerFiveValues,
        Fin.append, Fin.addCases, Fin.natAdd, Fin.castLT, Fin.subNat]
  · exact normalizerInducedCharacter_free_values D k L Q j i

include Q in
/-- Norm one proves irreducibility of the five actual representation characters. -/
public theorem normalizerInducedCharacter_irreducible_of_fusion_centralizers
    (swap : Bool)
    (hf : ∀ i : Fin 17, IsConj (normalizerCentralizer D k (localRepresentative i))
      (normalizerFixedRepresentative D k (normalizerInertiaFusionIndex swap i)))
    (hc : ∀ i : Fin 9, Nat.card (centralizer ({normalizerFixedRepresentative D k i} :
      Set (normalizer (CaseII.E D k : Set G)))) = normalizerFixedCentralizerOrders i)
    (j : Fin 5) : IsIrreducibleCharacter (normalizerInducedCharacter D k L j) := by
  obtain ⟨n, ρ, he⟩ := normalizerInducedCharacter_isCharacter D k L j
  refine ⟨n, ρ, (irreducible_iff_character_norm_one ρ).mpr ?_, he⟩
  change scalarProduct _ ρ.character ρ.character = 1
  rw [← he, normalizerInducedCharacter_norm_of_fusion_centralizers D k L Q swap hf hc,
    normalizerInertiaFusion_true_of_centralizers D k L Q swap hf hc]
  rfl

include L in
/-- Conditional assembly of the actual induced block from purely group-theoretic inputs. -/
public theorem nonempty_normalizerInducedBlock_of_fusion_centralizers
    (swap : Bool)
    (hf : ∀ i : Fin 17, IsConj (normalizerCentralizer D k (localRepresentative i))
      (normalizerFixedRepresentative D k (normalizerInertiaFusionIndex swap i)))
    (hc : ∀ i : Fin 9, Nat.card (centralizer ({normalizerFixedRepresentative D k i} :
      Set (normalizer (CaseII.E D k : Set G)))) = normalizerFixedCentralizerOrders i) :
    Nonempty (NormalizerInducedBlock Q) := by
  exact ⟨{ character := normalizerInducedCharacter D k L
           irreducible := normalizerInducedCharacter_irreducible_of_fusion_centralizers D k L Q swap hf hc
           values := normalizerInducedCharacter_values_of_fusion_centralizers D k L Q swap hf hc }⟩
end Theory.GroupTheory.HeldM22A10.M22Identification.CharacterOrder
