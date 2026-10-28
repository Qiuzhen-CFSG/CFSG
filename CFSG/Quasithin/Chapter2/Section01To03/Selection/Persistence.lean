module

public import CFSG.Quasithin.Chapter2.Section01To03.Selection.Transport
/-!
# Core normalizers preserve local pairs

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
Lemmas 2.3.2(3) and 2.3.8(1–3), printed pp.521–524.

A Sylow subgroup above the local base lies in β and hence in M; uniqueness
makes its order strictly smaller than that of T. Characteristic two and
the central-Sylow intersection argument put the local subgroup's two-core
in S₂e. Normality of O₂(H) embeds H in its normalizer, preserving the
actual local pair. O₂(H) also supplies a nontrivial normal two-subgroup
of that normalizer, putting it in Γ.

The source assembly theorems retain the genuine simple QTKE hypothesis,
the maximal two-local M containing T, and uniqueness where it is needed.
Only parts (1–3) of 2.3.8 are asserted here; its later structural conclusions
belong to the local-structure development.
-/

public section
namespace CFSG.Quasithin.Chapter2
open Subgroup
variable {G : Type*} [Group G] [Finite G] {M H U L : Subgroup G}

/-- Lemma 2.3.8(1): the chosen Sylow is in β, smaller than T, and Sylow in H ∩ M. -/
theorem lemma_2_3_8_1 (T : Sylow 2 G) (hTM : (T : Subgroup G) ≤ M)
    (hunique : ∀ K : Subgroup G, IsMaximalTwoLocal K → (T : Subgroup G) ≤ K → K = M)
    (hH : H ∈ gamma (Chapter1.He G) M) (hpair : (U, L) ∈ localPairsIn (Chapter1.He G) M H)
    (S : Sylow 2 H) (hUS : U ≤ (S : Subgroup H).map H.subtype) :
    Nat.card ((S : Subgroup H).map H.subtype) < Nat.card (T : Subgroup G) ∧
    (S : Subgroup H).map H.subtype ∈ beta M ∧
    (S : Subgroup H).map H.subtype ≤ M ∧
    ∃ R : Sylow 2 ↥(H ⊓ M), (R : Subgroup ↥(H ⊓ M)).map (H ⊓ M).subtype =
      (S : Subgroup H).map H.subtype := by
  have hSb := beta_mono hpair.1.1 hUS (S.isPGroup'.map H.subtype)
  refine ⟨?_, hSb, hSb.2.1, sylow_image_in_inf S hSb.2.1⟩
  rw [sylow_image_card, ← twoPart_eq_sylow_card T hTM]
  exact gamma_twoPart_lt T hTM hunique hH

/-- Lemma 2.3.8(2): the local subgroup’s two-core has characteristic-two normalizer. -/
theorem lemma_2_3_8_2 (hEven : IsEvenCharacteristic G) (hM : M ∈ Chapter1.He G)
    (hpair : (U, L) ∈ localPairsIn (Chapter1.He G) M H) :
    twoCore L ∈ Chapter1.S2e G :=
  beta_twoCore_mem_S2e hEven hM hpair.1.1 hpair.1.2.2.2.1 hpair.1.2.1

omit [Finite G] in
/-- Lemma 2.3.8(3): the pair persists into N_G(O₂(H)), which belongs to Γ. -/
theorem lemma_2_3_8_3 (hH : H ∈ gamma (Chapter1.He G) M)
    (hpair : (U, L) ∈ localPairsIn (Chapter1.He G) M H) :
    (U, L) ∈ localPairsIn (Chapter1.He G) M (normalizer (twoCore H : Set G)) ∧
    normalizer (twoCore H : Set G) ∈ gamma (Chapter1.He G) M := by
  have hp := localPairsIn_mono (le_normalizer_twoCore H) hpair
  refine ⟨hp, ?_, (U, L), hp⟩
  intro he
  apply hH.1
  exact bot_unique (he ▸ le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 H)
    (twoCore H).le_normalizer le_rfl)

/-- Lemma 2.3.2(3) under the genuine simple QTKE and maximal-two-local hypotheses. -/
theorem lemma_2_3_2_3 {C : GroupClass} (hG : IsSimpleQTKE C G)
    (T : Sylow 2 G) (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hU : U ∈ beta M) (hUH : U ≤ H) (hH : H ∈ Chapter1.He G) :
    twoCore H ∈ Chapter1.S2e G ∧ U ∈ Chapter1.S2e G := by
  have hMe : M ∈ Chapter1.He G := Chapter1.mem_He_iff.mpr (hG.evenCharacteristic T M hM hTM)
  exact ⟨beta_twoCore_mem_S2e hG.evenCharacteristic hMe hU hUH hH,
    beta_mem_S2e hG.evenCharacteristic hMe hU⟩

/-- Source assembly of exactly Lemma 2.3.8(1–3), with E instantiated as He. -/
theorem lemma_2_3_8_1_to_3 {C : GroupClass} (hG : IsSimpleQTKE C G)
    (T : Sylow 2 G) (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hunique : ∀ K : Subgroup G, IsMaximalTwoLocal K → (T : Subgroup G) ≤ K → K = M)
    (hH : H ∈ gamma (Chapter1.He G) M)
    (hpair : (U, L) ∈ localPairsIn (Chapter1.He G) M H)
    (S : Sylow 2 H) (hUS : U ≤ (S : Subgroup H).map H.subtype) :
    Nat.card ((S : Subgroup H).map H.subtype) < Nat.card (T : Subgroup G) ∧
    (S : Subgroup H).map H.subtype ∈ beta M ∧
    (∃ R : Sylow 2 ↥(H ⊓ M), (R : Subgroup ↥(H ⊓ M)).map (H ⊓ M).subtype =
      (S : Subgroup H).map H.subtype) ∧
    twoCore L ∈ Chapter1.S2e G ∧
    (U, L) ∈ localPairsIn (Chapter1.He G) M (normalizer (twoCore H : Set G)) ∧
    normalizer (twoCore H : Set G) ∈ gamma (Chapter1.He G) M := by
  have h1 := lemma_2_3_8_1 T hTM hunique hH hpair S hUS
  have h2 := lemma_2_3_8_2 hG.evenCharacteristic
    (Chapter1.mem_He_iff.mpr (hG.evenCharacteristic T M hM hTM)) hpair
  have h3 := lemma_2_3_8_3 hH hpair
  exact ⟨h1.1, h1.2.1, h1.2.2.2, h2, h3⟩
end CFSG.Quasithin.Chapter2
