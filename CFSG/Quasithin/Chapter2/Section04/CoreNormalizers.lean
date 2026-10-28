module

public import CFSG.Quasithin.Chapter2.Section01To03.LocalStructure.CoreGeometry

/-!
# Core normalizers in the nonempty characteristic-two branch

A characteristic-two member of Γ has a full Sylow local pair. The two
source maximality conditions then prove that a characteristic-two member
with at least the same two-part as a member of Γₑ₀ also lies in Γₑ₀,
with equality of two-parts. The actual Sylow subgroup stays Sylow in the
normalizer of O₂(H); normality and this containment identify its two-core
with O₂(H). The same maximality argument applied to a nontrivial normal
subgroup of H gives N_T(S₀)=S.

These are the original subgroup families, embedded cores and Sylow maps.
They supply the entry to the block/shadow argument without assuming its
classification conclusions or any additional universal source theorem.
Source: Aschbacher–Smith, Lemmas 2.4.3–4 and the preceding Sylow choice,
printed pp.527–528 (combined manuscript of 1 March 2004).
-/

public section
namespace CFSG.Quasithin.Chapter2
open Subgroup
variable {G : Type*} [Group G] [Finite G] {M H K U L : Subgroup G}

/-- Choose a full local pair in a characteristic-two member of Γ, with the
same actual Sylow subgroup in its intersection with M. -/
theorem exists_full_localPair_of_gammaEven
    (hH : H ∈ gammaEven (Chapter1.He G) M) :
    ∃ S : Sylow 2 H,
      ((S : Subgroup H).map H.subtype, H) ∈ localPairsIn (Chapter1.He G) M H ∧
      ∃ R : Sylow 2 ↥(H ⊓ M),
        (R : Subgroup ↥(H ⊓ M)).map (H ⊓ M).subtype =
          (S : Subgroup H).map H.subtype := by
  obtain ⟨P, hP, hPH⟩ := hH.1.2
  obtain ⟨S, _, hS⟩ := beta_exists_sylow hP.1 (hP.2.2.2.1.trans hPH)
  refine ⟨S, ?_, sylow_image_in_inf S hS.2.1⟩
  exact ⟨⟨hS, hH.2, hH.1.1, map_subtype_le _, gamma_not_le hH.1⟩, le_rfl⟩

/-- Source 2.4.3(2), preserving both starred selection alternatives. -/
theorem lemma_2_4_3_2
    (hH : H ∈ gammaEvenZero (Chapter1.He G) M)
    (hK : K ∈ gammaEven (Chapter1.He G) M) (hHK : twoPart H ≤ twoPart K) :
    twoPart K = twoPart H ∧ K ∈ gammaEvenZero (Chapter1.He G) M := by
  obtain ⟨S, hS, _⟩ := exists_full_localPair_of_gammaEven hK
  have hbound : ∀ V ∈ localBases (Chapter1.He G) M,
      Nat.card V ≤ Nat.card ((S : Subgroup K).map K.subtype) := by
    intro V hV
    rw [sylow_image_card]
    exact (gammaZero_card_bound hH.1 hV).trans hHK
  rcases hH.1 with hs | hm
  · have hlarge : K ∈ gammaWithLargestBase (Chapter1.He G) M :=
      ⟨hK.1, ((S : Subgroup K).map K.subtype, K), hS, hbound⟩
    have h := gammaStar_of_twoPart_le hs hlarge hHK
    exact ⟨h.2, Or.inl h.1, hK.2⟩
  · have h := gammaMax_of_twoPart_le hm hK.1 hHK
    exact ⟨h.2, Or.inr h.1, hK.2⟩

/-- Source 2.4.3(1): the original core normalizer lies in Γₑ₀, has exactly
the same embedded core, and retains the original Sylow subgroup. -/
theorem lemma_2_4_3_1 (hEven : IsEvenCharacteristic G)
    (hM : M ∈ Chapter1.He G) (hH : H ∈ gammaEvenZero (Chapter1.He G) M)
    (hpair : (U, L) ∈ localPairsIn (Chapter1.He G) M H)
    (S : Sylow 2 H) (hUS : U ≤ (S : Subgroup H).map H.subtype) :
    let N := normalizer (twoCore H : Set G)
    N ∈ gammaEvenZero (Chapter1.He G) M ∧ twoCore N = twoCore H ∧
      ∃ P : Sylow 2 N,
        (P : Subgroup N).map N.subtype = (S : Subgroup H).map H.subtype := by
  let N := normalizer (twoCore H : Set G)
  have hN := lemma_2_3_9_1 hH.1 hpair S hUS
  obtain ⟨P, hP⟩ := hN.2.1
  have hSb := beta_mono hpair.1.1 hUS (S.isPGroup'.map H.subtype)
  have hQe := beta_twoCore_mem_S2e hEven hM hSb (map_subtype_le _) hH.2
  have hNH : twoCore N ≤ H :=
    (pCoreIn_le_sylow N P).trans (hP.le.trans (map_subtype_le _))
  have hcore : twoCore N = twoCore H := by
    apply le_antisymm
    · exact le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 N) hNH
        ((le_normalizer_twoCore H).trans (le_normalizer_twoCore N))
    · exact le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 H)
        (twoCore H).le_normalizer le_rfl
  exact ⟨⟨hN.1, hQe.2.2⟩, hcore, P, hP⟩

/-- Source 2.4.4: the normalizer in T of the actual nontrivial S₀ normal
inside H is exactly the original Sylow subgroup S. -/
theorem lemma_2_4_4
    (hH : H ∈ gammaZero (Chapter1.He G) M)
    (hpair : (U, L) ∈ localPairsIn (Chapter1.He G) M H)
    (S : Sylow 2 H) (hUS : U ≤ (S : Subgroup H).map H.subtype)
    (T : Sylow 2 G) (hST : (S : Subgroup H).map H.subtype ≤ (T : Subgroup G))
    (S₀ : Subgroup G) (hne : S₀ ≠ ⊥)
    (hS₀ : S₀ ≤ (S : Subgroup H).map H.subtype) (hnormal : (S₀.subgroupOf H).Normal) :
    (T : Subgroup G) ⊓ normalizer (S₀ : Set G) = (S : Subgroup H).map H.subtype := by
  let N := normalizer (S₀ : Set G)
  have hHN : H ≤ N :=
    (normal_subgroupOf_iff_le_normalizer (hS₀.trans (map_subtype_le _))).mp hnormal
  have hp : IsPGroup 2 S₀ := T.isPGroup'.to_le (hS₀.trans hST)
  have hQN : S₀ ≤ twoCore N := le_pCoreIn_of_normalizes hp S₀.le_normalizer le_rfl
  have hNne : twoCore N ≠ ⊥ := fun he => hne (bot_unique (he ▸ hQN))
  obtain ⟨P, hP⟩ := (lemma_2_3_7_2 hH hpair S hUS ⟨hNne, hHN⟩).2.1
  let B : Subgroup G := (T : Subgroup G) ⊓ N
  have hSB : (S : Subgroup H).map H.subtype ≤ B :=
    le_inf hST ((map_subtype_le _).trans hHN)
  have hBp : IsPGroup 2 (B.subgroupOf N) :=
    (T.isPGroup'.to_le (show B ≤ (T : Subgroup G) from inf_le_left)).comap_of_injective
      N.subtype N.subtype_injective
  have hPB : (P : Subgroup N) ≤ B.subgroupOf N := by
    intro p hp
    exact hSB (hP ▸ mem_map_of_mem N.subtype hp)
  have he : B.subgroupOf N = (P : Subgroup N) := P.is_maximal' hBp hPB
  have hm := congrArg (fun Q : Subgroup N => Q.map N.subtype) he
  rw [map_subgroupOf_eq_of_le (show B ≤ N from inf_le_right), hP] at hm
  exact hm

end CFSG.Quasithin.Chapter2
