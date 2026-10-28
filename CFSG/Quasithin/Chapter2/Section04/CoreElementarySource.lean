module
public import CFSG.Quasithin.Chapter2.Section04.CoreSource
public import CFSG.Quasithin.Chapter2.Section01To03.LocalStructure.IndexTwo

/-!
# Elementary cores and the mixed-normalizer obstruction in Γₑ₀

Reselecting a minimal block preserves the original Sylow subgroup. The
original two-core embeds in the elementary two-core of that smaller
parabolic, so every member of Γₑ₀ has elementary two-core. For a mixed
product W, the index-two Thompson subgroup supplies a β base in N_H(W).
If its ambient two-normalizer is sufficiently large, source maximality
puts N_G(W) back in Γₑ₀. Thus W must be elementary, contradicting the
maximality of either of its two distinct maximum elementary factors.

The last theorem is the actual normalizer-size consumer used to exclude
the dihedral C.6 alternative. The containment of the Thompson subgroup
and the escaping relative normalizer remain explicit local geometric
inputs, to be discharged by each marked-block application.

Source: Aschbacher–Smith, 2.4.5 and the proof of 2.4.27, printed pp.528,
543–544 (combined manuscript, 1 March 2004).
-/

public section
open Subgroup Stellmacher
namespace CFSG.Quasithin.Chapter2
variable {G : Type*} [Group G] [Finite G] {M H : Subgroup G}

/-- Reselect the minimal block while retaining the original Sylow image. -/
theorem exists_minimalBlockSetup_with_sylow
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hTM : (T : Subgroup G) ≤ M)
    (hu : ∀ N : Subgroup G, IsMaximalTwoLocal N → (T : Subgroup G) ≤ N → N = M)
    (hH : H ∈ gammaEvenZero (Chapter1.He G) M) (S : Sylow 2 H)
    (hpair : ((S : Subgroup H).map H.subtype, H) ∈
      localPairsIn (Chapter1.He G) M H) :
    ∃ d : MinimalBlockSetup M, d.H ≤ H ∧
      (d.S : Subgroup d.H).map d.H.subtype = (S : Subgroup H).map H.subtype := by
  obtain ⟨K, hKH, hg, P, hP, hp, hmax, hmin, hgen⟩ :=
    exists_minimal_parabolic_in_gammaEvenZero hH S hpair
  obtain ⟨blocks⟩ := lemma_2_3_8_4_of_localC129 hG localC129Input_knownSimple
    T hTM hu hg.1 hg.2 hp P le_rfl
  obtain ⟨B, hB, hout, hmoved⟩ := blocks.exists_escapingBlock hp.1.2.2.2.2
  exact ⟨⟨K, P, hg, hp, hmax, hmin, B, hB, hout, hmoved, hgen B hout⟩, hKH, hP⟩

/-- Every original characteristic-two member of Γ₀ has elementary two-core. -/
theorem gammaEvenZero_twoCore_elementary_source
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hTM : (T : Subgroup G) ≤ M)
    (hu : ∀ N : Subgroup G, IsMaximalTwoLocal N → (T : Subgroup G) ≤ N → N = M)
    (hH : H ∈ gammaEvenZero (Chapter1.He G) M) :
    IsElementaryAbelian 2 (twoCore H) := by
  have hgam : H ∈ gamma (Chapter1.He G) M := hH.1.elim (fun h => h.1.1) (fun h => h.1)
  obtain ⟨S, hpair, _⟩ := exists_full_localPair_of_gammaEven ⟨hgam, hH.2⟩
  obtain ⟨d, hd, he⟩ := exists_minimalBlockSetup_with_sylow hG T hTM hu hH S hpair
  obtain ⟨P, hSP⟩ := (d.S.isPGroup'.map d.H.subtype).exists_le_sylow
  have hPM : (P : Subgroup G) ≤ M := (beta_mono d.full_pair.1.1 hSP P.isPGroup').2.1
  have hlt : (d.S : Subgroup d.H).map d.H.subtype < (P : Subgroup G) := by
    apply lt_of_le_of_ne hSP
    intro hp
    have hcore : twoCore d.H ≠ ⊥ :=
      (d.mem_gammaEvenZero.1.elim (fun h => h.1.1) (fun h => h.1)).1
    have hPH : (P : Subgroup G) ≤ d.H := hp ▸ map_subtype_le _
    have hPMH : (P.subtype hPM : Subgroup M).map M.subtype ≤ d.H := by
      simpa only [Sylow.coe_subtype, map_subgroupOf_eq_of_le hPM] using hPH
    exact d.full_pair.1.2.2.2.2 (core_overgroup_le_of_sylow T hTM hu hcore (P.subtype hPM) hPMH)
  let : IsElementaryAbelian 2 (twoCore d.H) := (d.core_source hG P hlt).2.2.2.1
  have hQd : twoCore H ≤ d.H := (pCoreIn_le_sylow H S).trans
    (he ▸ (show (d.S : Subgroup d.H).map d.H.subtype ≤ d.H from map_subtype_le _))
  have hQQ : twoCore H ≤ twoCore d.H := le_pCoreIn_of_normalizes
    (isPGroup_pCoreIn 2 H) hQd (hd.trans (le_normalizer_twoCore H))
  exact IsElementaryAbelian.of_le hQQ

theorem MinimalBlockSetup.thompson_beta_of_index_two
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hu : ∀ N : Subgroup G, IsMaximalTwoLocal N → (T : Subgroup G) ≤ N → N = M)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hi : (elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype)).relIndex
      ((d.S : Subgroup d.H).map d.H.subtype) = 2) :
    elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype) ∈ beta M := by
  have hQ := (d.core_source hG T hST).2.2
  have hQR : twoCore d.H ≤ elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype) :=
    le_sSup hQ
  exact lemma_2_3_8_5b hG T hM hTM hu d.mem_gammaEvenZero.1 d.full_pair d.S le_rfl
    le_rfl (sSup_le (fun _ h => h.1)) hi
    (lemma_2_3_8_5c d.mem_gammaEvenZero.1 d.mem_gammaEvenZero.2 d.full_pair d.S le_rfl hQR).2


/-- A large mixed-product normalizer has elementary two-core in the original
Γₑ₀ setup. This is the maximality step in 2.4.27. -/
theorem MinimalBlockSetup.normalizer_elementary_of_large_twoPart
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hu : ∀ N : Subgroup G, IsMaximalTwoLocal N → (T : Subgroup G) ≤ N → N = M)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hi : (elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype)).relIndex
      ((d.S : Subgroup d.H).map d.H.subtype) = 2)
    (W : Subgroup G) (hQW : twoCore d.H ≤ W)
    (hWS : W ≤ (d.S : Subgroup d.H).map d.H.subtype)
    (hRN : elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype) ≤
      normalizer (W : Set G))
    (hout : ¬ d.H ⊓ normalizer (W : Set G) ≤ M)
    (hcard : Nat.card ((d.S : Subgroup d.H).map d.H.subtype) ≤
      Nat.card ((T : Subgroup G) ⊓ normalizer (W : Set G) : Subgroup G)) :
    IsElementaryAbelian 2 W := by
  let S := (d.S : Subgroup d.H).map d.H.subtype
  let R := elementaryAbelianMaxJ S
  let N := normalizer (W : Set G)
  let J := d.H ⊓ N
  let S₁ := (T : Subgroup G) ⊓ N
  have hR := d.thompson_beta_of_index_two hG T hM hTM hu hST hi
  have hWp : IsPGroup 2 W := (d.S.isPGroup'.map d.H.subtype).to_le hWS
  have hMe := Chapter1.mem_He_iff.mpr (hG.evenCharacteristic T M hM hTM)
  have hQe := beta_twoCore_mem_S2e hG.evenCharacteristic hMe d.full_pair.1.1
    (map_subtype_le _) d.mem_gammaEvenZero.2
  have hWe := Chapter1.lemma_1_1_4_1 hQe hQW hWp
  have hWne : W ≠ ⊥ := hWe.1
  have hJe : J ∈ Chapter1.He G := Chapter1.normalizer_mem_He_of_isPGroup
    d.mem_gammaEvenZero.2 hWp (hWS.trans (map_subtype_le _))
  have hWJ : W ≤ J := le_inf (hWS.trans (map_subtype_le _)) W.le_normalizer
  have hQJ : W ≤ twoCore J := le_pCoreIn_of_normalizes hWp hWJ inf_le_right
  have hRJ : R ≤ J := le_inf ((sSup_le (fun _ h => h.1)).trans (map_subtype_le _)) hRN
  have hp : (R, J) ∈ localPairs (Chapter1.He G) M :=
    ⟨hR, hJe, fun he => hWne (bot_unique (he ▸ hQJ)), hRJ, hout⟩
  have hQN : W ≤ twoCore N := le_pCoreIn_of_normalizes hWp W.le_normalizer le_rfl
  have hNg : N ∈ gamma (Chapter1.He G) M :=
    ⟨fun he => hWne (bot_unique (he ▸ hQN)), ⟨(R, J), hp, inf_le_right⟩⟩
  have hRS₁ : R ≤ S₁ := le_inf
    ((sSup_le (fun _ h => h.1)).trans hST.le) hRN
  have hS₁ : S₁ ∈ beta M := beta_mono hR hRS₁ (T.isPGroup'.to_le inf_le_left)
  have hpart : twoPart d.H ≤ twoPart N := by
    rw [← sylow_image_card d.H d.S]
    exact hcard.trans (beta_card_le_twoPart hS₁ inf_le_right)
  have hNzero := (lemma_2_4_3_2 d.mem_gammaEvenZero ⟨hNg, hWe.2.2⟩ hpart).2
  let : IsElementaryAbelian 2 (twoCore N) :=
    gammaEvenZero_twoCore_elementary_source hG T hTM hu hNzero
  exact IsElementaryAbelian.of_le hQN

/-- Two distinct maximum elementary subgroups cannot generate an elementary
two-core in the large-normalizer alternative of C.6.1. -/
theorem MinimalBlockSetup.mixed_normalizer_card_lt
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hu : ∀ N : Subgroup G, IsMaximalTwoLocal N → (T : Subgroup G) ≤ N → N = M)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hi : (elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype)).relIndex
      ((d.S : Subgroup d.H).map d.H.subtype) = 2)
    (A : Subgroup G) (hA : A ∈ elementaryAbelianMaxSubgroups
      ((d.S : Subgroup d.H).map d.H.subtype))
    (hindex : (twoCore d.H).relIndex A = 2)
    (hRN : elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype) ≤
      normalizer ((twoCore d.H ⊔ A : Subgroup G) : Set G))
    (hout : ¬ d.H ⊓ normalizer ((twoCore d.H ⊔ A : Subgroup G) : Set G) ≤ M) :
    Nat.card ((T : Subgroup G) ⊓ normalizer ((twoCore d.H ⊔ A : Subgroup G) : Set G) : Subgroup G) <
      Nat.card ((d.S : Subgroup d.H).map d.H.subtype) := by
  by_contra! hcard
  let W := twoCore d.H ⊔ A
  have hQ := (d.core_source hG T hST).2.2
  have hWS : W ≤ (d.S : Subgroup d.H).map d.H.subtype := sup_le hQ.1 hA.1
  have hW := d.normalizer_elementary_of_large_twoPart hG T hM hTM hu hST hi W
    le_sup_left hWS hRN hout hcard
  have he : W = twoCore d.H :=
    (Subgroup.eq_of_le_of_card_ge le_sup_left (hQ.2.2 W hWS hW)).symm
  have hAQ : A ≤ twoCore d.H := he ▸ (show A ≤ W from le_sup_right)
  have hidx : (twoCore d.H).relIndex A = 1 := relIndex_eq_one.mpr hAQ
  omega

end CFSG.Quasithin.Chapter2
