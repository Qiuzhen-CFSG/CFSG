module

public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.SylowThompson.KnownSimple
public import CFSG.Quasithin.Chapter6.Section01.SourceHStarE23
public import CFSG.Quasithin.Chapter6.SourceReduction.LocalCentralization.FFReduction.BaumannControl

/-!
# The Thompson rank argument before trivial intersections

The printed E.6.26 assumes normalizer control and uniqueness over the
Sylow centralizer. It does not assume that the module is TI. This version
retains precisely those normalizer assumptions and uses actual E-generation
to apply E.5.2. The original Hypothesis 6.1.1 supplies these assumptions
for both its reduced subgroup and its moved layer. An actual outside
H-star member then gives 6.1.3(2), before any TI conclusion or module
classification has been established.

Source: Aschbacher–Smith E.6.26, printed p.256, and 6.1.3–4, pp.664–665.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
open ChapterB ChapterE
open ChapterE.Section06.FixedPointBounds.SylowThompson

variable {G : Type*} [Group G] [Finite G]

/-- E.6.26 under its original normalizer assumptions, without a TI premise.
The generation input concerns the literal subgroup H and its chosen Sylow. -/
theorem thompson_containment_of_generation
    (T : Sylow 2 G) {M V : Subgroup G} [IsElementaryAbelian 2 V]
    (hVT : V ≤ (T : Subgroup G)) (hNV : normalizer (V : Set G) ≤ M)
    (hunique : ∀ N : Subgroup G, IsMaximalTwoLocal N →
      normalizer ((T : Subgroup G) ⊓ centralizer (V : Set G) : Set G) ≤ N → N = M)
    {j : ℕ} (hjpos : 0 < j) (H : Subgroup G) (S : Sylow 2 H)
    (hgen : IsEGenerated j H)
    (hQA : (T : Subgroup G) ⊓ centralizer (V : Set G) ≤
      (S : Subgroup H).map H.subtype)
    (hAT : (S : Subgroup H).map H.subtype ≤ (T : Subgroup G))
    (hj : (j : ℕ∞) < globalR V)
    (hJ : thompsonJ ((S : Subgroup H).map H.subtype) j ≤ centralizer (V : Set G)) :
    H ≤ M ∧ normalizer ((S : Subgroup H).map H.subtype : Set G) ≤ M := by
  classical
  by_cases hM : M = ⊤
  · subst M
    exact ⟨le_top, le_top⟩
  let A := (S : Subgroup H).map H.subtype
  let Q := (T : Subgroup G) ⊓ centralizer (V : Set G)
  let D := higherThompsonCenter (S : Subgroup H) (0 + j)
  have hVQ : V ≤ Q := le_inf hVT V.le_centralizer
  have hVA : V ≤ A := hVQ.trans hQA
  have hrV : globalR V ≤ (Nat.log 2 (Nat.card V) : ℕ∞) := by
    have hb : ¬ centralizer (↑(⊥ : Subgroup G) : Set G) ≤ normalizer (V : Set G) := by
      intro hn
      apply hM
      apply top_le_iff.mp
      intro x _
      apply hNV
      apply hn
      exact mem_centralizer_iff.mpr (by intro a ha; have : a = 1 := ha; subst a; simp)
    simpa only [subgroupCorank, relIndex_bot_left] using globalR_le_corank bot_le hb
  have hr : j < twoRank A := by
    have hjV : j < Nat.log 2 (Nat.card V) := by exact_mod_cast hj.trans_le hrV
    obtain ⟨B, hB⟩ := elementaryAbelianMaxSubgroups_nonempty A
    have hc := hB.2.2 V hVA inferInstance
    rw [card_eq_elementaryAbelianMaxOrder _ B hB] at hc
    exact hjV.trans_le (Nat.log_mono_right hc)
  have hJQ : thompsonJ A 0 ≤ Q :=
    le_inf ((thompsonJ_le A 0).trans hAT)
      ((lemma_B_2_3_1 A (Nat.zero_le j) hr).trans hJ)
  have hJ0 : thompsonJ A 0 = thompsonJ Q 0 :=
    lemma_B_2_3_3 A Q ((Nat.zero_le j).trans_lt hr) hJQ hQA
  have hne : thompsonJ Q 0 ≠ ⊥ := by
    intro hz
    obtain ⟨B, hB⟩ := elementaryAbelianMaxSubgroups_nonempty A
    have hBJ : B ≤ thompsonJ A 0 := by rw [thompsonJ_zero]; exact le_sSup hB
    have hBb : B = ⊥ := le_bot_iff.mp (hJ0 ▸ hBJ |>.trans hz.le)
    have hc := card_eq_elementaryAbelianMaxOrder A B hB
    rw [hBb] at hc
    have hm : elementaryAbelianMaxOrder A = 1 := by simpa using hc.symm
    have hzR : twoRank A = 0 := by simp [twoRank, hm]
    omega
  have hNQ : normalizer (thompsonJ Q 0 : Set G) ≤ M :=
    normalizer_le_of_unique_maximalTwoLocal hunique
      (T.isPGroup'.to_le ((thompsonJ_le Q 0).trans inf_le_left)) hne
      (normalizer_le_normalizer_thompson Q 0)
  have hNJ : normalizer (thompsonJ A 0 : Set G) ≤ M := hJ0.symm ▸ hNQ
  have hNA : normalizer (A : Set G) ≤ M :=
    (normalizer_le_normalizer_thompson A 0).trans hNJ
  have hVD : V ≤ higherThompsonCenter A j := by
    change V ≤ omegaOneCenterAmbient (thompsonJ A j)
    rw [← (lemma_B_2_3_2 A (le_refl j) hr).2]
    intro x hx
    exact (omegaOneAmbient_le_iff _ _).mp le_rfl x
      ⟨hVA hx, (le_centralizer_iff.mp hJ) hx⟩
      (elemPow_eq_one_of_isElementaryAbelian x hx)
  have hDmap : D.map H.subtype = higherThompsonCenter A j := by
    dsimp [D, higherThompsonCenter, A]
    rw [Nat.zero_add, thompsonJ_map_injective H.subtype H.subtype_injective,
      omegaOneCenterAmbient_map_injective H.subtype H.subtype_injective]
  have hwhole := source_E_5_2_of_isEGenerated S 0 j hjpos hgen
  have hle : thompsonCentralizerGenerators (S : Subgroup H) 0 j ≤ M.comap H.subtype := by
    apply sup_le
    · apply map_le_iff_le_comap.mp
      apply (le_normalizer_map H.subtype).trans
      rw [← thompsonJ_map_injective H.subtype H.subtype_injective]
      exact hNJ
    · apply iSup_le
      intro d
      have hd : d.val ∈ smallIndexSubgroups D (0 + j) := d.property
      have hi : Nat.log 2 ((V ⊓ d.val.map H.subtype).relIndex V) ≤ j := by
        rw [inf_relIndex_left]
        have hv : V ≤ D.map H.subtype := hDmap.symm ▸ hVD
        have hi := relIndex_le_of_le_right (H := d.val.map H.subtype) hv
          (show (d.val.map H.subtype).relIndex (D.map H.subtype) ≠ 0 from index_ne_zero_of_finite)
        have hl := Nat.log_mono_right (b := 2) hi
        rw [relIndex_map_map_of_injective _ _ H.subtype_injective] at hl
        exact hl.trans (by simpa only [Nat.zero_add] using hd.2)
      have hc : centralizer (V ⊓ d.val.map H.subtype : Set G) ≤ M :=
        (centralizer_le_normalizer_of_corank_lt_globalR inf_le_left
          (lt_of_le_of_lt (by exact_mod_cast hi) hj)).trans hNV
      apply map_le_iff_le_comap.mp
      apply (map_mono (thompsonJ_le (centralizer (d.val : Set H)) 0)).trans
      apply (map_centralizer_le_centralizer_image (d.val : Set H) H.subtype).trans
      exact (centralizer_le inf_le_right).trans hc
  refine ⟨?_, hNA⟩
  rw [hwhole] at hle
  intro x hx
  exact hle (show (⟨x, hx⟩ : H) ∈ (⊤ : Subgroup H) from mem_top _)

/-- The numerical source form on a known-simple SQTK subgroup, with actual
E-generation constructed from its generation parameter. -/
theorem thompson_containment_of_parameter
    (T : Sylow 2 G) {M V : Subgroup G} [IsElementaryAbelian 2 V]
    (hVT : V ≤ (T : Subgroup G)) (hNV : normalizer (V : Set G) ≤ M)
    (hunique : ∀ N : Subgroup G, IsMaximalTwoLocal N →
      normalizer ((T : Subgroup G) ⊓ centralizer (V : Set G) : Set G) ≤ N → N = M)
    {j : ℕ} (hjpos : 0 < j) (H : Subgroup G) (S : Sylow 2 H)
    (hH : IsSQTK KnownSimple.IsKnownSimple H) (hn : generationParameter H ≤ j)
    (hQA : (T : Subgroup G) ⊓ centralizer (V : Set G) ≤
      (S : Subgroup H).map H.subtype)
    (hAT : (S : Subgroup H).map H.subtype ≤ (T : Subgroup G))
    (hj : (j : ℕ∞) < globalR V)
    (hJ : thompsonJ ((S : Subgroup H).map H.subtype) j ≤ centralizer (V : Set G)) :
    H ≤ M ∧ normalizer ((S : Subgroup H).map H.subtype : Set G) ≤ M :=
  thompson_containment_of_generation T hVT hNV hunique hjpos H S
    (source_isEGenerated_of_parameter_le_knownSimple hH S hjpos hn) hQA hAT hj hJ

private theorem original_unique_over_LT
    {T : Sylow 2 G} {L M V : Subgroup G} {n : ℕ}
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M V n)
    (N : Subgroup G) (hN : IsMaximalTwoLocal N)
    (hLT : L ⊔ (T : Subgroup G) ≤ N) : N = M := by
  have hstar : L ∈ Chapter1.LStar G (T : Subgroup G) := by
    refine ⟨h.local_mem.1.prop, ?_⟩
    intro K hK hLK
    exact le_antisymm (h.local_mem.1.2 hK hLK) hLK
  have hu := Chapter1.Section02.nonsolvable_uniqueness_knownSimple h.simpleQTKE T hstar
  have horbit : componentOrbit L (T : Subgroup G) = L :=
    le_antisymm (iSup_conjugates_le_of_le_normalizer L T L le_rfl
      h.sylow_normalizes_L) (le_componentOrbit L T)
  have h₁ := hu.normalizer_unique N hN
  have h₂ := hu.normalizer_unique M h.maximal
  rw [horbit] at h₁ h₂
  exact (h₁ hLT).trans (h₂ (sup_le h.L_le h.sylow_le)).symm

private theorem original_rank_one_of_core
    {T : Sylow 2 G} {L M V B : Subgroup G} {n : ℕ}
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M V n)
    (hout : Chapter3.HasMaximalOutside T M)
    [IsElementaryAbelian 2 B] (hBT : B ≤ (T : Subgroup G)) (hB : B ≠ ⊥)
    (hLTB : L ⊔ (T : Subgroup G) ≤ normalizer (B : Set G))
    (hCT : (T : Subgroup G) ⊓ centralizer (B : Set G) =
      (L ⊔ (T : Subgroup G)).pCoreIn 2)
    (hJ : thompsonJ (T : Subgroup G) 1 ≤ centralizer (B : Set G)) :
    globalR B = 1 := by
  by_contra hn
  have hr : (1 : ℕ∞) < globalR B := lt_of_le_of_ne (one_le_globalR B) (Ne.symm hn)
  have hNB : normalizer (B : Set G) ≤ M :=
    normalizer_le_of_unique_maximalTwoLocal (original_unique_over_LT h)
      (IsElementaryAbelian.isPGroup 2 B) hB hLTB
  have huniq : ∀ N : Subgroup G, IsMaximalTwoLocal N →
      normalizer ((T : Subgroup G) ⊓ centralizer (B : Set G) : Set G) ≤ N → N = M := by
    intro N hN hle
    apply original_unique_over_LT h N hN
    apply le_trans ?_ hle
    change L ⊔ (T : Subgroup G) ≤ normalizer
      (((T : Subgroup G) ⊓ centralizer (B : Set G) : Subgroup G) : Set G)
    rw [hCT]
    exact (L ⊔ (T : Subgroup G)).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image _ (pCore 2 _))
  obtain ⟨H, hH⟩ := Chapter3.exists_HStar_of_hasMaximalOutside hout
  let S : Sylow 2 H := T.subtype hH.1.1.2
  have hS : (S : Subgroup H).map H.subtype = (T : Subgroup G) :=
    map_subgroupOf_eq_of_le hH.1.1.2
  have hHsqtk : IsSQTK KnownSimple.IsKnownSimple H := by
    let R := H.pCoreIn 2
    let N := normalizer (R : Set G)
    have hHN : H ≤ N := H.le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image H (pCore 2 H))
    have hN : IsTwoLocal N := ⟨R, hH.1.1.1, isPGroup_pCoreIn 2 H, rfl⟩
    have hh := (h.simpleQTKE.twoLocal_sqtk hN).subgroup (H.subgroupOf N)
    exact ⟨hh.stronglyQuasithin.of_injective
      (subgroupOfEquivOfLe hHN).symm.toMonoidHom (subgroupOfEquivOfLe hHN).symm.injective,
      hh.isKGroup.of_injective
        (subgroupOfEquivOfLe hHN).symm.toMonoidHom (subgroupOfEquivOfLe hHN).symm.injective⟩
  apply hH.1.2
  exact (thompson_containment_of_parameter T hBT hNB huniq (by decide) H S hHsqtk
    ((h.generation_one H hH).le) (by rw [hS]; exact inf_le_left)
    (by rw [hS]) hr (by rw [hS]; exact hJ)).1

/-- Source 6.1.3(2) for the literal original reduced subgroup, in the branch
where the first higher Thompson subgroup centralizes it. No TI is assumed. -/
theorem original_rank_one_of_thompson_centralizes
    {T : Sylow 2 G} {L M V : Subgroup G} {n : ℕ}
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M V n)
    (hout : Chapter3.HasMaximalOutside T M)
    (hJ : thompsonJ (T : Subgroup G) 1 ≤ centralizer (V : Set G)) :
    globalR V = 1 := by
  let := h.V_mem.2.1
  have hV : V ≠ ⊥ := fun he => h.nontrivial_action (by rw [layer, he, commutator_bot_left])
  exact original_rank_one_of_core h hout h.V_le_T hV (reduced_normalizes h.V_mem)
    (h.rankOneInput hout).sylow_centralizer_eq_core hJ

/-- The same original rank-one conclusion on the literal moved layer. -/
theorem original_layer_rank_one_of_thompson_centralizes
    {T : Sylow 2 G} {L M V : Subgroup G} {n : ℕ}
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M V n)
    (hout : Chapter3.HasMaximalOutside T M)
    (hJ : thompsonJ (T : Subgroup G) 1 ≤ centralizer (layer L V : Set G)) :
    globalR (layer L V) = 1 := by
  let := h.layer_elementary
  exact original_rank_one_of_core h hout h.layer_le_T h.nontrivial_action
    (sup_le (normalizer_commutator_ge_right V L) h.sylow_normalizes_layer)
    (h.rankOneInput hout).commutator_input.sylow_centralizer_eq_core hJ

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition
