module
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.LocalConfigurationNaturalHStarSourceFiveExclusion
public import Theory.SpecificGroups.Alternating.FiveResidualPlacement
/-!
# Residual placement and the orthogonal A₅ exclusion in 12.2.19

The original chosen V lies in O₂(L), hence in O₂(N_G(L)) and in
O₂(H ∩ N_G(L)). The intrinsic A₅-residual placement theorem now gives
V ≤ O²(H)O₂(H), retaining the literal embedded residual and two-core.
The unique proper Sylow-overgroup premise follows from the original
H-star minimality, not from a model-labelled configuration.

Applying this containment to the previously proved quadratic-action
obstruction removes the last extra hypothesis from the exclusion of
12.2.7(3i): one or two orthogonal A₅ modules cannot occur. Their own
conjugation marking supplies the required residual identification.

The source production of the 12.2.7 alternatives and the A₇ branch still
belong to qt-d-12213-hstar-natural. This module completes the exclusion
of (3i), not the full nonsolvable exclusion or natural local analysis.

Source: Aschbacher--Smith, 12.2.7 and 12.2.19, printed pp.797 and 801–802.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource
open ChapterI.Section06To08
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V H : Subgroup G}

/-- The chosen Irr⁺ module lies in the original component two-core. -/
theorem chosen_le_component_core_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T) : V ≤ L.pCoreIn 2 := by
  have hc := (D.fundamentalSetup h.toHypothesis1221).module_le_orbitCore
  rw [D.fundamentalSetup_module] at hc
  have ho : componentOrbit V (T : Subgroup G) = V :=
    le_antisymm (iSup_conjugates_le_of_le_normalizer V T V le_rfl
      (((structural L h).2.2 V D).1)) (le_componentOrbit V T)
  simpa only [ho,D.localOrbit_eq] using hc

/-- Characteristicity of O₂(L) places V in the full normalizer two-core. -/
theorem chosen_le_normalizer_core_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T) :
    V ≤ (normalizer (L : Set G)).pCoreIn 2 := by
  apply (chosen_le_component_core_at h D structural).trans
  exact le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 L)
    ((pCoreIn_le 2 L).trans L.le_normalizer)
    (normalizer_le_normalizer_characteristic_image L (pCore 2 L))

/-- The two-core of the literal local intersection contains V. -/
theorem chosen_hstar_le_local_intersection_core_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G))) :
    V ≤ (H ⊓ normalizer (L : Set G)).pCoreIn 2 := by
  let M := normalizer (L : Set G)
  let Q := M.pCoreIn 2
  have hn : H ⊓ M ≤ normalizer ((H ⊓ Q : Subgroup G) : Set G) :=
    (le_inf (inf_le_left.trans H.le_normalizer)
      (inf_le_right.trans (M.le_normalizer.trans
        (normalizer_le_normalizer_characteristic_image M (pCore 2 M))))).trans
      inf_normalizer_le_normalizer_inf
  have hq : H ⊓ Q ≤ (H ⊓ M).pCoreIn 2 :=
    le_pCoreIn_of_normalizes ((isPGroup_pCoreIn 2 M).to_le inf_le_right)
      (inf_le_inf_left H (pCoreIn_le 2 M)) hn
  exact (le_inf (D.le_sylow.trans hH.1.1.2)
    (chosen_le_normalizer_core_at h D structural)).trans hq

/-- The source residual identification forces V into O²(H)O₂(H). -/
theorem chosen_hstar_le_residual_join_core_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (e : (pResidual 2 H ⧸ pCore 2 (pResidual 2 H)) ≃* alternatingGroup (Fin 5)) :
    V ≤ (pResidual 2 H).map H.subtype ⊔ H.pCoreIn 2 := by
  let B := H ⊓ normalizer (L : Set G)
  have hTB : (T : Subgroup G) ≤ B := le_inf hH.1.1.2 (structural L h).1
  have hp : ∀ Y : Subgroup H, (T.subtype hH.1.1.2 : Subgroup H) ≤ Y →
      Y ≠ ⊤ → Y ≤ B.subgroupOf H := by
    intro Y hSY hne
    have hTY : (T : Subgroup G) ≤ Y.map H.subtype := by
      have hh := map_mono (f := H.subtype) hSY
      change ((T : Subgroup G).subgroupOf H).map H.subtype ≤ _ at hh
      rwa [map_subgroupOf_eq_of_le hH.1.1.2] at hh
    have hYH : Y.map H.subtype < H := by
      have hh := (map_lt_map_iff_of_injective H.subtype_injective).mpr (lt_top_iff_ne_top.mpr hne)
      simpa only [← MonoidHom.range_eq_map,range_subtype] using hh
    exact map_le_iff_le_comap.mp
      (le_inf (map_subtype_le _) (Chapter3.HStar.proper_overgroup_le T hH hTY hYH))
  have hc := Theory.SpecificGroups.Alternating.FiveResidualPlacement.core_le_residual_join_core
    (T.subtype hH.1.1.2) (B.subgroupOf H) (comap_mono hTB) hp e
  have hm := map_mono (f := H.subtype) hc
  rw [Theory.SpecificGroups.Alternating.FiveBorelCentralFactor.core_subgroupOf_map
    (show B ≤ H from inf_le_left), Subgroup.map_sup] at hm
  exact (chosen_hstar_le_local_intersection_core_at h D structural hH).trans hm

/-- The original one-or-two orthogonal A₅ alternative is impossible, with no extra containment or residual-identification premise. -/
theorem chosen_hstar_not_one_or_two_five_of_source_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (hnone : NoEscape L V) (hTI : IsTISubgroup V)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G))) :
    ¬ Chapter6.Source.IsOneOrTwoA5Modules ((pResidual 2 H).map H.subtype)
      ⁅hstarOmegaModule T H, (pResidual 2 H).map H.subtype⁆ := by
  intro hm
  have he : Nonempty ((((pResidual 2 H).map H.subtype) ⧸
      pCore 2 ((pResidual 2 H).map H.subtype)) ≃* alternatingGroup (Fin 5)) := by
    rcases hm with ⟨e,b,hb⟩ | ⟨e,b,hb⟩ <;> exact ⟨e⟩
  obtain ⟨e⟩ := he
  let c := (pResidual 2 H).equivMapOfInjective H.subtype H.subtype_injective
  let d := (QuotientGroup.congr _ _ c (pCore_map_iso 2 c)).trans e
  exact chosen_hstar_not_one_or_two_five_at h D structural hnone hTI hH
    (chosen_hstar_le_residual_join_core_at h D structural hH d) hm
end CFSG.Quasithin.Chapter12.Section02.RecognitionSource
