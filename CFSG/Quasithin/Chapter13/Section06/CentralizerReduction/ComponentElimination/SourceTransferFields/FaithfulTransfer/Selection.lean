module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.Signalizer
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.ComponentControl.TwoCore

/-!
# Selecting a faithful component in the involution centralizer

A.3.9 and the checked quotient deduction 1.2.1(1) identify the C-component
layer of C_G(a) with its solvable residual. Every perfect subgroup K of
that centralizer lies in this layer. If K moves Ω₁(Z(O₂(C_G(a)))), some
actual C-component moves it. A.4.9 makes that component's intrinsic module
nontrivial. Its local-family membership follows from 1.2.6 for the given
ambient Sylow subgroup contained in C_G(a).

This selects directly from C(C_G(a)), which suffices for the replacement
choice in 13.6.17. The SQTK quotient and two-local premises are derived
from the involution and ambient simple-QTKE hypotheses. Only the genuine
universal earlier theorem A.3.9(1) remains explicit.

Source: Aschbacher–Smith, combined 1 March 2004 manuscript,
13.6.17, printed pp.930–931; 1.2.1 and 1.2.6, pp.503–506; A.4.9, p.60.
-/

@[expose] public section
open Subgroup Stellmacher
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields
open ChapterA.Section04 Chapter1.Section02.Adequate ComponentSelection
universe u
variable {G : Type u} [Group G] [Finite G]

/-- Selection in the actual layer of the centralizer, followed by A.4.9. -/
theorem faithful_component_of_moving_core {𝒦 : GroupClass.{u}}
    (hG : IsSimpleQTKE 𝒦 G)
    (hA39 : ∀ (X : Type u) [Group X] [Finite X],
      IsSQTK 𝒦 X → pCore 2 X = ⊥ → cComponentLayer X = solvableResidual X)
    (S : Sylow 2 G) (a : G) (ha : orderOf a = 2)
    (hSa : (S : Subgroup G) ≤ Gv a)
    (K : Subgroup G) [Group.IsPerfect K] (hKa : K ≤ Gv a)
    (hm : ¬ K ≤ centralizer (omegaOneCenterAmbient (Qv a) : Set G)) :
    ∃ K₁ : Subgroup G, K₁ ∈ Chapter1.cComponentsIn (Gv a) ∧
      K₁ ∈ MainForward.faithfulLocalComponents S := by
  let M := Gv a
  have hloc : IsTwoLocal M := Theory.GroupTheory.isTwoLocal_involution_centralizer ha
  have hMH : M ∈ Chapter1.HOver G (S : Set G) :=
    ⟨Chapter1.mem_H_of_isTwoLocal hloc, hSa⟩
  have hMQ := hG.twoLocal_sqtk hloc
  have hQ : IsSQTK 𝒦 (M ⧸ pCore 2 M) := by
    refine ⟨?_, hMQ.isKGroup.quotient (pCore 2 M)⟩
    intro p hp ho
    let : Fact p.Prime := ⟨hp⟩
    exact (primeRank_quotient_le_of_isTwoGroup p ho (pCore 2 M) pCore_isPGroup).trans
      (hMQ.stronglyQuasithin p hp ho)
  have hgen := Chapter1.Section02.proposition_1_2_1_one_of_A_3_9 hA39 hQ
  have hKlayer : K ≤ (cComponentLayer M).map M.subtype := by
    rw [hgen]
    exact le_map_solvableResidual_of_isPerfect K M hKa
  have hex : ∃ D : Subgroup M, D.IsCComponent ∧
      ¬ D.map M.subtype ≤ centralizer (omegaOneCenterAmbient (Qv a) : Set G) := by
    by_contra! hn
    apply hm
    apply hKlayer.trans
    rw [map_le_iff_le_comap]
    exact sSup_le fun D hD => map_le_iff_le_comap.mp (hn D hD)
  obtain ⟨D, hD, hmove⟩ := hex
  let K₁ := D.map M.subtype
  have hK₁ : K₁ ∈ Chapter1.cComponentsIn M := by
    refine ⟨map_subtype_le D, ?_⟩
    simpa only [K₁, subgroupOf, comap_map_eq_self_of_injective M.subtype_injective] using hD
  have hL := ((Chapter1.lemma_1_2_6 S hMH).1 hK₁).2
  refine ⟨K₁, hK₁, (mem_faithfulLocalComponents_iff_module S
    (hG.evenCharacteristic S)).mpr ⟨hL, ?_⟩⟩
  apply (intrinsic_ne_bot_iff_core_module_ne_bot K₁ M hK₁.1 hK₁.2.subnormal
    (mem_L_isPPerfect hL)).mpr
  intro he
  apply hmove
  exact commutator_eq_bot_iff_le_centralizer.mp
    ((signalizerModule_eq_commutator_omegaCenter K₁ (M.pCoreIn 2)).symm.trans he)

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields

end
