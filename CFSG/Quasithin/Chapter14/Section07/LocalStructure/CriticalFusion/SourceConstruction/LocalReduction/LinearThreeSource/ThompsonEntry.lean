module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.LinearThreeSource.PointQuotient
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.LinearThreeSource.ChosenFixed
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalUnitaryNoncentrality.ThompsonGeneration
public import Theory.GroupTheory.ReducedNormal.ComponentSeed

/-!
# Original point-component entry into the chosen-module source

Under contrary plane centrality, the original conjugate span lies in the
omega-center of the complete point core. Its actual component moves this
span, so the component is faithful. The original flag point and the two
maximal normalizers give Thompson generation. The component supplement then
places the span in R₂(H). Its original point is a nonzero fixed vector in
the reduced commutator, to which the B.5 chosen-module construction applies.

All groups here are the original subgroups. No natural-module clause or
chosen-module hypothesis on the selected component is assumed.
Source: Aschbacher--Smith 13.3.14(a),(e--g), printed pp.891--893, and
14.7.48, printed p.1064.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.LinearThreeSource
open Chapter12.Section08 CriticalFusion.Source WholeResidualAssembly
open Chapter12.Section02 ChapterA.Section04
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open Chapter14.Section04.LargerDimension.LocalAction.Components
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

/-- Contrary centrality constructs a chosen module on the actual reduced
commutator, retaining its nonzero original fixed point and faithful actor. -/
theorem original_point_chosen_of_plane_centralized_at
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (source47 : Earlier14747 F L)
    (C : Subgroup F.H) (hC : C.IsCComponent)
    (hc : ⁅F.Vi 2,F.H.pCoreIn 2⁆ = ⊥) :
    let B := C.map F.H.subtype
    let W := ⁅(reducedTwoSubgroup F.H).map F.H.subtype,B⁆
    B ∈ MainForward.faithfulLocalComponents T ∧
      W ⊓ centralizer (B : Set G) ≠ ⊥ ∧ Nonempty (ChosenModule T B W) := by
  let := h.chosen.elementary
  let := hab
  let := elementary_U F
  let B := C.map F.H.subtype
  let W := ⁅(reducedTwoSubgroup F.H).map F.H.subtype,B⁆
  have hH := h.point_mem_Hz_at F previous
  obtain ⟨_,hgen,hm⟩ := local_component_eq_residual_at d h hab structural previous
    faithful earlier source47 F.H hH C hC
  change B ⊔ (T : Subgroup G) = F.H at hgen
  change ⁅F.U,B⁆ = F.U at hm
  let := local_component_normal_at h structural source47 F.H hH C hC
  let := local_component_twoCore_of_earlier14747 source47 F.H hH C hC
  have hBH : B ≤ F.H := map_subtype_le _
  have hBC : (B.subgroupOf F.H).IsCComponent := by
    simpa only [B,subgroupOf,comap_map_eq_self_of_injective F.H.subtype_injective] using hC
  have hn : (B.subgroupOf F.H).Normal := by
    simpa only [B,subgroupOf,comap_map_eq_self_of_injective F.H.subtype_injective] using
      (inferInstance : C.Normal)
  have hHN : F.H ≤ normalizer (B : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hBH).mp hn
  have hTH : (T : Subgroup G) ≤ F.H := F.invariant 1
  have hpCard : Nat.card (F.Vi 1) = 2 := by simpa using F.card 1 (by decide)
  have hp : F.Vi 1 ≠ ⊥ := by intro he; simp [he] at hpCard
  have hpU : F.Vi 1 ≤ F.U := (F.le_seed 1).trans (le_conjugateSpanBy V F.H)
  have hUne : F.U ≠ ⊥ := fun he => hp (le_bot_iff.mp (hpU.trans_eq he))
  have htwo : IsTwoLocal F.H := ⟨F.Vi 1,hp,
    T.isPGroup'.to_le ((F.le_seed 1).trans h.chosen.le_sylow),rfl⟩
  have hHe : F.H ∈ Chapter1.He G := Chapter1.twoLocal_mem_He_of_sylow_le T
    (h.source.simpleQTKE.toIsQTKE.evenCharacteristic T) htwo hTH
  have hω := original_point_span_le_omega_of_plane_centralized h hc
  have hωmap : (omegaOneCenterAmbient (pCore 2 F.H)).map F.H.subtype =
      omegaOneCenterAmbient (F.H.pCoreIn 2) :=
    (omegaOneCenterAmbient_map_injective F.H.subtype F.H.subtype_injective _).symm
  have hUi : F.U.subgroupOf F.H ≤ omegaOneCenterAmbient (pCore 2 F.H) := by
    intro a ha
    have hh := hω ha
    rw [←hωmap] at hh
    obtain ⟨b,hb,he⟩ := hh
    exact (F.H.subtype_injective he) ▸ hb
  have hmi : ⁅F.U.subgroupOf F.H,C⁆ ≠ ⊥ := by
    intro he
    have hh := congrArg (Subgroup.map F.H.subtype) he
    rw [map_commutator,map_subgroupOf_eq_of_le F.U_le_H,Subgroup.map_bot] at hh
    exact hUne (hm.symm.trans hh)
  obtain ⟨hBL,hBf⟩ := Chapter13.Section03.Noncentrality.source_component_faithful_local
    T F.H hTH (Chapter1.mem_H_of_isTwoLocal htwo) hHe C _ hC hUi hmi
  have hf : B ∈ MainForward.faithfulLocalComponents T :=
    (Chapter1.Section02.Adequate.mem_faithfulLocalComponents_iff T B).mpr ⟨hBL,hBf⟩
  have hstar := (faithful B hBL hBf).2.2
  have hTB : (T : Subgroup G) ≤ normalizer (B : Set G) := hTH.trans hHN
  have horb : componentOrbit B (T : Subgroup G) = B :=
    le_antisymm (iSup_conjugates_le_of_le_normalizer B _ B le_rfl hTB)
      (le_componentOrbit B _)
  have hmax : IsMaximalTwoLocal (normalizer (B : Set G)) := by
    rw [←horb]
    exact (Chapter1.Section02.nonsolvable_uniqueness_knownSimple
      h.source.simpleQTKE T hstar).normalizer_maximal
  have hTh : ⁅B,elementaryAbelianMaxJ (T : Subgroup G)⁆ = B :=
    Chapter13.Section03.SourceCompletion.unitary_component_thompson_generation
      h.source.simpleQTKE T (F.Vi 1) F.H (normalizer (L : Set G))
      ((F.le_seed 1).trans h.chosen.le_sylow) hpCard (F.invariant 1) rfl C
      inferInstance hf hstar hHN hmax (h.maximal_unique_at structural).1
      (h.sylow_normalizes_at structural)
      (local_component_not_le_normalizer_at h structural F.H hH C hC)
  let : IsElementaryAbelian 2 (F.U.subgroupOf F.H) :=
    IsElementaryAbelian.subgroupOf F.U_le_H
  let : (F.U.subgroupOf F.H).Normal :=
    normal_subgroupOf_of_le_normalizer (le_normalizer_conjugateSpanBy V F.H)
  have hgeni : C ⊔ (T : Subgroup G).subgroupOf F.H = ⊤ := by
    apply map_injective F.H.subtype_injective
    rw [Subgroup.map_sup,map_subgroupOf_eq_of_le hTH,
      ←MonoidHom.range_eq_map,range_subtype]
    exact hgen
  have hQC : pCore 2 F.H ≤ centralizer (F.U.subgroupOf F.H : Set F.H) := by
    intro q hq
    apply mem_centralizer_iff.mpr
    intro a ha
    exact (((mem_omegaOneCenterAmbient_iff _ _).mp (hUi ha)).2.2 q hq).symm
  have hUR : F.U ≤ (reducedTwoSubgroup F.H).map F.H.subtype := by
    have hh := seed_le_reduced_of_component_supplement C
      ((T : Subgroup G).subgroupOf F.H) (F.U.subgroupOf F.H) (F.U.subgroupOf F.H)
      hC T.isPGroup'.comap_subtype hgeni le_rfl hQC hmi
    have hm := map_mono (f := F.H.subtype) hh
    rwa [map_subgroupOf_eq_of_le F.U_le_H] at hm
  have hUW : F.U ≤ W := by
    rw [←hm]
    exact commutator_mono hUR le_rfl
  have hpC : F.Vi 1 ≤ centralizer (B : Set G) := by
    apply le_centralizer_iff.mp
    exact hBH.trans (normalizer_le_centralizer_of_card_two (F.Vi 1) hpCard)
  have hfixed : W ⊓ centralizer (B : Set G) ≠ ⊥ := by
    intro he
    exact hp (le_bot_iff.mp ((le_inf (hpU.trans hUW) hpC).trans_eq he))
  let e := C.equivMapOfInjective F.H.subtype F.H.subtype_injective
  have hqB : IsQuasisimple (B ⧸ pCore 2 B) := IsQuasisimple.of_mulEquiv
    (QuotientGroup.congr _ _ e (pCore_map_iso 2 e))
  exact ⟨hf,hfixed,chosen_moved_of_thompson_component F.H B
    (h.source.simpleQTKE.twoLocal_sqtk htwo) hTH hBH hHN hBC hqB hBf.2
    hgen.symm hTh hfixed⟩

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.LinearThreeSource
