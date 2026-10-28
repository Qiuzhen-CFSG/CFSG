module
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.IntrinsicOvergroupFF
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.OvergroupSelectedFieldFour
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.OvergroupFullyMoved
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.TensorPlaneMoved

/-!
# Original tensor-overgroup action models

For the original tensor setup, the old residual's proper local A₅ image
restricts the B.5 classification of the new overgroup action. The tensor
plane generates the omega orbit under commutators, while the old residual
fixes the actual Sylow omega center. These two facts exclude both A₇ rows
and leave the four linear, repeated linear, symplectic and G₂ models.
The same proper local A₅ image forces the defining field to have order four.

The old residual's A₅ recognition and its centralization and movement
hypotheses remain explicit earlier source inputs. The nonzero-core version
derives the stabilizer Sylow property from the original overgroup theorem.
All quotient maps and the offender action are the literal ones.

Source: Aschbacher–Smith, 9.3.6–9.3.7, printed pp.733–734.
-/

public section

open Subgroup Theory.GroupTheory Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter10.SourceA5TensorModel
open Chapter3.Section02 ChapterC.MSCentralOrbit ChapterB.InternalThompsonAction ChapterA.Section03
open Representation Representation.BinaryOffender
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)}
  (m : SourceA5TensorModel D e)

theorem old_residual_overgroup_fourField_models
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (houtside : Chapter3.HasMaximalOutside T D.maximalLocal)
    (hcomm : ⁅omegaCenterIn ((localJoin T L).pCoreIn 2), localOrbit T L⁆ ≤ D.fullModule)
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (eK : ((pResidual 2 H).map H.subtype ⧸
      pCore 2 ((pResidual 2 H).map H.subtype)) ≃* alternatingGroup (Fin 5))
    (hSyl : Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ normalizer (L : Set G))
      ((pResidual 2 H).map H.subtype ⊔ ((T : Subgroup G) ⊓ normalizer (L : Set G))))
    (M₀ : Subgroup G) (hcore : pCore 2 M₀ ≠ ⊥)
    (hgen : M₀ = (L ⊔ (pResidual 2 H).map H.subtype) ⊔
      ((T : Subgroup G) ⊓ normalizer (L : Set G)))
    (hKU : (pResidual 2 H).map H.subtype ≤ centralizer (m.tensorLine : Set G))
    (hmove : ¬ (pResidual 2 H).map H.subtype ≤ centralizer (m.tensorPlane : Set G)) :
    m.tensorLine ≤ M₀.pCoreIn 2 ∧ M₀ ∈ Chapter1.He G ∧
      generalizedFitting M₀ = pCore 2 M₀ ∧ center M₀ = ⊥ ∧
    let R := ((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf M₀
    let W := omegaOrbit R
    ∃ hr : IsPReduced 2 W,
      letI := hr.normal; letI := hr.elementary
      let ρ : Representation (ZMod 2) (ActionQuotient W) (Additive W) := action W
      let N := offenderSubgroup ρ
      m.tensorLine.subgroupOf M₀ ≤ W ∧
      (pResidual 2 M₀).map (actionMk W) ≤ N ∧
      ChapterB.QuasisimpleSource.moved (ρ.comp N.subtype)
        (((pResidual 2 M₀).map (actionMk W)).subgroupOf N) = ⊤ ∧
      ∃ h : ChapterB.SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion
        (ρ.comp N.subtype) (((pResidual 2 M₀).map (actionMk W)).subgroupOf N),
      SourceA5TensorExclusion.FourWayFourField (ρ.comp N.subtype)
        (((pResidual 2 M₀).map (actionMk W)).subgroupOf N) h.sectionData := by
  obtain ⟨hU,hHe,hF,hZ,hr,hUW,hsource⟩ := m.old_residual_overgroup_core_and_ff_intrinsic
    hn houtside hcomm hH eK hSyl M₀ hcore hgen hKU hmove
  refine ⟨hU,hHe,hF,hZ,hr,hUW,?_⟩
  let W := omegaOrbit (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf M₀)
  let := hr.normal
  let := hr.elementary
  let B := (pResidual 2 H).map H.subtype
  let R := (T : Subgroup G) ⊓ normalizer (L : Set G)
  have hLH : L ≤ M₀ := hgen ▸ le_sup_of_le_left le_sup_left
  have hBH : B ≤ M₀ := hgen ▸ le_sup_of_le_left le_sup_right
  have hRH : R ≤ M₀ := hgen ▸ le_sup_right
  have hUH : m.tensorLine ≤ M₀ := hU.trans (map_subtype_le _)
  have hVH : m.tensorPlane ≤ M₀ := iSup_conjugates_le_of_le_normalizer
    m.tensorLine L M₀ hUH (hLH.trans M₀.le_normalizer)
  have hout : ¬ M₀ ≤ D.maximalLocal := fun hm =>
    source_hstar_residual_not_le (le_normalizer_componentOrbit L T) hH (hBH.trans hm)
  obtain ⟨hK,hLK,hBK,hprod⟩ := m.old_residual_component_product hn hH eK hSyl
    M₀ hcore hgen hKU hmove
  obtain ⟨P,hP⟩ := source_a5_local_outside_overgroup_sylow D e hn hcore hLH hRH hout
  have hPR : (P : Subgroup M₀) = R.subgroupOf M₀ := by
    apply map_injective M₀.subtype_injective
    rw [hP,map_subgroupOf_eq_of_le hRH]
  have hKP : pResidual 2 M₀ ⊔ (P : Subgroup M₀) = ⊤ := by
    apply top_unique
    intro g _
    obtain ⟨k,hk,r,hr,rfl⟩ := hprod g
    exact mul_mem_sup hk (hPR ▸ hr)
  have hBlocal : B.subgroupOf M₀ ∈ localCComponents P := by
    rw [hPR]
    exact ChapterA.Section03.SourceEmbeddings.local_restrict
      (m.old_residual_mem_local_at_stabilizer hn hH eK hSyl).1 hBH
  let b : B.subgroupOf M₀ ≃* B := subgroupOfEquivOfLe hBH
  let eB : (B.subgroupOf M₀ ⧸ pCore 2 (B.subgroupOf M₀)) ≃* alternatingGroup (Fin 5) :=
    (QuotientGroup.congr _ _ b (pCore_map_iso 2 b)).trans eK
  have hBU : B.subgroupOf M₀ ≤ centralizer (m.tensorLine.subgroupOf M₀ : Set M₀) := by
    intro b hb u hu
    exact Subtype.ext (hKU hb u hu)
  have horbit : (componentOrbit (m.tensorLine.subgroupOf M₀) (L.subgroupOf M₀)).map M₀.subtype =
      m.tensorPlane := by
    rw [map_componentOrbit,map_subgroupOf_eq_of_le hUH,map_subgroupOf_eq_of_le hLH]
    rfl
  have hVW : m.tensorPlane.subgroupOf M₀ ≤ W := by
    have h := iSup_conjugates_le_of_le_normalizer
      (m.tensorLine.subgroupOf M₀) (L.subgroupOf M₀) W hUW le_normalizer_of_normal
    have he : componentOrbit (m.tensorLine.subgroupOf M₀) (L.subgroupOf M₀) =
        m.tensorPlane.subgroupOf M₀ := map_injective M₀.subtype_injective
      (horbit.trans (map_subgroupOf_eq_of_le hVH).symm)
    exact he ▸ h
  have hmoveB : ¬ B.subgroupOf M₀ ≤ centralizer
      (componentOrbit (m.tensorLine.subgroupOf M₀) (L.subgroupOf M₀) : Set M₀) := by
    intro hc
    apply hmove
    intro b hb w hw
    obtain ⟨w',hw',rfl⟩ := horbit ▸ hw
    exact congrArg M₀.subtype (hc (show (⟨b,hBH hb⟩ : M₀) ∈ B.subgroupOf M₀ from hb) w' hw')
  have hmoveL : ¬ L.subgroupOf M₀ ≤ centralizer (m.tensorLine.subgroupOf M₀ : Set M₀) := by
    intro hc
    have hfixed : m.tensorLine ≤ centralizer (L : Set G) := by
      intro u hu l hl
      exact (congrArg M₀.subtype
        (hc (show (⟨l,hLH hl⟩ : M₀) ∈ L.subgroupOf M₀ from hl) ⟨u,hUH hu⟩ hu)).symm
    exact m.tensorLine_ne_bot (le_bot_iff.mp
      (m.fullModule_component_fixed_eq_bot ▸ (le_inf m.tensorLine_le_fullModule hfixed)))
  have hBC : B.subgroupOf M₀ = ⁅B.subgroupOf M₀,elementaryAbelianMaxJ (P : Subgroup M₀)⁆ := by
    apply map_injective M₀.subtype_injective
    rw [map_commutator,map_subgroupOf_eq_of_le hBH,
      ←elementaryAbelianMaxJ_map_injective M₀.subtype M₀.subtype_injective,hP]
    rw [m.thompson_stabilizer_eq]
    exact m.old_residual_eq_thompson_commutator hH eK
  have hH0 : IsSQTK KnownSimple.IsKnownSimple M₀ := by
    obtain ⟨M,hM,hHM⟩ := exists_maximalTwoLocal_overgroup_of_twoCore_ne_bot M₀ hcore
    have hs := D.simpleQTKE.twoLocal_sqtk hM.1
    exact ⟨hs.stronglyQuasithin.of_injective (inclusion hHM) (inclusion_injective hHM),
      hs.isKGroup.of_injective (inclusion hHM) (inclusion_injective hHM)⟩
  obtain ⟨hKN,_,h,hsix⟩ := source_tensor_overgroup_six_models hH0 P (pResidual 2 M₀)
    (B.subgroupOf M₀) (L.subgroupOf M₀) (m.tensorLine.subgroupOf M₀) W hK hKP
    hBlocal hBK hLK eB hr hUW hBU hmoveB hmoveL hBC
  have hOmega : omegaCenterIn (P : Subgroup M₀) ≤ m.tensorLine.subgroupOf M₀ := by
    have hmap : (omegaCenterIn (P : Subgroup M₀)).map M₀.subtype = omegaCenterIn R := by
      change (omegaOneCenterAmbient (P : Subgroup M₀)).map M₀.subtype = omegaOneCenterAmbient R
      rw [←omegaOneCenterAmbient_map_injective M₀.subtype M₀.subtype_injective,hP]
    intro x hx
    exact m.omegaCenter_stabilizer_le_tensorLine hn houtside hcomm
      (hmap ▸ mem_map_of_mem M₀.subtype hx)
  have hVL : ⁅m.tensorPlane.subgroupOf M₀,L.subgroupOf M₀⁆ = m.tensorPlane.subgroupOf M₀ := by
    apply map_injective M₀.subtype_injective
    rw [map_commutator,map_subgroupOf_eq_of_le hVH,map_subgroupOf_eq_of_le hLH]
    exact m.tensorPlane_component_commutator
  have hRV : omegaCenterIn (R.subgroupOf M₀) ≤ m.tensorPlane.subgroupOf M₀ := by
    rw [←hPR]
    exact hOmega.trans (comap_mono (le_componentOrbit m.tensorLine L))
  have hm := source_tensor_omegaOrbit_offender_action_fully_moved
    (R.subgroupOf M₀) (m.tensorPlane.subgroupOf M₀) (L.subgroupOf M₀)
    (pResidual 2 M₀) hRV hVW hLK hVL hr hKN
  obtain ⟨_,_,h,hfour⟩ := source_tensor_overgroup_fourField_models hH0 P (pResidual 2 M₀)
    (B.subgroupOf M₀) (L.subgroupOf M₀) (m.tensorLine.subgroupOf M₀) W hK hKP
    hBlocal hBK hLK eB hr hUW hBU hmoveB hmoveL hBC
    (hBU.trans (centralizer_le hOmega)) hm
  exact ⟨hKN,hm,h,hfour⟩
/-- Once the new overgroup has nontrivial two-core, its proved Sylow theorem
supplies the old residual's required relative Sylow marking by restriction. -/
theorem old_residual_overgroup_fourField_models_of_nonzero_core
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (houtside : Chapter3.HasMaximalOutside T D.maximalLocal)
    (hcomm : ⁅omegaCenterIn ((localJoin T L).pCoreIn 2), localOrbit T L⁆ ≤ D.fullModule)
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (eK : ((pResidual 2 H).map H.subtype ⧸
      pCore 2 ((pResidual 2 H).map H.subtype)) ≃* alternatingGroup (Fin 5))
    (M₀ : Subgroup G) (hcore : pCore 2 M₀ ≠ ⊥)
    (hgen : M₀ = (L ⊔ (pResidual 2 H).map H.subtype) ⊔
      ((T : Subgroup G) ⊓ normalizer (L : Set G)))
    (hKU : (pResidual 2 H).map H.subtype ≤ centralizer (m.tensorLine : Set G))
    (hmove : ¬ (pResidual 2 H).map H.subtype ≤ centralizer (m.tensorPlane : Set G)) :
    m.tensorLine ≤ M₀.pCoreIn 2 ∧ M₀ ∈ Chapter1.He G ∧
      generalizedFitting M₀ = pCore 2 M₀ ∧ center M₀ = ⊥ ∧
    let R := ((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf M₀
    let W := omegaOrbit R
    ∃ hr : IsPReduced 2 W,
      letI := hr.normal; letI := hr.elementary
      let ρ : Representation (ZMod 2) (ActionQuotient W) (Additive W) := action W
      let N := offenderSubgroup ρ
      m.tensorLine.subgroupOf M₀ ≤ W ∧
      (pResidual 2 M₀).map (actionMk W) ≤ N ∧
      ChapterB.QuasisimpleSource.moved (ρ.comp N.subtype)
        (((pResidual 2 M₀).map (actionMk W)).subgroupOf N) = ⊤ ∧
      ∃ h : ChapterB.SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion
        (ρ.comp N.subtype) (((pResidual 2 M₀).map (actionMk W)).subgroupOf N),
      SourceA5TensorExclusion.FourWayFourField (ρ.comp N.subtype)
        (((pResidual 2 M₀).map (actionMk W)).subgroupOf N) h.sectionData := by
  have hLH : L ≤ M₀ := hgen ▸ le_sup_of_le_left le_sup_left
  have hBH : (pResidual 2 H).map H.subtype ≤ M₀ := hgen ▸ le_sup_of_le_left le_sup_right
  have hRH : (T : Subgroup G) ⊓ normalizer (L : Set G) ≤ M₀ := hgen ▸ le_sup_right
  have hout : ¬ M₀ ≤ D.maximalLocal := fun hm =>
    source_hstar_residual_not_le (le_normalizer_componentOrbit L T) hH (hBH.trans hm)
  have hSyl := (source_a5_local_outside_overgroup_sylow D e hn hcore hLH hRH hout).restrict
    le_sup_right (sup_le hBH hRH)
  exact m.old_residual_overgroup_fourField_models hn houtside hcomm hH eK hSyl M₀ hcore hgen hKU hmove


theorem old_residual_overgroup_four_models
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (houtside : Chapter3.HasMaximalOutside T D.maximalLocal)
    (hcomm : ⁅omegaCenterIn ((localJoin T L).pCoreIn 2), localOrbit T L⁆ ≤ D.fullModule)
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (eK : ((pResidual 2 H).map H.subtype ⧸
      pCore 2 ((pResidual 2 H).map H.subtype)) ≃* alternatingGroup (Fin 5))
    (hSyl : Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ normalizer (L : Set G))
      ((pResidual 2 H).map H.subtype ⊔ ((T : Subgroup G) ⊓ normalizer (L : Set G))))
    (M₀ : Subgroup G) (hcore : pCore 2 M₀ ≠ ⊥)
    (hgen : M₀ = (L ⊔ (pResidual 2 H).map H.subtype) ⊔
      ((T : Subgroup G) ⊓ normalizer (L : Set G)))
    (hKU : (pResidual 2 H).map H.subtype ≤ centralizer (m.tensorLine : Set G))
    (hmove : ¬ (pResidual 2 H).map H.subtype ≤ centralizer (m.tensorPlane : Set G)) :
    m.tensorLine ≤ M₀.pCoreIn 2 ∧ M₀ ∈ Chapter1.He G ∧
      generalizedFitting M₀ = pCore 2 M₀ ∧ center M₀ = ⊥ ∧
    let R := ((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf M₀
    let W := omegaOrbit R
    ∃ hr : IsPReduced 2 W,
      letI := hr.normal; letI := hr.elementary
      let ρ : Representation (ZMod 2) (ActionQuotient W) (Additive W) := action W
      let N := offenderSubgroup ρ
      m.tensorLine.subgroupOf M₀ ≤ W ∧
      ∃ h : ChapterB.SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion
        (ρ.comp N.subtype) (((pResidual 2 M₀).map (actionMk W)).subgroupOf N),
      SourceA5TensorExclusion.FourWay (ρ.comp N.subtype)
        (((pResidual 2 M₀).map (actionMk W)).subgroupOf N) h.sectionData := by
  obtain ⟨hU,hHe,hF,hZ,hr,hUW,_,_,h,hm⟩ := m.old_residual_overgroup_fourField_models
    hn houtside hcomm hH eK hSyl M₀ hcore hgen hKU hmove
  let := hr.normal
  let := hr.elementary
  exact ⟨hU,hHe,hF,hZ,hr,hUW,h,hm.toFourWay⟩

theorem old_residual_overgroup_four_models_of_nonzero_core
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (houtside : Chapter3.HasMaximalOutside T D.maximalLocal)
    (hcomm : ⁅omegaCenterIn ((localJoin T L).pCoreIn 2), localOrbit T L⁆ ≤ D.fullModule)
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (eK : ((pResidual 2 H).map H.subtype ⧸
      pCore 2 ((pResidual 2 H).map H.subtype)) ≃* alternatingGroup (Fin 5))
    (M₀ : Subgroup G) (hcore : pCore 2 M₀ ≠ ⊥)
    (hgen : M₀ = (L ⊔ (pResidual 2 H).map H.subtype) ⊔
      ((T : Subgroup G) ⊓ normalizer (L : Set G)))
    (hKU : (pResidual 2 H).map H.subtype ≤ centralizer (m.tensorLine : Set G))
    (hmove : ¬ (pResidual 2 H).map H.subtype ≤ centralizer (m.tensorPlane : Set G)) :
    m.tensorLine ≤ M₀.pCoreIn 2 ∧ M₀ ∈ Chapter1.He G ∧
      generalizedFitting M₀ = pCore 2 M₀ ∧ center M₀ = ⊥ ∧
    let R := ((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf M₀
    let W := omegaOrbit R
    ∃ hr : IsPReduced 2 W,
      letI := hr.normal; letI := hr.elementary
      let ρ : Representation (ZMod 2) (ActionQuotient W) (Additive W) := action W
      let N := offenderSubgroup ρ
      m.tensorLine.subgroupOf M₀ ≤ W ∧
      ∃ h : ChapterB.SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion
        (ρ.comp N.subtype) (((pResidual 2 M₀).map (actionMk W)).subgroupOf N),
      SourceA5TensorExclusion.FourWay (ρ.comp N.subtype)
        (((pResidual 2 M₀).map (actionMk W)).subgroupOf N) h.sectionData := by
  obtain ⟨hU,hHe,hF,hZ,hr,hUW,_,_,h,hm⟩ := m.old_residual_overgroup_fourField_models_of_nonzero_core
    hn houtside hcomm hH eK M₀ hcore hgen hKU hmove
  let := hr.normal
  let := hr.elementary
  exact ⟨hU,hHe,hF,hZ,hr,hUW,h,hm.toFourWay⟩


end CFSG.Quasithin.Chapter10.SourceA5TensorModel
