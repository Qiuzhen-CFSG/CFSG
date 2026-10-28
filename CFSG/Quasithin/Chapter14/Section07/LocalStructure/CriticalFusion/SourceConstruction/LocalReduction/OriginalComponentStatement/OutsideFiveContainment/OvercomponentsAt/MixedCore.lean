module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.OriginalComponentStatement.OutsideFiveContainment.OvercomponentsAt.Maximality
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.InnerLinearExclusion.MiddleQuotient
public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.LocalAction.NaturalFlags.Construction
public import Theory.GroupTheory.UniqueLocalResidualKernel

/-!
# The nonzero-core contradiction for the original mixed group

Source 1.2.4 constructs a normal overcomponent of the literal full-point
component in G₀. Faithful local rigidity and uniqueness in the point
stabilizer force equality. The original plane closure and Sylow generate
the plane parabolic, so both original rank-one residuals normalize this
component. Their generation of L contradicts the unique maximal two-local
over LT and the component's original escape from N_G(L).
Source: Aschbacher–Smith 14.7.46, printed p.1063.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.OriginalComponentStatement.OutsideFiveContainment.OvercomponentsAt
open Chapter12.Section08 Chapter12.Section09.NaturalSource CriticalFusion.Source
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open Chapter14.Section04.LargerDimension.LocalAction
open Chapter14.Section04.LargerDimension.LocalAction.Components
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

private theorem natural_action_at
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T) :
    NaturalThreeAction L V T := by
  refine ⟨?_,h.sylow_normalizes_at structural,h.chosen.normalizes,?_,?_⟩
  · change (pResidual 2 L).map L.subtype = L
    rw [h.residual,←MonoidHom.range_eq_map,range_subtype]
  · intro a
    obtain ⟨l,hl,he⟩ := h.full_L_action a
    refine ⟨⟨l,hl⟩,?_⟩
    ext v
    rw [Chapter14.Section04.LargerDimension.LocalAction.conjugation_apply]
    exact he v
  · rw [conjugation_ker]
    apply map_injective L.subtype_injective
    simpa only [subgroupOf_map_subtype,inf_comm,pCoreIn] using h.centralizer_L

/-- The literal component–plane-closure–Sylow group has trivial two-core
when the original point core moves the plane. Every overcomponent is constructed. -/
theorem full_point_component_mixed_core_eq_bot_of_plane_moved_at
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (C : Subgroup F.H) (hC : C.IsCComponent) [C.Normal]
    (hm : ⁅F.Vi 2,F.H.pCoreIn 2⁆ ≠ ⊥) :
    pCore 2 (C.map F.H.subtype ⊔ planeCoreClosure F ⊔ (T : Subgroup G) : Subgroup G) = ⊥ := by
  let K := C.map F.H.subtype
  let G₀ := K ⊔ planeCoreClosure F ⊔ (T : Subgroup G)
  by_contra hcore
  have hc : G₀.pCoreIn 2 ≠ ⊥ := by
    intro he
    exact hcore ((map_eq_bot_iff_of_injective _ G₀.subtype_injective).mp he)
  have hKG : K ≤ G₀ := le_sup_left.trans le_sup_left
  have hTG : (T : Subgroup G) ≤ G₀ := le_sup_right
  have hn := full_point_component_normal_in_overgroup_at d h previous faithful C hC hKG hTG hc
  have hGK : G₀ ≤ normalizer (K : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hKG).mp hn
  have hnC : (K.subgroupOf F.H).Normal := by
    simpa only [K,subgroupOf,comap_map_eq_self_of_injective F.H.subtype_injective] using
      (inferInstance : C.Normal)
  have hHK : F.H ≤ normalizer (K : Set G) :=
    (normal_subgroupOf_iff_le_normalizer (map_subtype_le C)).mp hnC
  have hP : F.P L ≤ G₀ := by
    rw [←InnerLinearExclusion.plane_core_closure_sup_sylow_at h structural
      hm]
    exact sup_le (le_sup_right.trans le_sup_left) le_sup_right
  have hL₂P : F.Li L 2 ≤ F.P L := by
    apply (F.Li_le L 2).trans
    intro x hx
    exact ⟨mem_sup_left hx.1,mem_iInf.mpr fun i => mem_iInf.mpr fun hi => by
      have : i = 2 := by omega
      subst i
      exact hx.2⟩
  have hLTK : L ⊔ (T : Subgroup G) ≤ normalizer (K : Set G) := by
    let := h.chosen.elementary
    have hg := (NaturalFlags.naturalFlagData_of_invariant_flag
      (natural_action_at h structural) F 1 (one_mem L)).generated
    rw [←hg]
    exact sup_le (sup_le (((F.Li_le L 1).trans inf_le_right).trans hHK)
      ((hL₂P.trans hP).trans hGK)) (hTG.trans hGK)
  have hH := F.H_mem_Hz (by decide) L _ (h.flag_escape_at F previous)
  have hout : ¬ G₀ ≤ normalizer (L : Set G) := fun he =>
    local_component_not_le_normalizer_at h structural F.H hH C hC (hKG.trans he)
  have hself : G₀ ⊓ centralizer (G₀.pCoreIn 2 : Set G) ≤ G₀.pCoreIn 2 :=
    Chapter1.lemma_1_1_4_6 T (d.qtke.evenCharacteristic T) ⟨hc,hTG⟩
  have hb : K = ⊥ := normal_eq_bot_of_unique_core (L ⊔ (T : Subgroup G)) G₀
    (normalizer (L : Set G)) K (by
      intro N hN hLN
      exact Set.mem_singleton_iff.mp ((h.maximal_unique_at structural).2 ▸
        show N ∈ {N : Subgroup G | IsMaximalTwoLocal N ∧ L ⊔ (T : Subgroup G) ≤ N}
          from ⟨hN,hLN⟩)) hout hself hKG hGK hLTK
  exact hC.ne_bot ((map_eq_bot_iff_of_injective _ F.H.subtype_injective).mp hb)

/-- The existing full-point-normality producer supplies the required movement. -/
theorem full_point_component_mixed_core_eq_bot_at
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (C : Subgroup F.H) (hC : C.IsCComponent) [C.Normal]
    (hpoint : ((F.Li L 1).subgroupOf F.H).Normal) :
    pCore 2 (C.map F.H.subtype ⊔ planeCoreClosure F ⊔ (T : Subgroup G) : Subgroup G) = ⊥ :=
  full_point_component_mixed_core_eq_bot_of_plane_moved_at d h structural previous faithful C hC
    (plane_moved_of_point_normal_at h structural hpoint)

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.OriginalComponentStatement.OutsideFiveContainment.OvercomponentsAt
