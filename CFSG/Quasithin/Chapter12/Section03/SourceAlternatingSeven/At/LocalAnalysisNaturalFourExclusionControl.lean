module

public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.LocalAnalysisNaturalFourExclusionControl
public import CFSG.Quasithin.Chapter12.Section02.StructuralSource.At
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.At.LocalAnalysisNaturalFourExclusionFaithful

/-!
# LocalAnalysisNaturalFourExclusionControl at the original ambient group and Sylow subgroup

These are the same source arguments as `LocalAnalysisNaturalFourExclusionControl`, with structural
12.2.2 and its module alternatives restricted to the original G,T. Every
chosen subgroup, central quotient, action and relative normality statement
is retained. Independent definitions and lemmas are imported unchanged.
The universal statements remain available from the original module.

Source: Aschbacher–Smith, 12.3.1–13, printed pp.807–812.
-/

public noncomputable section

open Subgroup Theory.GroupTheory

open scoped IsMulCommutative

namespace CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven

open Section02

universe u

variable {G : Type u} [Group G] [Finite G]

variable {T : Sylow 2 G} {L V : Subgroup G}

namespace Setup

variable (S : Setup T L V)

include S

omit S [Finite G] in

private theorem module_kernel_of_simple_core_at
    (X W : Subgroup G) (hn : X ≤ normalizer (W : Set G))
    (hc : X.pCoreIn 2 ≤ centralizer (W : Set G))
    (hm : ⁅W,X⁆ ≠ ⊥) [IsSimpleGroup (X ⧸ pCore 2 X)] :
    X ⊓ centralizer (W : Set G) = X.pCoreIn 2 := by
  let C := (centralizer (W : Set G)).subgroupOf X
  let : C.Normal := normal_subgroupOf_of_le_normalizer
    (hn.trans (normalizer_le_normalizer_centralizer W))
  let q := QuotientGroup.mk' (pCore 2 X)
  have hpc : pCore 2 X ≤ C := fun x hx => hc (mem_map_of_mem X.subtype hx)
  have hnq : (C.map q).Normal := (inferInstance : C.Normal).map q
    (QuotientGroup.mk'_surjective _)
  have hC : C ≤ pCore 2 X := by
    rcases hnq.eq_bot_or_eq_top with hb | ht
    · simpa only [q, QuotientGroup.ker_mk'] using (map_eq_bot_iff C).mp hb
    · have htC : C = ⊤ := by
        have hh := congrArg (comap q) ht
        simpa only [comap_map_eq, q, QuotientGroup.ker_mk', sup_eq_left.mpr hpc,
          comap_top] using hh
      apply False.elim
      apply hm
      rw [commutator_comm]
      apply commutator_eq_bot_iff_le_centralizer.mpr
      intro x hx
      exact htC.ge (mem_top (⟨x,hx⟩ : X))
  apply le_antisymm ?_ (le_inf (pCoreIn_le 2 X) hc)
  intro x hx
  exact mem_map_of_mem X.subtype (hC (show (⟨x,hx.1⟩ : X) ∈ C from hx.2))

private theorem point_quotient_simple_at {z : G}
    (quotient : ClassicalGroup.IsPSL
      ((S.fourPointPerfect z) ⧸ pCore 2 (S.fourPointPerfect z)) 3 2) :
    IsSimpleGroup ((S.fourPointPerfect z) ⧸ pCore 2 (S.fourPointPerfect z)) := by
  obtain ⟨F, hF, hfin, _, ⟨f⟩⟩ := quotient
  let := Atlas.psl_simple_high_rank (F := F) 3 (by decide)
  exact f.isSimpleGroup

private theorem point_quotient_quasisimple_at {z : G}
    (quotient : ClassicalGroup.IsPSL
      ((S.fourPointPerfect z) ⧸ pCore 2 (S.fourPointPerfect z)) 3 2) :
    IsQuasisimple ((S.fourPointPerfect z) ⧸ pCore 2 (S.fourPointPerfect z)) := by
  obtain ⟨F, hF, hfin, _, ⟨f⟩⟩ := quotient
  let := Theory.SpecificGroups.LinearHigher.psl_isQuasisimple (F := F) (n := 3) (by decide)
  exact IsQuasisimple.of_mulEquiv f.symm

theorem chosen_sylowCentralizer_eq_core_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T) :
    (T : Subgroup G) ⊓ centralizer (V : Set G) = (L ⊔ (T : Subgroup G)).pCoreIn 2 := by
  have hu := Chapter1.Section02.nonsolvable_uniqueness_of_theoremsAC
    (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
    (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple)
    S.hypothesis.simpleQTKE T S.hypothesis.maximal_faithful.1
  have hm : (S.chosen.fundamentalSetup S.hypothesis.toHypothesis1221).moduleSubgroup = V := by
    rw [S.chosen.fundamentalSetup_module]
    exact le_antisymm
      (iSup_conjugates_le_of_le_normalizer V (T : Subgroup G) V le_rfl
        ((structural L S.hypothesis).2.2 V S.chosen).1)
      (le_componentOrbit V (T : Subgroup G))
  have hh := (S.chosen.fundamentalSetup S.hypothesis.toHypothesis1221).sylow_centralizer_module hu
  rw [hm] at hh
  simpa only [Chapter3.Section02.localJoin, S.chosen.localOrbit_eq] using hh

theorem chosen_core_characteristicControl_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T) :
    ((L ⊔ (T : Subgroup G)).pCoreIn 2).characteristicNormalizerClosure ≤
      normalizer (L : Set G) := by
  apply characteristicNormalizerClosure_le_of_unique_maximalTwoLocal
    (S.hypothesis.source_normalizer_maximal_unique_at structural
      (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
      (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple)).2
    (isPGroup_pCoreIn 2 (L ⊔ (T : Subgroup G)))
  exact (L ⊔ (T : Subgroup G)).le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image (L ⊔ (T : Subgroup G))
      (pCore 2 (L ⊔ (T : Subgroup G) : Subgroup G)))

theorem four_pointCore_le_chosenCore_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (e : letI := S.chosen.actionCentralizer_normal
      (L ⧸ (centralizer (V : Set G)).subgroupOf L) ≃* alternatingGroup (Fin 7))
    (hd : Module.finrank (ZMod 2) S.chosen.space = 4)
    {z : G} (hz : z ∈ V) (hz1 : z ≠ 1)
    (hzT : z ∈ omegaCenterIn (T : Subgroup G)) :
    S.fourPointCore z ≤ (L ⊔ (T : Subgroup G)).pCoreIn 2 := by
  rw [← S.chosen_sylowCentralizer_eq_core_at structural]
  refine le_inf ?_ (S.four_pointCore_centralizes_at structural e hd hz hz1 hzT)
  simpa only [Sylow.coe_subtype, map_subgroupOf_eq_of_le le_sup_right] using
    pCoreIn_le_sylow (S.fourPointPerfect z ⊔ (T : Subgroup G))
      (T.subtype le_sup_right)

theorem four_pointCore_control_of_reverse_core_le_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (e : letI := S.chosen.actionCentralizer_normal
      (L ⧸ (centralizer (V : Set G)).subgroupOf L) ≃* alternatingGroup (Fin 7))
    (hd : Module.finrank (ZMod 2) S.chosen.space = 4)
    {z : G} (hz : z ∈ V) (hz1 : z ≠ 1)
    (hzT : z ∈ omegaCenterIn (T : Subgroup G))
    (hcore : (L ⊔ (T : Subgroup G)).pCoreIn 2 ≤ S.fourPointCore z) :
    ((S.fourPointCore z).subgroupOf (S.fourPointCentralizer z)).characteristicNormalizerClosure ≤
      (S.fourPointLocal z).subgroupOf (S.fourPointCentralizer z) := by
  have he := le_antisymm (S.four_pointCore_le_chosenCore_at structural e hd hz hz1 hzT) hcore
  have hc : (S.fourPointCore z).characteristicNormalizerClosure ≤ normalizer (L : Set G) := by
    rw [he]
    exact S.chosen_core_characteristicControl_at structural
  have hQH := (Chapter1.isSylowIn_iff.mp
    (S.four_pointCore_section_sylow_at structural hz hz1 hzT)).2.1.trans
      (ChapterA.Section04.twoSectionCentralizer_le _ _)
  have hh := characteristicNormalizerClosure_subgroupOf_le hQH hc
  intro g hg
  exact ⟨hh hg, g.property⟩

theorem four_pointPerfect_actionKernel_of_quotient_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (e : letI := S.chosen.actionCentralizer_normal
      (L ⧸ (centralizer (V : Set G)).subgroupOf L) ≃* alternatingGroup (Fin 7))
    (hd : Module.finrank (ZMod 2) S.chosen.space = 4)
    {z : G} (hz : z ∈ V) (hz1 : z ≠ 1)
    (hzT : z ∈ omegaCenterIn (T : Subgroup G))
    (quotient : ClassicalGroup.IsPSL
      ((S.fourPointPerfect z) ⧸ pCore 2 (S.fourPointPerfect z)) 3 2) :
    S.fourPointPerfect z ⊓ centralizer (V : Set G) = (S.fourPointPerfect z).pCoreIn 2 := by
  let := S.point_quotient_simple_at quotient
  have hKN : S.fourPointPerfect z ≤ normalizer (V : Set G) :=
    (map_subtype_le _).trans ((map_subtype_le _).trans inf_le_left)
  have hTK : (T : Subgroup G) ≤ normalizer (S.fourPointPerfect z : Set G) := by
    apply le_trans ?_ (S.four_pointLocal_normalizes_perfect_at structural hz hz1)
    refine le_inf S.chosen.sylow_normalizes_component ?_
    intro t ht
    exact mem_centralizer_singleton_iff.mpr (((mem_omegaCenterIn_iff _ _).mp hzT).2.1 t ht)
  have hcore : (S.fourPointPerfect z).pCoreIn 2 ≤ S.fourPointCore z :=
    pCoreIn_mono_of_normalizes le_sup_left
      (sup_le (S.fourPointPerfect z).le_normalizer hTK)
  apply module_kernel_of_simple_core_at _ V hKN
    (hcore.trans (S.four_pointCore_centralizes_at structural e hd hz hz1 hzT))
  rw [← S.four_pointPerfect_moved e hd hz hz1]
  exact S.chosen.ne_bot

theorem four_pointCore_eq_chosenCore_of_quotient_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (e : letI := S.chosen.actionCentralizer_normal
      (L ⧸ (centralizer (V : Set G)).subgroupOf L) ≃* alternatingGroup (Fin 7))
    (hd : Module.finrank (ZMod 2) S.chosen.space = 4)
    {z : G} (hz : z ∈ V) (hz1 : z ≠ 1)
    (hzT : z ∈ omegaCenterIn (T : Subgroup G))
    (quotient : ClassicalGroup.IsPSL
      ((S.fourPointPerfect z) ⧸ pCore 2 (S.fourPointPerfect z)) 3 2) :
    S.fourPointCore z = (L ⊔ (T : Subgroup G)).pCoreIn 2 := by
  let R := (L ⊔ (T : Subgroup G)).pCoreIn 2
  have hRT : R ≤ (T : Subgroup G) := by
    dsimp only [R]
    rw [← S.chosen_sylowCentralizer_eq_core_at structural]
    exact inf_le_left
  have hTC : (T : Subgroup G) ≤ S.fourPointCentralizer z := by
    intro t ht
    exact mem_centralizer_singleton_iff.mpr (((mem_omegaCenterIn_iff _ _).mp hzT).2.1 t ht)
  have hTK : (T : Subgroup G) ≤ normalizer (S.fourPointPerfect z : Set G) :=
    (le_inf S.chosen.sylow_normalizes_component hTC).trans
      (S.four_pointLocal_normalizes_perfect_at structural hz hz1)
  have hKN : S.fourPointPerfect z ≤ normalizer (V : Set G) :=
    (map_subtype_le _).trans ((map_subtype_le _).trans inf_le_left)
  have hRK : R ≤ normalizer (S.fourPointPerfect z : Set G) := hRT.trans hTK
  have hcomm : ⁅S.fourPointPerfect z,R⁆ ≤ (S.fourPointPerfect z).pCoreIn 2 := by
    rw [← S.four_pointPerfect_actionKernel_of_quotient_at structural e hd hz hz1 hzT quotient]
    refine le_inf (le_normalizer_iff_commutator_le_left.mp hRK) ?_
    exact (commutator_mono le_rfl S.chosen.core_centralizes).trans
      (le_normalizer_iff_commutator_le_right.mp
        (hKN.trans (normalizer_le_normalizer_centralizer V)))
  have hRY : R ≤ S.fourPointSection z :=
    (ChapterA.Section04.le_twoSectionCentralizer_iff _ _ _).mpr
      ⟨hRT.trans hTC,hRK,hcomm⟩
  exact ((Chapter1.isSylowIn_iff.mp (S.four_pointCore_section_sylow_at structural hz hz1 hzT)).2.2
    R (isPGroup_pCoreIn 2 _) (S.four_pointCore_le_chosenCore_at structural e hd hz hz1 hzT) hRY).symm

theorem four_pointPerfect_component_of_quotient_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    {z : G} (hz : z ∈ V) (hz1 : z ≠ 1)
    (quotient : ClassicalGroup.IsPSL
      ((S.fourPointPerfect z) ⧸ pCore 2 (S.fourPointPerfect z)) 3 2) :
    ((S.fourPointPerfect z).subgroupOf (S.fourPointLocal z)).IsCComponent := by
  have hKM : S.fourPointPerfect z ≤ S.fourPointLocal z := by
    rw [S.four_pointLocal_eq_at structural hz hz1]
    exact (map_subtype_le _).trans (map_subtype_le _)
  let f := subgroupOfEquivOfLe hKM
  let q := f.toMonoidHom.pCoreQuotientEquiv (p := 2) f.surjective
    (by rw [f.toMonoidHom.ker_eq_bot f.injective]; exact IsPGroup.of_bot)
  let := S.point_quotient_quasisimple_at quotient
  let : IsQuasisimple (((S.fourPointPerfect z).subgroupOf (S.fourPointLocal z)) ⧸
      pCore 2 ((S.fourPointPerfect z).subgroupOf (S.fourPointLocal z))) :=
    IsQuasisimple.of_mulEquiv q.symm
  have hn : ((S.fourPointPerfect z).subgroupOf (S.fourPointLocal z)).Normal :=
    normal_subgroupOf_of_le_normalizer (S.four_pointLocal_normalizes_perfect_at structural hz hz1)
  exact isCComponent_of_isPPerfect_of_quasisimple_core_quotient hn.isSubnormal
    ((S.four_pointPerfect_twoPerfect z).of_surjective f.symm.toMonoidHom f.symm.surjective)

theorem fourResidualData_of_quotient_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (e : letI := S.chosen.actionCentralizer_normal
      (L ⧸ (centralizer (V : Set G)).subgroupOf L) ≃* alternatingGroup (Fin 7))
    (hd : Module.finrank (ZMod 2) S.chosen.space = 4)
    {z : G} (hz : z ∈ V) (hz1 : z ≠ 1)
    (hzT : z ∈ omegaCenterIn (T : Subgroup G))
    (quotient : ClassicalGroup.IsPSL
      ((S.fourPointPerfect z) ⧸ pCore 2 (S.fourPointPerfect z)) 3 2) :
    S.FourResidualData z :=
  S.fourResidualData_of_component_control_quotient_at structural e hd hz hz1 hzT
    (S.four_pointPerfect_component_of_quotient_at structural hz hz1 quotient)
    (S.four_pointCore_control_of_reverse_core_le_at structural e hd hz hz1 hzT
      (S.four_pointCore_eq_chosenCore_of_quotient_at structural e hd hz hz1 hzT quotient).ge) quotient

theorem fourResidualData_of_component_quotient_reverse_core_le_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (e : letI := S.chosen.actionCentralizer_normal
      (L ⧸ (centralizer (V : Set G)).subgroupOf L) ≃* alternatingGroup (Fin 7))
    (hd : Module.finrank (ZMod 2) S.chosen.space = 4)
    {z : G} (hz : z ∈ V) (hz1 : z ≠ 1)
    (hzT : z ∈ omegaCenterIn (T : Subgroup G))
    (component : ((S.fourPointPerfect z).subgroupOf (S.fourPointLocal z)).IsCComponent)
    (quotient : ClassicalGroup.IsPSL
      ((S.fourPointPerfect z) ⧸ pCore 2 (S.fourPointPerfect z)) 3 2)
    (hcore : (L ⊔ (T : Subgroup G)).pCoreIn 2 ≤ S.fourPointCore z) :
    S.FourResidualData z :=
  S.fourResidualData_of_component_control_quotient_at structural e hd hz hz1 hzT component
    (S.four_pointCore_control_of_reverse_core_le_at structural e hd hz hz1 hzT hcore) quotient

end Setup

end CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven

