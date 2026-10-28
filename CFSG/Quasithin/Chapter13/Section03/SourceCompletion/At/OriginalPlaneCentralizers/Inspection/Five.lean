module
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalPlaneCentralizers.Inspection.Five
public import CFSG.Quasithin.Chapter12.Section02.Preliminaries.NormalizerSourceAt
public import CFSG.Quasithin.Chapter12.Section02.SourceApplications.At
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.At.OriginalPlaneCentralizers.Inspection.Actions
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.At.OriginalPlaneCentralizers.Inspection.CubicKernel

/-!
# Original unitary source argument at the same ambient group and Sylow subgroup

This is the ambient-local specialization of `OriginalPlaneCentralizers.Inspection.Five`.
Its proof retains the original subgroups, actions, relative Sylow placement,
and quotient maps. Only the earlier 12.2.2 and 12.2.13 inputs are restricted
to the fixed G,T. The universal public API remains in the imported module.
The source argument and reference are recorded there; no additional local
classification or normalizer premise is introduced by this specialization.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section03.SourceCompletion.At.OriginalPlaneCentralizers
open CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalPlaneCentralizers
variable {G : Type*} [Group G] [Finite G]

private theorem five_cubic_centralizes_sylow_center
    (X : Subgroup G) (hb : ChapterC.IsAlternatingBlock X 5) [X.Normal]
    (S : Sylow 2 G) (W : Subgroup G)
    (hWC : W ≤ centralizer (S : Set G))
    (hchar : HasCharacteristicTwo G) :
    ∃ x : G, x ∈ centralizer (W : Set G) ∧ orderOf x = 3 := by
  have hWcore : W ≤ pCore 2 G := by
    intro w hw
    apply hchar
    exact (hWC.trans (centralizer_le (pCore_isPGroup.le_sylow_of_normal S))) hw
  obtain ⟨P,hP⟩ := S.exists_subgroupOf_eq_of_normal X
  have hPS : (P : Subgroup X).map X.subtype ≤ (S : Subgroup G) := by
    rw [hP,subgroupOf_map_subtype]
    exact inf_le_left
  have hWfix : W ≤ pCore 2 G ⊓ centralizer ((P : Subgroup X).map X.subtype : Set G) :=
    le_inf hWcore (hWC.trans (centralizer_le hPS))
  have hblock : ChapterC.IsBlock X := ⟨inferInstance,hb.2.1,(inferInstance : X.Normal).isSubnormal⟩
  have hn := hb.sylowNormalizer_centralizes_core_fixed X hblock P
  obtain ⟨a,ha,ho⟩ := hb.exists_sylow_normalizer_cubic P
  exact ⟨a,(hn.trans (centralizer_le hWfix)) (mem_map_of_mem X.subtype ha),
    (Subgroup.orderOf_coe a).trans ho⟩

variable {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]

private theorem five_block_forces_module_cubic (s : Context T L V) (d : MarkedPlane V)
    (J : Subgroup G) (j : LocalData T L d J)
    (hs : Chapter1.IsSylowIn 2 ((L ⊔ T).pCoreIn 2) (J ⊔ (L ⊔ T).pCoreIn 2))
    (hb : ChapterC.IsAlternatingBlock J 5) :
    ∃ x : G, x ∈ centralizer (V : Set G) ∧ orderOf x = 3 := by
  let Q := (L ⊔ (T : Subgroup G)).pCoreIn 2
  let D := J ⊔ Q
  let X := J.subgroupOf D
  let W := V.subgroupOf D
  let : X.Normal := normal_subgroupOf_of_le_normalizer
    (sup_le J.le_normalizer j.input.normalizes)
  let e : X ≃* J := subgroupOfEquivOfLe le_sup_left
  have hbX : ChapterC.IsAlternatingBlock X 5 :=
    ChapterC.RankOne.Solvable.isAlternatingBlock_of_equiv e.symm hb
  obtain ⟨S,hS⟩ := hs
  have hQ : (S : Subgroup D) = Q.subgroupOf D := by
    apply map_injective D.subtype_injective
    rw [map_subgroupOf_eq_of_le (show Q ≤ D from le_sup_right)]
    exact hS
  have hchar : HasCharacteristicTwo D := by
    have hc := ChapterB.QuasisimpleSections.centralizer_generalizedFitting_le (G := D)
    rwa [ChapterC.C27Source.source_join_fitting j.input] at hc
  have hWC : W ≤ centralizer (S : Set D) := by
    intro x hx y hy
    apply Subtype.ext
    have hyQ : (y : G) ∈ Q := by
      change y ∈ Q.subgroupOf D
      rwa [←hQ]
    exact (s.chosen.core_centralizes hyQ) x hx |>.symm
  obtain ⟨x,hx,ho⟩ := five_cubic_centralizes_sylow_center X hbX S W hWC hchar
  refine ⟨x,?_,(Subgroup.orderOf_coe x).trans ho⟩
  intro v hv
  exact congrArg Subtype.val (hx ⟨v,mem_sup_right (s.chosen.le_core hv)⟩ hv)

/-- The original A₅ block is impossible when Q is Sylow in the actual join. -/
theorem Context.not_alternatingFive_block_of_sylow (s : Context T L V) (d : MarkedPlane V)
    (J : Subgroup G) (j : LocalData T L d J)
    (hs : Chapter1.IsSylowIn 2 ((L ⊔ T).pCoreIn 2) (J ⊔ (L ⊔ T).pCoreIn 2))
    (hb : ChapterC.IsAlternatingBlock J 5) : False := by
  obtain ⟨x,hx,ho⟩ := five_block_forces_module_cubic s d J j hs hb
  exact s.no_module_centralizer_cubic x hx ho

open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
open Representation Representation.BinaryOffender ChapterB.QuasisimpleSource

/-- Apply the A₅ exclusion to the original rank-one block alternative,
retaining the full moved section in each higher action row. -/
theorem Context.even_block_or_higher_action
    (s : Context T L V) (d : MarkedPlane V) (J : Subgroup G) (j : LocalData T L d J) :
    let ρ := starRepresentation J ((L ⊔ T).pCoreIn 2)
    let B := offenderSubgroup ρ
    let K := (starImage J ((L ⊔ T).pCoreIn 2) J).subgroupOf B
    (Chapter1.IsSylowIn 2 ((L ⊔ T).pCoreIn 2) (J ⊔ (L ⊔ T).pCoreIn 2) ∧
      IsRankOneBorel (starImage J ((L ⊔ T).pCoreIn 2) J)
        (starM J ((L ⊔ T).pCoreIn 2)
          (centralizer (d.A : Set G) ⊓ normalizer (L : Set G))) ∧
      ∃ n, ChapterC.IsL2EvenBlock J n) ∨
    ∃ c : ChapterB.SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion
        (ρ.comp B.subtype) K,
      PlaneHigherActionCase (ρ.comp B.subtype) K c.sectionData := by
  rcases s.block_or_linear_three_or_symmetric_five d J j with ⟨hs,hm,hb⟩ | hh
  · rcases hb with hb | hb
    · exact Or.inl ⟨hs,hm,hb⟩
    · exact (s.not_alternatingFive_block_of_sylow d J j hs hb).elim
  · exact Or.inr hh

end CFSG.Quasithin.Chapter13.Section03.SourceCompletion.At.OriginalPlaneCentralizers
