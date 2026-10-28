module
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalPlaneCentralizers.Inspection.Actions
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalPlaneCentralizers.Inspection.CubicKernel
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.AlternatingFivePlaneCentralizer
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.AlternatingFive.CubicNormalizer
public import CFSG.Quasithin.ChapterC.Section01.RankOne.Solvable.Source.Transport
public import CFSG.Quasithin.ChapterC.Section02.SourceExtraction.C27.MSRestriction

/-!
# Excluding the actual A₅ block in the original rank-one branch

The original radical Q is central on V. When Q is Sylow in JQ,
characteristic two puts V in O₂(JQ). The deleted A₅ module calculation
makes the normalizer of a Sylow subgroup of J centralize V. That normalizer
contains an actual cubic, contradicting the previously proved three-free
order of C_G(V). All restrictions use the original component and join.

This removes the A₅ block from the rank-one alternative. The distinct
symmetric-five moved-section row and the linear field reductions remain
with the plane-centralizer assembly owner.
Source: Aschbacher--Smith 13.3.12, pp.889--890, and C.1.13(c), pp.124--125.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalPlaneCentralizers
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

end CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalPlaneCentralizers
