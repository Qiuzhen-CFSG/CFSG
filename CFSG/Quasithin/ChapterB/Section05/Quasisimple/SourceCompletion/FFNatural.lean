module
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceCompletion.FFSocle
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.NormalElementaryEmbedding
public import Theory.Representation.BinaryOffender.AmbientSectionTransport

/-!
# Natural sections after shrinking the elementary module

A normal elementary submodule with unchanged conjugation kernel retains the
same perfect component's moved quotient. Its independently proved FF action
admits the full known-simple B.5 source classification on its own offender
subgroup. Comparing the two literal component actions transfers the original
natural coordinates, even when these offender subgroups differ.
Source application: Aschbacher–Smith C.2.7(3)(a), pp.146–147.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterB.QuasisimpleSource.SourceCompletion
variable {G H : Type*} [Group G] [Finite G] [Group H] [Finite H]
  (U V : Subgroup G) [U.Normal] [V.Normal]
  [IsElementaryAbelian 2 U] [IsElementaryAbelian 2 V]
  (hUV : U ≤ V) (q : G →* H) (hq : Function.Surjective q)
  (hU : q.ker = centralizer (U : Set G))
  (hV : q.ker = centralizer (V : Set G))

include hUV in
theorem ff_natural_of_normal_elementary_inclusion
    (C : Subgroup H) [C.Normal] [IsSimpleGroup C] [IsQuasisimple C]
    (hC : centralizer (C : Set H) = ⊥) (hs : IsSQTK KnownSimple.IsKnownSimple C)
    (hff : IsFFModule (NormalElementaryQuotient.representation U q hq hU))
    (hCJ : C ≤ offenderSubgroup (NormalElementaryQuotient.representation V q hq hV))
    (c : SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion
      ((NormalElementaryQuotient.representation V q hq hV).comp
        (offenderSubgroup (NormalElementaryQuotient.representation V q hq hV)).subtype)
      (C.subgroupOf (offenderSubgroup (NormalElementaryQuotient.representation V q hq hV))))
    (hi : IsIrrPlus
      ((NormalElementaryQuotient.representation V q hq hV).comp
        (offenderSubgroup (NormalElementaryQuotient.representation V q hq hV)).subtype)
      (C.subgroupOf (offenderSubgroup (NormalElementaryQuotient.representation V q hq hV)))
      c.sectionData.space.toSubmodule)
    (F : BinaryField)
    (hnatural : ActionEquiv (c.sectionData.action.comp
      (C.subgroupOf (offenderSubgroup (NormalElementaryQuotient.representation V q hq hV))).subtype)
      (linearNatural F 2)) :
    let σ := NormalElementaryQuotient.representation U q hq hU
    C ≤ offenderSubgroup σ ∧
      ∃ cU : SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion
        (σ.comp (offenderSubgroup σ).subtype) (C.subgroupOf (offenderSubgroup σ)),
        IsLinearNatural (cU.sectionData.action.comp (C.subgroupOf (offenderSubgroup σ)).subtype) F 2 := by
  let ρ := NormalElementaryQuotient.representation V q hq hV
  let σ := NormalElementaryQuotient.representation U q hq hU
  obtain ⟨hCσ,⟨cU⟩⟩ := ff_socle_source_conclusion σ C hC hs
    (NormalElementaryQuotient.representation_injective _ _ _ _) hff
  have hi' := (IsIrrPlus.subgroupOf_iff ρ C (offenderSubgroup ρ) hCJ
    c.sectionData.space.toSubmodule).mp hi
  have hspace := c.sectionData.space_eq
  rw [moved_comp_map,map_subgroupOf_eq_of_le hCJ] at hspace
  rw [hspace] at hi'
  have hne : C ≠ ⊥ := (nontrivial_iff_ne_bot C).mp inferInstance
  let E := normalElementary_moved_comparison U V hUV q hq hU hV C
    (offenderSubgroup ρ) (offenderSubgroup σ) hne hCJ hCσ c.sectionData cU.sectionData hi'
  refine ⟨hCσ,cU,⟨?_⟩⟩
  exact ⟨E.groupEquiv.trans hnatural.groupEquiv,E.linearEquiv.trans hnatural.linearEquiv,
    fun g v => (congrArg hnatural.linearEquiv (E.intertwines g v)).trans
      (hnatural.intertwines (E.groupEquiv g) (E.linearEquiv v))⟩

end CFSG.Quasithin.ChapterB.QuasisimpleSource.SourceCompletion
