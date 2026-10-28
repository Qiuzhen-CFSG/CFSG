module

public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.FusionEightGeometryDecompositionMovedAction
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.FusionEightGeometryDecompositionCocycles
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.MovedRestriction

/-!
# The moved point span is the chosen module

Transport the original chosen Irr⁺ space into the point span through its actual
inclusion in R₂(LT). Its nonzero L-fixed vector lies in the moved space, excluding
a fixed complement. Clause two of the genuine B.5.1 source conclusion therefore
makes the moved space Irr⁺. The Irr⁺ antichain property identifies it with the
chosen space, giving [pointSpan,L] = V for the original ambient subgroups.

The final theorem applies this equality to the point-fixed cocycle assembly.
The point-span module witness and the three point-geometry premises remain
explicit, as required by their separate source constructions.

Source: Aschbacher--Smith, B.5.1(2) and original 12.2.16, printed pp.99 and 800,
`refs/quasithin.pdf`.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource.AlternatingEightFusion
universe u
variable {G : Type u} [Group G]
variable {T : Sylow 2 G} {L V : Subgroup G}
variable {C : AlternatingEightFusion T L V}
namespace PointSpanModule
variable (R : C.PointSpanModule)

/-- The original inclusion of the reduced point span into R₂(LT). -/
def reducedInclusion : letI := R.elementary
    Additive C.pointSpan →ₗ[ZMod 2] Additive (ReducedModule (L ⊔ (T : Subgroup G))) :=
  letI := R.elementary
  ({ toFun w := ⟨⟨w, R.le_sylow.trans le_sup_right w.property⟩,
       R.reduced.le_reducedPSubgroup w.property⟩
     map_one' := rfl
     map_mul' _ _ := rfl } : C.pointSpan →* ReducedModule (L ⊔ (T : Subgroup G))).toAdditive.toZModLinearMap 2

private theorem reducedInclusion_injective : letI := R.elementary
    Function.Injective R.reducedInclusion := by
  let := R.elementary
  intro a b he
  exact Additive.toMul.injective (Subtype.ext
    (congrArg (fun w : Additive (ReducedModule (L ⊔ (T : Subgroup G))) =>
      (w.toMul.val : G)) he))

abbrev chosenSpace (D : ChosenModule T L V) : letI := R.elementary
    Submodule (ZMod 2) (Additive C.pointSpan) :=
  letI := R.elementary
  D.space.comap R.reducedInclusion

private theorem chosenSpace_map (D : ChosenModule T L V) : letI := R.elementary
    (R.chosenSpace D).map R.reducedInclusion = D.space := by
  let := R.elementary
  apply le_antisymm (Submodule.map_comap_le _ _)
  intro v hv
  have hvV : (v.toMul.val : G) ∈ V :=
    D.image_eq.le (mem_map_of_mem _ (mem_map_of_mem _ hv))
  refine ⟨Additive.ofMul ⟨(v.toMul.val : G), C.chosen_le_pointSpan D hvV⟩, ?_, ?_⟩
  · exact hv
  · rfl

theorem mem_chosenSpace (D : ChosenModule T L V) : letI := R.elementary
    ∀ w : Additive C.pointSpan, w ∈ R.chosenSpace D ↔ (w.toMul : G) ∈ V := by
  let := R.elementary
  intro w
  constructor
  · intro hw
    change R.reducedInclusion w ∈ D.space at hw
    apply D.image_eq.le
    exact ⟨_, ⟨(R.reducedInclusion w).toMul, hw, rfl⟩, rfl⟩
  · intro hw
    obtain ⟨v, ⟨a, ha, rfl⟩, he⟩ := D.image_eq.ge hw
    have he' : Additive.ofMul a = R.reducedInclusion w :=
      Additive.toMul.injective (Subtype.ext (Subtype.ext he))
    change R.reducedInclusion w ∈ D.space
    rw [← he']
    exact ha

theorem chosenSpace_irrPlus (D : ChosenModule T L V) : letI := R.elementary
    IsIrrPlus R.representation R.component (R.chosenSpace D) := by
  let := R.elementary
  apply D.irrPlus.isIrrPlus.of_intertwining
    (reducedRepresentation (L ⊔ (T : Subgroup G))) R.representation
    (R.projection.subgroupMap (L.subgroupOf (L ⊔ (T : Subgroup G))))
    (R.projection.subgroupMap_surjective _) R.reducedInclusion R.reducedInclusion_injective
  · intro l w
    rfl
  · exact R.chosenSpace_map D

open ChapterB.QuasisimpleSource in
/-- The nontrivial chosen fixed vector excludes a fixed complement to the moved space. -/
theorem moved_not_compl (D : ChosenModule T L V) : letI := R.elementary
    ¬ IsCompl (moved R.representation R.component)
      (fixedSpace R.representation R.component) := by
  let := R.elementary
  have hle : R.chosenSpace D ≤ moved R.representation R.component := by
    rw [← (R.chosenSpace_irrPlus D).choose_spec.1]
    exact subspaceCommutator_mono_left _ le_top _
  let z : Additive C.pointSpan := Additive.ofMul ⟨C.z, C.chosen_le_pointSpan D C.z.property⟩
  have hz : z ∈ moved R.representation R.component :=
    hle ((R.mem_chosenSpace D z).mpr C.z.property)
  have hzfix : z ∈ fixedSpace R.representation R.component := by
    intro k
    obtain ⟨l, rfl⟩ := R.componentHom_surjective k
    apply Additive.toMul.injective
    apply Subtype.ext
    change (l : G) * (C.z : G) * (l : G)⁻¹ = C.z
    rw [C.z_fixed l l.property, mul_inv_cancel_right]
  intro hc
  have he : z = 0 := hc.disjoint.le_bot ⟨hz, hzfix⟩
  exact C.z_ne (congrArg (fun w : Additive C.pointSpan => (w.toMul : G)) he)

open ChapterB.QuasisimpleSource in
/-- B.5.1(2) identifies the moved space with the original chosen Irr⁺ space. -/
theorem moved_eq_chosenSpace [Finite G] (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L) : letI := R.elementary
    moved R.representation R.component = R.chosenSpace D := by
  let := R.elementary
  obtain ⟨hKJ, ⟨c⟩⟩ := R.source_conclusion D h
  have hspace : c.sectionData.space.toSubmodule = moved R.representation R.component := by
    rw [c.sectionData.space_eq, moved_comp_map, map_subgroupOf_eq_of_le hKJ]
  have hfix := fixedSpace_subgroupOf R.representation R.component
    (offenderSubgroup R.representation) hKJ
  have hn : ¬ IsCompl c.sectionData.space.toSubmodule
      (fixedSpace (R.representation.comp (offenderSubgroup R.representation).subtype)
        (R.component.subgroupOf (offenderSubgroup R.representation))) := by
    rw [hspace, hfix]
    exact R.moved_not_compl D
  have hi := (IsIrrPlus.subgroupOf_iff R.representation R.component
    (offenderSubgroup R.representation) hKJ c.sectionData.space.toSubmodule).mp
      (c.clause_two hn).1
  rw [hspace] at hi
  apply Eq.symm
  apply (R.chosenSpace_irrPlus D).eq_of_le R.representation hi
  rw [← (R.chosenSpace_irrPlus D).choose_spec.1]
  exact subspaceCommutator_mono_left _ le_top _

end PointSpanModule

variable (C : AlternatingEightFusion T L V)
open ChapterB.QuasisimpleSource in
/-- The moved point span is exactly the original chosen module. -/
theorem pointSpan_commutator_eq_chosen [Finite G]
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V) (R : C.PointSpanModule) : ⁅C.pointSpan, L⁆ = V := by
  let := R.elementary
  apply le_antisymm _ (C.chosen_le_pointSpan_commutator D)
  rw [commutator_comm]
  apply commutator_le.mpr
  intro l hl w hw
  let v : Additive C.pointSpan := Additive.ofMul ⟨w, hw⟩
  have hm : R.representation (R.componentHom ⟨l, hl⟩) v - v ∈
      moved R.representation R.component :=
    Submodule.subset_span ⟨R.componentHom ⟨l, hl⟩,
      (R.componentHom ⟨l, hl⟩).property, v, Submodule.mem_top, rfl⟩
  rw [R.moved_eq_chosenSpace D h] at hm
  have hh := (R.mem_chosenSpace D _).mp hm
  change (l * w * l⁻¹) / w ∈ V at hh
  simpa only [commutatorElement_def, div_eq_mul_inv] using hh

/-- The corrected point-fixed supplement now needs only its point geometry. -/
theorem pointFixed_conclusions_of_point_geometry [Finite G]
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V) (R : C.PointSpanModule)
    (hP : fixedSpace (BinaryPermutation.alternatingRepresentation (Fin 8))
      C.pointComponentImage ≤ BinaryPermutation.core (Fin 8))
    (hfixed : V ⊓ centralizer (L ⊓ C.pointSylow : Set G) ≤ C.pointCore)
    (hs : (T : Subgroup G) ≤ C.pointSylow ⊔ ((T : Subgroup G) ⊓ L)) :
    omegaCenterIn C.pointSylow = C.pointCore ⊔ C.pointFixed ∧
      C.pointFixed ≤ centralizer ((T : Subgroup G) : Set G) :=
  C.pointFixed_conclusions_of_moved_and_point_geometry D R
    (C.pointSpan_commutator_eq_chosen h.toHypothesis1221 D R).le hP hfixed hs

end CFSG.Quasithin.Chapter12.Section02.RecognitionSource.AlternatingEightFusion
