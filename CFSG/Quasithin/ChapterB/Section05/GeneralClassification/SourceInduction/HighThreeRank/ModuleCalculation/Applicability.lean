module

public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.HighThreeRank.Offenders
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.HighThreeRank.Preparation
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.IrreducibleBranch.LocalGroups
public import Theory.Representation.BinaryOffender.EquivariantOffender

/-!
# Applying B.5.1 to the actual offender overgroup

Let L be the normal component in the noncentral high-three-rank context.
Its odd centralizer meets every two-subgroup trivially. A normal two-core
in an overgroup of L centralizes L, so that two-core is trivial. The literal
quotient LA/L is a two-group; thus F*(LA) is precisely the embedded L.

Every best offender moves L, and the component commutator dichotomy gives
[L,A] = L. Since the best-offender subgroup of LA is normal and contains A,
it contains L as well. These deductions establish every B.5.1 hypothesis
on the restricted original representation, without assuming a classification
of LA. The full B.5.1 conclusion is retained. If A is outside L, its last
three branches are impossible, leaving the full irreducible-section branch.

The only earlier-source parameter is the complete universal
`ProjectiveLine.QuasisimpleClassificationInput`, produced by
`qt-b05-quasisimple`. Constructing the supplied `NoncentralContext` remains
with `qt-b05-high-three-cover-centralizer`; this file does not assume a
natural S6/S7 model or either of the target centralizer equalities.

Source: Aschbacher–Smith, combined 1 March 2004 manuscript, the proof of
B.5.7, printed p.106, from “As C is of odd order” through the use of B.5.1.
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterB.SourceInduction.HighThreeRank.ModuleCalculation
universe u v
variable {G : Type u} [Group G] [Finite G] {K : GroupClass.{u}}
variable {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
variable (ρ : Representation (ZMod 2) G V)

/-- The actual three-core is cyclic, using its literal image from the prepared cover. -/
theorem threeCore_cyclic {L : Subgroup G} (d : NoncentralContext K G L) :
    IsCyclic (pCore 3 G) := by
  let : IsCyclic (pCore 3 d.cover.Cover) := d.cyclic_threeCore
  rw [← d.threeCore_image]
  exact isCyclic_of_surjective (d.cover.projection.subgroupMap _)
    (d.cover.projection.subgroupMap_surjective _)

/-- Every ambient two-subgroup meets the odd component centralizer trivially. -/
theorem twoSubgroup_disjoint {L : Subgroup G} (d : NoncentralContext K G L)
    (P : Subgroup G) (hP : IsPGroup 2 P) :
    Disjoint P (centralizer (L : Set G)) := by
  obtain ⟨n, hn⟩ := hP.exists_card_eq
  apply disjoint_of_coprime_natCard
  rw [hn]
  exact (Nat.coprime_two_left.mpr d.odd_centralizer).pow_left n

/-- Every overgroup of the component has trivial two-core. -/
theorem local_twoCore {L : Subgroup G} (hL : IsComponent G L)
    (d : NoncentralContext K G L) (D : Subgroup G) (hLD : L ≤ D) :
    pCore 2 D = ⊥ := by
  have hcomp := hL.subgroupOf hLD
  let : IsQuasisimple (L.subgroupOf D) := hcomp.2
  rcases hcomp.normal_dichotomy (pCore 2 D) with hle | hc
  · let : IsSimpleGroup ((L.subgroupOf D) ⧸ center (L.subgroupOf D)) := IsQuasisimple.simple
    let : Nontrivial (L.subgroupOf D) :=
      (QuotientGroup.mk'_surjective (center (L.subgroupOf D))).nontrivial
    let : Group.IsNilpotent (L.subgroupOf D) := (pCore_isPGroup.to_le hle).isNilpotent
    exact (Group.IsPerfect.not_isSolvable (L.subgroupOf D) inferInstance).elim
  · have hC : (pCore 2 D).map D.subtype ≤ centralizer (L : Set G) := by
      rintro _ ⟨a, ha, rfl⟩ l hl
      have hh := commutator_eq_bot_iff_le_centralizer.mp hc
        (show (⟨l, hLD hl⟩ : D) ∈ L.subgroupOf D from hl) a ha
      exact (congrArg Subtype.val hh).symm
    have he : (pCore 2 D).map D.subtype = ⊥ :=
      (twoSubgroup_disjoint d _ (pCore_isPGroup.map D.subtype)).eq_bot_of_le hC
    exact (Subgroup.map_eq_bot_iff_of_injective _ D.subtype_injective).mp he

/-- Inside the literal LA, the generalized Fitting subgroup is the embedded L. -/
theorem local_generalizedFitting {L : Subgroup G} (hL : IsComponent G L)
    (d : NoncentralContext K G L) {A : Subgroup G} (hA : IsBestOffender ρ A) :
    generalizedFitting ↥(L ⊔ A) = L.subgroupOf (L ⊔ A) := by
  let : L.Normal := d.normal
  let : IsQuasisimple (L.subgroupOf (L ⊔ A)) := (hL.subgroupOf le_sup_left).2
  let : IsElementaryAbelian 2 A := hA.1.2
  exact generalizedFitting_eq_of_quasisimple_two_quotient _
    (QuasisimpleSource.IrreducibleBranch.local_quotient_isTwoGroup L A
      (IsElementaryAbelian.isPGroup 2 A))
    (local_twoCore hL d (L ⊔ A) le_sup_left)

/-- Each best offender generates the entire component by commutators. -/
theorem component_commutator {L : Subgroup G} (hL : IsComponent G L)
    (d : NoncentralContext K G L) {A : Subgroup G} (hA : IsBestOffender ρ A) :
    ⁅L, A⁆ = L := by
  let : L.Normal := d.normal
  have hne : ⁅L, A⁆ ≠ ⊥ := by
    intro he
    have hAC : A ≤ centralizer (L : Set G) :=
      le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp he)
    let : IsElementaryAbelian 2 A := hA.1.2
    exact hA.1.1 ((twoSubgroup_disjoint d A
      (IsElementaryAbelian.isPGroup 2 A)).eq_bot_of_le hAC)
  rcases hL.commutator_dichotomy A with hb | he
  · exact (hne hb).elim
  · exact le_antisymm (commutator_le_left L A)
      ((le_iSup_conjugates L A).trans he.symm.le)

/-- Best offenders of the restricted original representation generate LA. -/
theorem local_generated {L : Subgroup G} (hL : IsComponent G L)
    (d : NoncentralContext K G L) {A : Subgroup G} (hA : IsBestOffender ρ A) :
    offenderSubgroup (ρ.comp (L ⊔ A).subtype) = ⊤ := by
  let H := L ⊔ A
  let J := offenderSubgroup (ρ.comp H.subtype)
  let : J.Normal := offenderSubgroup_normal _
  have hAJ : A.subgroupOf H ≤ J :=
    le_iSup_of_le _ (le_iSup_of_le ⟨hA.subgroupOf ρ le_sup_right, le_top⟩ le_rfl)
  have hc : ⁅L.subgroupOf H, A.subgroupOf H⁆ = L.subgroupOf H := by
    apply map_injective H.subtype_injective
    rw [map_commutator, map_subgroupOf_eq_of_le (show L ≤ H from le_sup_left),
      map_subgroupOf_eq_of_le (show A ≤ H from le_sup_right), component_commutator ρ hL d hA]
  have hLJ : L.subgroupOf H ≤ J := by
    rw [← hc]
    exact (commutator_mono le_rfl hAJ).trans (commutator_le_right _ _)
  apply top_unique
  rw [← subgroupOf_self H, subgroupOf_sup (show L ≤ H from le_sup_left)
    (show A ≤ H from le_sup_right)]
  exact sup_le hLJ hAJ

/-- All B.5.1 hypotheses hold on the actual restricted LA action. -/
theorem local_hypothesis (hyp : FFHypothesis K ρ) {L : Subgroup G}
    (hL : IsComponent G L) (d : NoncentralContext K G L)
    {A : Subgroup G} (hA : IsBestOffender ρ A) :
    QuasisimpleSource.QuasisimpleSourceHypothesis (ρ.comp (L ⊔ A).subtype)
      K (L.subgroupOf (L ⊔ A)) := by
  have hf := local_generalizedFitting ρ hL d hA
  refine ⟨hyp.finite_module, hyp.faithful.comp (L ⊔ A).subtype_injective,
    (hL.subgroupOf le_sup_left).2, ?_, ?_, local_twoCore hL d _ le_sup_left,
    local_generated ρ hL d hA⟩
  · exact (IsSQTK.equiv (subgroupOfEquivOfLe (show L ≤ L ⊔ A from le_sup_left))).mpr
      d.component_sqtk
  · rw [hf]
    apply (sup_of_le_left ?_).symm
    rw [← hf]
    exact le_trans (show center ↥(L ⊔ A) ≤ fittingSubgroup ↥(L ⊔ A) from
      le_sSup ⟨inferInstance, inferInstance⟩) le_sup_left

/-- Apply the complete universal B.5.1 input, retaining all six conclusions. -/
theorem local_classification
    (earlier : ProjectiveLine.QuasisimpleClassificationInput.{u,v} K)
    (hyp : FFHypothesis K ρ) {L : Subgroup G}
    (hL : IsComponent G L) (d : NoncentralContext K G L)
    {A : Subgroup G} (hA : IsBestOffender ρ A) :
    Nonempty (ProjectiveLine.QuasisimpleSourceConclusion
      (ρ.comp (L ⊔ A).subtype) (L.subgroupOf (L ⊔ A))) :=
  earlier ↥(L ⊔ A) V (ρ.comp (L ⊔ A).subtype) (L.subgroupOf (L ⊔ A))
    (local_hypothesis ρ hyp hL d hA)

omit [Finite G] in
/-- An offender outside L makes the embedded component proper in LA. -/
theorem local_component_ne_top {L A : Subgroup G} (hout : ¬ A ≤ L) :
    L.subgroupOf (L ⊔ A) ≠ ⊤ := by
  intro he
  apply hout
  intro a ha
  have hh : (⟨a, (le_sup_right : A ≤ L ⊔ A) ha⟩ : ↥(L ⊔ A)) ∈
      L.subgroupOf (L ⊔ A) := he ▸ mem_top _
  exact hh

omit [Finite G] in
/-- Outside L, only B.5.1(1i) survives; retain its complete action and extension data. -/
theorem local_irreducible {L A : Subgroup G} (hout : ¬ A ≤ L)
    (c : ProjectiveLine.QuasisimpleSourceConclusion
      (ρ.comp (L ⊔ A).subtype) (L.subgroupOf (L ⊔ A))) :
    IsIrrPlus (ρ.comp (L ⊔ A).subtype) (L.subgroupOf (L ⊔ A))
        c.sectionData.space.toSubmodule ∧
      Function.Injective c.sectionData.action ∧
      IsIrreducible (c.sectionData.action.comp (L.subgroupOf (L ⊔ A)).subtype) ∧
      ProjectiveLine.IrreducibleActionCase c.sectionData.action
        (L.subgroupOf (L ⊔ A)) (offenderSubgroup c.sectionData.action) ∧
      (∀ T : Sylow 2 ↥(L ⊔ A), L.subgroupOf (L ⊔ A) ⊔ (T : Subgroup ↥(L ⊔ A)) = ⊤) ∧
      QuasisimpleSource.OuterNaturalAction c.sectionData.action := by
  have hn := local_component_ne_top hout
  cases c.clause_one with
  | irreducible hp hf hi hs he =>
    exact ⟨hp, hf, hi, hs, he.resolve_left hn⟩
  | doubleThree _ hw _ _ _ => exact (hn hw).elim
  | naturalDual _ _ hw _ => exact (hn hw).elim
  | repeatedNatural _ _ _ _ _ hw _ => exact (hn hw).elim

/-- The source-selected offender moving O₃(G) has the full local B.5.1 conclusion. -/
theorem exists_moving_classification
    (earlier : ProjectiveLine.QuasisimpleClassificationInput.{u,v} K)
    (hyp : FFHypothesis K ρ) {L : Subgroup G}
    (hL : IsComponent G L) (d : NoncentralContext K G L) :
    ∃ A : Subgroup G, IsBestOffender ρ A ∧
      ¬ A ≤ centralizer (pCore 3 G : Set G) ∧ ¬ A ≤ L ∧
      Nonempty (ProjectiveLine.QuasisimpleSourceConclusion
        (ρ.comp (L ⊔ A).subtype) (L.subgroupOf (L ⊔ A))) := by
  obtain ⟨A, hA, hm, ho, _⟩ := exists_moving_offender ρ hyp hL d
  exact ⟨A, hA, hm, ho, local_classification ρ earlier hyp hL d hA⟩

end CFSG.Quasithin.ChapterB.SourceInduction.HighThreeRank.ModuleCalculation
