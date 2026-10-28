module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceOrthogonal.LocalAction.OrthogonalModule.Recognition.SourceAction.OffenderReduction
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.Orthogonal.OffenderModels.StrongSections.Extensions.PerfectCover
public import CFSG.Quasithin.ChapterB.Section03.Offenders.Eight.Canonical.Hyperplanes
public import Theory.GroupTheory.GeneralizedFitting.SimpleTwoQuotient
public import Theory.AtlasPort.LinearGroups.G2.Order


/-!
# Offenders on the alternating moved space of a generated S₈-module

Apply the full corrected B.5.1 input to the faithful offender-generated
S₈ actor and its actual normal A₈. The latter is the generalized Fitting
subgroup. Since it is proper, clause (1) selects the irreducible outer
alternative; group orders identify its central quotient as the natural
six-dimensional S₈-module.

The moved space is a perfect central cover of that quotient. The intrinsic
augmentation-cover theorem therefore identifies it with the natural module
or the seven-dimensional augmentation core. On both spaces the even subgroup
of four disjoint swaps has rank and fixed codimension three. Transporting this
specific offender proves FF for A₈ on the covering space itself. Equality of
the literal moved submodules gives the assertion for every named MovedSection.

The final application constructs all premises on the original plus quotient
from SourceAction.Configuration, retaining its elementary-module instance.
The full corrected B.5.1 implication remains explicit, as permitted here;
its universal proof belongs to qt-b05-quasisimple. The source classification
assembly remains with the parent of this conditional transfer.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), the paragraph
following 13.6.23, printed p.933/PDF p.950; B.5.1, pp.99–103; the augmentation
module of B.3 and the perfect-cover comparison I.1.5–6, printed p.408.
-/

@[expose] public section

open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceOrthogonal.LocalAction.OrthogonalModule.Recognition.SourceAction
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives
open CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction
universe u w
variable {D : Type u} [Group D] {W : Type w} [AddCommGroup W] [Module (ZMod 2) W]

private theorem component_eq_commutator (E : D ≃* Equiv.Perm (Fin 8))
    (C : Subgroup D) (hC : C.map E.toMonoidHom = alternatingGroup (Fin 8)) :
    C = _root_.commutator D := by
  apply Subgroup.map_injective (f := E.toMonoidHom) E.injective
  rw [hC, _root_.commutator_def, Subgroup.map_commutator,
    map_top_of_surjective _ E.surjective]
  exact (alternatingGroup.commutator_perm_eq (by simp)).symm

private theorem component_map (E E' : D ≃* Equiv.Perm (Fin 8))
    (C : Subgroup D) (hC : C.map E.toMonoidHom = alternatingGroup (Fin 8)) :
    C.map E'.toMonoidHom = alternatingGroup (Fin 8) := by
  rw [component_eq_commutator E C hC, _root_.commutator_def, Subgroup.map_commutator,
    map_top_of_surjective _ E'.surjective]
  exact alternatingGroup.commutator_perm_eq (by simp)

private theorem component_index (E : D ≃* Equiv.Perm (Fin 8))
    (C : Subgroup D) (hC : C.map E.toMonoidHom = alternatingGroup (Fin 8)) :
    C.index = 2 := by
  rw [← Subgroup.index_map_equiv C E]
  change (C.map E.toMonoidHom).index = 2
  rw [hC]
  exact alternatingGroup.index_eq_two

private theorem component_quasisimple (E : D ≃* Equiv.Perm (Fin 8))
    (C : Subgroup D) (hC : C.map E.toMonoidHom = alternatingGroup (Fin 8)) :
    IsQuasisimple C := by
  let : IsSimpleGroup (alternatingGroup (Fin 8)) := alternatingGroup.isSimpleGroup (by simp)
  let : IsQuasisimple (alternatingGroup (Fin 8)) := {
    toIsPerfect := ⟨commutator_alternatingGroup_eq_top (by simp)⟩
    simple := ((QuotientGroup.quotientMulEquivOfEq
      (alternatingGroup.center_eq_bot (by simp))).trans QuotientGroup.quotientBot).isSimpleGroup }
  let e := (C.equivMapOfInjective E.toMonoidHom E.injective).trans
    (MulEquiv.subgroupCongr hC)
  exact IsQuasisimple.of_mulEquiv e.symm

private theorem symmetric_card (n : ℕ) : Nat.card (Equiv.Perm (Fin n)) = n.factorial := by
  simp [Nat.card_eq_fintype_card, Fintype.card_perm]

private theorem eight_of_outer (ρ : Representation (ZMod 2) D W)
    (E : D ≃* Equiv.Perm (Fin 8)) (h : OuterNaturalAction ρ) : IsSymmetricNatural ρ 8 := by
  rcases h with hn | hg
  · obtain ⟨n, hn, hn', ⟨e⟩⟩ := hn
    have hc : n.factorial = Nat.factorial 8 := by
      rw [← symmetric_card, ← symmetric_card]
      exact (Nat.card_congr e.groupEquiv.toEquiv).symm.trans (Nat.card_congr E.toEquiv)
    have he : n = 8 := by
      interval_cases n <;> first | rfl | (exfalso; norm_num at hc)
    subst n
    exact ⟨e⟩
  · obtain ⟨e⟩ := hg
    have hc := (Nat.card_congr E.toEquiv).symm.trans (Nat.card_congr e.groupEquiv.toEquiv)
    rw [symmetric_card, Atlas.G2.card_Model] at hc
    norm_num at hc

private theorem ff_of_natural_or_cover [FiniteDimensional (ZMod 2) W]
    (ρ : Representation (ZMod 2) D W) (E : D ≃* Equiv.Perm (Fin 8))
    (C : Subgroup D) (hC : C.map E.toMonoidHom = alternatingGroup (Fin 8))
    (h : IsEightNaturalOrCover ρ E) : IsFFModule (ρ.comp C.subtype) := by
  let B := ChapterB.Offenders.evenPart 8
  let A := B.map E.symm.toMonoidHom
  have hmap : A.map E.toMonoidHom = B := by
    rw [map_map]
    simp
  have hB := ChapterB.Offenders.Eight.isElementaryTwo_evenPart
  let : IsElementaryAbelian 2 B := hB.2
  have hA : IsElementaryTwo A := by
    refine ⟨?_, IsElementaryAbelian.map E.symm.toMonoidHom⟩
    intro hb
    apply hB.1
    change B = ⊥
    rw [← hmap, hb, Subgroup.map_bot]
  have hAC : A ≤ C := by
    intro a ha
    have he : E a ∈ alternatingGroup (Fin 8) := by
      have hb : E a ∈ B := hmap ▸ mem_map_of_mem E.toMonoidHom ha
      exact hb.2
    rw [← hC, mem_map_equiv] at he
    simpa only [E.symm_apply_apply] using he
  have hr : rank A = 3 := by
    rw [rank_map_injective _ E.symm.injective]
    exact ChapterB.Offenders.Eight.rank_evenPart
  have ho : IsOffender ρ A := by
    refine ⟨hA, ?_⟩
    rcases h with ⟨e, he⟩ | ⟨e, he⟩
    · rw [fixedCodim_map_equivariant ρ _ E.toMonoidHom e he, hmap,
        ChapterB.Offenders.Eight.fixedCodim_evenPart.2.2.2, hr]
    · rw [fixedCodim_map_equivariant ρ _ E.toMonoidHom e he, hmap,
        ChapterB.Offenders.Eight.fixedCodim_evenPart.2.2.1, hr]
  exact ⟨A.subgroupOf C, ho.subgroupOf ρ hAC⟩

private theorem ff_of_natural_section [FiniteDimensional (ZMod 2) W]
    (ρ : Representation (ZMod 2) D W) (E : D ≃* Equiv.Perm (Fin 8))
    (C : Subgroup D) (hC : C.map E.toMonoidHom = alternatingGroup (Fin 8))
    (s : MovedSection ρ C) (hi : IsIrrPlus ρ C s.space.toSubmodule)
    (hn : IsSymmetricNatural s.action 8) : IsFFModule (s.space.toRepresentation.comp C.subtype) := by
  obtain ⟨e⟩ := hn
  have hmap := component_map E e.groupEquiv C hC
  let p := e.linearEquiv.toLinearMap.comp s.central.toSubmodule.mkQ
  have hp (g : D) (v : s.space.toSubmodule) :
      p (s.space.toRepresentation g v) =
        BinaryPermutation.naturalRepresentation (Fin 8) (e.groupEquiv g) (p v) :=
    e.intertwines g (s.central.toSubmodule.mkQ v)
  have hsur : Function.Surjective p := e.linearEquiv.surjective.comp (Submodule.mkQ_surjective _)
  have hker : p.ker ≤ fixedSpace s.space.toRepresentation C := by
    intro v hv
    have hv' : s.central.toSubmodule.mkQ v = 0 := e.linearEquiv.injective
      ((show e.linearEquiv (s.central.toSubmodule.mkQ v) = 0 from hv).trans
        e.linearEquiv.map_zero.symm)
    rw [← s.central_eq]
    exact (Submodule.Quotient.mk_eq_zero _).mp hv'
  have hgen : subspaceCommutator s.space.toRepresentation ⊤ C = ⊤ := by
    let U := subspaceCommutator s.space.toRepresentation ⊤ C
    have hm : s.space.toSubmodule ≤ U.map s.space.toSubmodule.subtype := by
      conv_lhs => rw [← hi.choose_spec.1]
      apply Submodule.span_le.mpr
      rintro _ ⟨g, hg, v, hv, rfl⟩
      exact ⟨s.space.toRepresentation g ⟨v, hv⟩ - ⟨v, hv⟩,
        Submodule.subset_span ⟨g, hg, ⟨v, hv⟩, Submodule.mem_top, rfl⟩, rfl⟩
    apply top_unique
    intro v _
    obtain ⟨w, hw, he⟩ := hm v.property
    rwa [show w = v from Subtype.ext he] at hw
  have hmodel := OffenderModels.StrongSections.Extensions.naturalOrCover_of_central_cover
    s.space.toRepresentation e.groupEquiv C hmap p hp hsur hker hgen
  exact ff_of_natural_or_cover s.space.toRepresentation e.groupEquiv C hmap hmodel

/-- A faithful offender-generated S₈-module is FF for the actual normal A₈
on every choice of its literal moved covering space. Only the full corrected
B.5.1 theorem is retained as a classification input. -/
theorem generated_symmetric_component_ff [Finite D] [FiniteDimensional (ZMod 2) W]
    {Ξ : GroupClass.{u}} (classification : ProjectiveLine.QuasisimpleClassificationInput.{u,w} Ξ)
    (ρ : Representation (ZMod 2) D W) (hρ : Function.Injective ρ)
    (C : Subgroup D) [C.Normal] (E : D ≃* Equiv.Perm (Fin 8))
    (hC : C.map E.toMonoidHom = alternatingGroup (Fin 8))
    (hsq : IsSQTK Ξ C) (hcore : pCore 2 D = ⊥) (hgen : offenderSubgroup ρ = ⊤)
    (s : MovedSection ρ C) : IsFFModule (s.space.toRepresentation.comp C.subtype) := by
  let : IsQuasisimple C := component_quasisimple E C hC
  have hidx := component_index E C hC
  have hneq : C ≠ ⊤ := by intro he; simp [he] at hidx
  have hquot : IsPGroup 2 (D ⧸ C) := IsPGroup.of_card (n := 1) (by
    change C.index = 2 ^ 1
    simpa using hidx)
  have hf := generalizedFitting_eq_of_quasisimple_two_quotient C hquot hcore
  have hz : center D ≤ C := by
    rw [← hf]
    exact (show center D ≤ fittingSubgroup D from le_sSup ⟨inferInstance, inferInstance⟩).trans
      (fitting_le_generalizedFitting D)
  obtain ⟨h⟩ := classification D W ρ C {
    finite_module := inferInstance
    faithful := hρ
    quasisimple := inferInstance
    sqtk := hsq
    fitting := hf.trans (sup_of_le_left hz).symm
    twoCore := hcore
    generated := hgen }
  have hff : IsFFModule (h.sectionData.space.toRepresentation.comp C.subtype) := by
    cases h.clause_one with
    | irreducible hi _ _ _ he =>
      exact ff_of_natural_section ρ E C hC h.sectionData hi
        (eight_of_outer h.sectionData.action E ((he.resolve_left hneq).2))
    | doubleThree _ he _ _ _ => exact (hneq he).elim
    | naturalDual _ _ he _ => exact (hneq he).elim
    | repeatedNatural _ _ _ _ _ he _ => exact (hneq he).elim
  have he : h.sectionData.space = s.space := Subrepresentation.toSubmodule_injective
    (h.sectionData.space_eq.trans s.space_eq.symm)
  exact (congrArg (fun U : Subrepresentation ρ =>
    IsFFModule (U.toRepresentation.comp C.subtype)) he).mp hff

open ComponentSelection
variable {G : Type u} [Group G] [Finite G] {Ξ : GroupClass.{u}}
  {K L V : Subgroup G} {T : Sylow 2 G} {z v : G}

/-- The generated branch of the source's ordinary component-FF assertion.
The supplied elementary structure, plus quotient, and canonical moved section
are exactly those used by `source_action_inputs` and the final recognition. -/
theorem component_ff_of_generated (c : Configuration Ξ K L V T z v)
    (classification : ProjectiveLine.QuasisimpleClassificationInput.{u,u} Ξ) :
    letI := c.elementary
    let ρ := representation K L (T : Subgroup G) z v c.lv_invariant c.seed_fixed
    let C := plusImage K L (T : Subgroup G) z v c.lv_invariant c.seed_fixed K
    let s := movedSection K L (T : Subgroup G) z v c.lv_invariant c.seed_fixed c.invariant c.lv_le
    offenderSubgroup ρ = ⊤ → IsFFModule (s.space.toRepresentation.comp C.subtype) := by
  let := c.elementary
  dsimp only
  intro hgen
  obtain ⟨hcore, hρ, hsq, _, _, _, _, E, _, hmap⟩ := source_action_inputs c
  let := c.applicability.finite_module
  let := c.applicability.normal
  exact generated_symmetric_component_ff classification _ hρ _ E hmap hsq hcore hgen _

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceOrthogonal.LocalAction.OrthogonalModule.Recognition.SourceAction
