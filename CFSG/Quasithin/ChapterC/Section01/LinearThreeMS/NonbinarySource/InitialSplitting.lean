module
public import CFSG.Quasithin.ChapterC.Section01.LinearThreeMS.NonbinarySource.InitialLayer

/-!
# The whole initial moved space over a nonbinary field

The natural initial quotient has vanishing first cohomology in both
natural and dual coordinates. Thus its literal moved space splits from
the component-fixed space. The doubled-natural row splits by the same
cohomology calculation on both summands. The binary higher-rank rows
are excluded by the already proved Sylow-center comparison.

Consequently the whole initial moved space, with its actual conjugation
action, is natural or doubled natural in the original field degree.
This is a statement about Ω₁(Z(O₂(KR))); the nonabelian whole-core
sections and radical inequalities in C.1.34 remain separate obligations.
Source: Aschbacher--Smith B.5.1(1)--(2), I.1.6(4),(6), and C.1.31--34;
MS93, the initial module analysis in Sections 2--3.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.ChapterC.LinearThreeMS.NonbinarySource
open Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
open ChapterB.QuasisimpleSource

/-- Larger-field cohomology splits the actual moved section; its whole
space is natural or doubled natural with one actor on all summands. -/
theorem split_natural_or_double_of_full_source
    {X W : Type*} [Group X] [Finite X] [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W]
    (ρ : Representation (ZMod 2) X W) {B : Subgroup X} [IsQuasisimple B]
    (c : ChapterB.SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion ρ B)
    (hsq : IsSQTK KnownSimple.IsKnownSimple X) (hff : IsFFModule ρ)
    (E : BinaryField) (hn : 1 < E.degree)
    (mark : B ≃* SL(3,E.Carrier)) :
    IsCompl c.sectionData.space.toSubmodule (fixedSpace ρ B) ∧
    ∃ F : BinaryField, F.degree = E.degree ∧
      (IsLinearNatural (c.sectionData.space.toRepresentation.comp B.subtype) F 3 ∨
        IsRepeatedLinearNatural (c.sectionData.space.toRepresentation.comp B.subtype) F 3 2) := by
  cases c.clause_one with
  | irreducible hi hf hirr hs hext =>
    have hff' : IsFFModule c.sectionData.action := by
      obtain ⟨A,hA⟩ := hff
      exact ⟨A,IrreducibleBranch.moved_offender c.sectionData hA⟩
    have hq : quadraticRatio c.sectionData.action ≤ 2 :=
      ((isFFModule_iff_quadraticRatio_le_one _).mp hff').trans (by norm_num)
    let hsource : ChapterK.Linear.Recognition.SourceHypothesis KnownSimple.IsKnownSimple
        c.sectionData.action B :=
      ⟨inferInstance,inferInstance,hsq,c.fitting_eq.symm,inferInstance,hf,hirr,
        (cubicRatio_le_quadraticRatio _).trans hq⟩
    let : IsSimpleGroup PSL(3,E.Carrier) := Atlas.psl_simple_high_rank 3 (by decide)
    let : Nontrivial SL(3,E.Carrier) := (Matrix.PSL3.projection_surjective E.Carrier).nontrivial
    obtain ⟨d⟩ := ChapterK.Linear.Recognition.SourceFF.naturalSourceInput_of_quotient_ff
      hsource (B := E)
      (IsQuasisimple.centralQuotientEquiv mark.toMonoidHom mark.surjective) hff'
    have hsplit := ExtensionConsequences.linearThree_large_isCompl c.sectionData hi E hn d.natural
    have hz : Representation.invariants (c.sectionData.space.toRepresentation.comp B.subtype) = ⊥ := by
      apply bot_unique
      intro v hv
      apply Subtype.ext
      exact (disjoint_iff.mp hsplit.disjoint).le
        ⟨v.property, fun g => congrArg Subtype.val (hv g)⟩
    let a := ExtensionConsequences.actionSymm
      (ExtensionConsequences.movedQuotientEquiv c.sectionData hz)
    refine ⟨hsplit,E,rfl,Or.inl ⟨?_⟩⟩
    exact ⟨a.groupEquiv.trans d.natural.groupEquiv,
      a.linearEquiv.trans d.natural.linearEquiv,
      fun g v => (congrArg d.natural.linearEquiv (a.intertwines g v)).trans
        (d.natural.intertwines (a.groupEquiv g) (a.linearEquiv v))⟩
  | doubleThree F hw e _ _ =>
    have hd := SourceCompletion.linearThree_degree_eq E F (mark.symm.trans e.groupEquiv)
    have hsplit := ExtensionConsequences.doubleThree_large_isCompl c.sectionData F
      (hd ▸ hn) hw e
    refine ⟨?_,F,hd.symm,Or.inr ⟨e⟩⟩
    simpa only [hw,ExtensionConsequences.fixedSpace_top] using hsplit
  | naturalDual d hd _ hn' =>
    obtain ⟨e⟩ := hn'
    exact (SourceCompletion.no_linearThree_binary_equiv E hd (mark.symm.trans e.groupEquiv)).elim
  | repeatedNatural d r hd _ _ _ hn' =>
    obtain ⟨e⟩ := hn'
    exact (SourceCompletion.no_linearThree_binary_equiv E hd (mark.symm.trans e.groupEquiv)).elim

variable {G : Type*} [Group G] [Finite G] {K R : Subgroup G}
variable {n : ℕ} {F : Type} [Field F] [Finite F] [CharP F 2]
variable (h : LinearThreeMSPair KnownSimple.IsKnownSimple K R n F) (hn : 1 < n)
include h hn

/-- The actual initial moved space splits from its component-fixed space
and has a full natural or doubled natural marking. -/
theorem centralOmega_split_source :
    ∃ c : ChapterB.SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion
      ((centralOmegaRepresentation K R).comp (offenderSubgroup (centralOmegaRepresentation K R)).subtype)
      ((centralOmegaComponent K R).subgroupOf (offenderSubgroup (centralOmegaRepresentation K R))),
    IsCompl c.sectionData.space.toSubmodule
      (fixedSpace ((centralOmegaRepresentation K R).comp
        (offenderSubgroup (centralOmegaRepresentation K R)).subtype)
        ((centralOmegaComponent K R).subgroupOf (offenderSubgroup (centralOmegaRepresentation K R)))) ∧
    ∃ E : BinaryField, E.degree = n ∧
      (IsLinearNatural (c.sectionData.space.toRepresentation.comp
        ((centralOmegaComponent K R).subgroupOf (offenderSubgroup (centralOmegaRepresentation K R))).subtype) E 3 ∨
      IsRepeatedLinearNatural (c.sectionData.space.toRepresentation.comp
        ((centralOmegaComponent K R).subgroupOf (offenderSubgroup (centralOmegaRepresentation K R))).subtype) E 3 2) := by
  let e := Classical.choice h.model
  have hBO := (centralOmega_source_conclusion h hn).1
  let c := Classical.choice (centralOmega_source_conclusion h hn).2
  let ρ := centralOmegaRepresentation K R
  let O := offenderSubgroup ρ
  let B := (centralOmegaComponent K R).subgroupOf O
  let a : B ≃* centralOmegaComponent K R := subgroupOfEquivOfLe hBO
  let := centralOmegaComponent_quasisimple h hn
  let : IsQuasisimple B := IsQuasisimple.of_mulEquiv a.symm
  have hff : IsFFModule (ρ.comp O.subtype) := by
    obtain ⟨A,hA⟩ := (isFFModule_iff_exists_bestOffender ρ).mp (centralOmega_isFF h hn)
    exact ⟨A.subgroupOf O,(hA.subgroupOf ρ (hA.le_offenderSubgroup ρ)).isOffender _⟩
  let : Algebra (ZMod 2) F := ZMod.algebra F 2
  let E : BinaryField := { Carrier := F, degree := n, degree_pos := by omega, card_eq := h.field_card }
  exact ⟨c,split_natural_or_double_of_full_source (ρ.comp O.subtype) c
    ((centralOmega_actor_sqtk h hn).subgroup O) hff E hn
    (a.trans (centralOmegaFullEquiv h hn e))⟩

end CFSG.Quasithin.ChapterC.LinearThreeMS.NonbinarySource
