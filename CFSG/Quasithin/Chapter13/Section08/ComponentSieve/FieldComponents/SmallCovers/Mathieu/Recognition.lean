module

public import CFSG.Quasithin.Chapter13.Section08.SourceDefs
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Basic
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Mathieu.SourceSeed
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Swapped.LinearTwo.ModuleAlternatives.F918Sections.NoStrong.SourceB42
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Suzuki.NaturalSections.RatioRecognition.SmallRatioSource

/-!
# The invariant M₂₂ code module in 13.8.21(2)

This file is the representation-selection boundary for the ordinary M₂₂
branch.  The representation supplied by case (i) of F.9.18(4) is an actual
subrepresentation of `Ũ_H`; F.9.18(7) is retained as the explicit saturation
map from its no-FF conclusion to the whole component commutator.  B.4.2 is
used through a precise M₂₂ model-elimination certificate, and B.4.5 retains
both ten-dimensional M₂₂ rows.  The cocode row is removed by the quadratic
bound, leaving an actual group equivalence and an intertwining linear
equivalence with the native M₂₂ code.

No group-family tag is used in place of a model equivalence.  In particular,
the result below returns the literal subrepresentation and its equality with
`subspaceCommutator d.representation ⊤ (Source.starImage H K)`, which is the
interface consumed by `SourceSeed.source_code_contradiction_of_group_seed`.

Source: Aschbacher–Smith, F.9.18(4),(7), printed pp.325–326, B.4.2 and
B.4.5, printed pp.86–87, and 13.8.21(2), printed p.956 (PDF p.973).
-/

@[expose] public noncomputable section

open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative
open CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearTwo.ModuleAlternatives.F918Sections.NoStrong
open CFSG.Quasithin.Chapter13.Section08.Components.Suzuki.NaturalSections.RatioRecognition
open CFSG.Quasithin.Chapter13.Section08.Components.Suzuki.NaturalSections.RatioRecognition.SmallRatioSource
open CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.RepresentationReduction.SourceRestrictions.Cases
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives
open Sporadic.Mathieu

namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Mathieu.Recognition

universe u v

variable {D : Type u} [Group D] [Finite D]
  {V : Type v} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
  {ρ : Representation (ZMod 2) D V}

/-! ## The two M₂₂ rows of Table B.4.5 -/

/-- The two B.4.5 rows whose generalized-Fitting actor is M₂₂.  The
quadratic inequalities are retained from the source rows; they are what
distinguish the code from the cocode below. -/
inductive M22TableCase (ρ : Representation (ZMod 2) D V) : Prop
  | cocode
      (action : ActionEquiv ρ SmallRatioSource.m22Cocode)
      (quadratic : 2 < quadraticRatio ρ)
  | code
      (action : ActionEquiv ρ MathieuCode.m22CodeRepresentation)
      (quadratic : 2 ≤ quadraticRatio ρ)

/-- The result of filtering the complete B.4.5 table by the actual M₂₂
component model.  `filter` is the source model comparison: it is a premise
about the row returned by the universal theorem, not a family-name tag. -/
structure B45SelectionData (𝒦 : GroupClass.{u})
    (ρ : Representation (ZMod 2) D V) where
  fullB42 : FullB42.{u,v} 𝒦
  fullB45 : SmallRatioSource.FullB45.{u,v} 𝒦
  hypotheses : B45Hypotheses 𝒦 ρ
  /-- The actual component comparison used to lift the table action from
  `F*(D)` back to the represented group `D`. -/
  componentEquiv : D ≃* Theory.GroupTheory.generalizedFitting D
  component_coe : ∀ g : D, (componentEquiv g : D) = g
  quadratic_bound : quadraticRatio ρ ≤ 2
  component_quadratic_bound : quadraticRatio (ρ.comp
    (Theory.GroupTheory.generalizedFitting D).subtype) ≤ 2
  filter : ∀ _row : TableB45 ρ (Theory.GroupTheory.generalizedFitting D),
    M22TableCase (ρ.comp (Theory.GroupTheory.generalizedFitting D).subtype)

/-! ## B.4.2's no-FF consequence -/

/-- A precise B.4.2 model-elimination premise for the M₂₂ actor.  The
universal B.4.2 implication is applied to a genuine best offender; the field
only records the source comparison that every resulting action row is
incompatible with the actual M₂₂ component equivalence. -/
structure B42M22Exclusion (𝒦 : GroupClass.{u})
    (ρ : Representation (ZMod 2) D V) where
  hypotheses : B4Hypotheses 𝒦 ρ
  eliminate : IrreducibleActionCase ρ (Theory.GroupTheory.generalizedFitting D)
      (offenderSubgroup ρ) → False

theorem no_ff_of_B42M22Exclusion
    {𝒦 : GroupClass.{u}} (hB42 : FullB42.{u,v} 𝒦)
    (h : B42M22Exclusion (D := D) (V := V) 𝒦 ρ) : ¬ IsFFModule ρ := by
  intro hff
  obtain ⟨A, hA⟩ := h.hypotheses.exists_bestOffender hff
  exact h.eliminate (hB42 D V ρ A hA)

/-! ## Selecting the actual code action -/

omit [Finite D] [Finite V] in
theorem code_of_m22TableCase (h : M22TableCase ρ)
    (hq : quadraticRatio ρ ≤ 2) :
    ∃ e : D ≃* M22, ∃ E : V ≃ₗ[ZMod 2] MathieuCode.M22Code,
      ∀ g v, E (ρ g v) = MathieuCode.m22CodeRepresentation (e g) (E v) := by
  cases h with
  | cocode action quadratic =>
      exact (not_lt_of_ge hq quadratic).elim
  | code action _ =>
      exact ⟨action.groupEquiv, action.linearEquiv, action.intertwines⟩

theorem m22_code_of_B45Selection
    {𝒦 : GroupClass.{u}} (h : B45SelectionData 𝒦 ρ)
    (hnoff : ¬ IsFFModule ρ) :
    ∃ e : D ≃* M22, ∃ E : V ≃ₗ[ZMod 2] MathieuCode.M22Code,
      ∀ g v, E (ρ g v) = MathieuCode.m22CodeRepresentation (e g) (E v) := by
  have hc := h.fullB45 D V ρ h.hypotheses
  cases hc with
  | ff cubic =>
      exact (hnoff (isFFModule_of_cubicRatio_le_one ρ cubic)).elim
  | table lower upper row =>
      obtain ⟨e, E, hE⟩ := code_of_m22TableCase (h.filter row)
        h.component_quadratic_bound
      refine ⟨h.componentEquiv.trans e, E, ?_⟩
      intro g v
      calc
        E (ρ g v) = E (ρ (h.componentEquiv g : D) v) := by
          rw [h.component_coe g]
        _ = MathieuCode.m22CodeRepresentation (e (h.componentEquiv g)) (E v) :=
          hE (h.componentEquiv g) v
  | boundary cubic quadratic alternative =>
      exact (not_lt_of_ge h.quadratic_bound quadratic).elim

/-! ## The F.9.18(4)(i) subrepresentation and F.9.18(7) saturation -/

variable {G : Type u} [Group G] [Finite G]
variable {H K L₁ T G₁ M V₃ V₁ : Subgroup G}

variable [(V₁.subgroupOf (Source.UH H V₃)).Normal]
variable [IsElementaryAbelian 2 (Source.Utilde H V₃ V₁)]

/-- The explicit representation-selection data for case (i) of F.9.18(4).
`I` is already the normal ambient subrepresentation from that case; the
remaining equality is supplied by the conditional F.9.18(7) saturation
clause, whose premise is kept visible. -/
structure F918Selection (d : SourceAction H V₃ V₁)
    (L : Subgroup (Source.Hstar H)) where
  I : Subrepresentation d.representation
  irrPlus : IsIrrPlus d.representation L I.toSubmodule
  noFF : ¬ IsFFModule (I.toRepresentation.comp L.subtype)
  saturation :
    (¬ IsFFModule (I.toRepresentation.comp L.subtype)) →
      I.toSubmodule = subspaceCommutator d.representation ⊤ L

/-- The complete output consumed by the parent M₂₂ contradiction. -/
structure Witness (d : SourceAction H V₃ V₁)
    (L : Subgroup (Source.Hstar H)) where
  I : Subrepresentation d.representation
  moved : I.toSubmodule = subspaceCommutator d.representation ⊤ L
  code : MathieuCode.IsM22Code (I.toRepresentation.comp L.subtype)

theorem select_code
    {d : SourceAction H V₃ V₁} {L : Subgroup (Source.Hstar H)}
    (sel : F918Selection d L)
    {𝒦 : GroupClass.{u}}
    (classification : B45SelectionData 𝒦
      (sel.I.toRepresentation.comp L.subtype)) :
    Nonempty (Witness d L) := by
  obtain ⟨e, E, hE⟩ := m22_code_of_B45Selection classification sel.noFF
  refine ⟨⟨sel.I, sel.saturation sel.noFF, ?_⟩⟩
  exact ⟨e, E, hE⟩

/-- The source assembly with B.4.2's actual no-FF deduction.  The
`B42M22Exclusion` premise compares every genuine B.4.2 action output with
the M₂₂ component model; `select_code` then uses that derived absence both
for the F.9.18(7) saturation clause and for the B.4.5 alternatives. -/
theorem select_code_of_B42_and_B45
    {d : SourceAction H V₃ V₁} {L : Subgroup (Source.Hstar H)}
    (sel : F918Selection d L)
    {𝒦 : GroupClass.{u}}
    (classification : B45SelectionData 𝒦
      (sel.I.toRepresentation.comp L.subtype))
    (exclusion : B42M22Exclusion 𝒦
      (sel.I.toRepresentation.comp L.subtype)) :
    Nonempty (Witness d L) := by
  have hnoff := no_ff_of_B42M22Exclusion classification.fullB42 exclusion
  exact select_code { sel with noFF := hnoff } classification

/-- The specialization used by 13.8.21(2), with the actual component image
and the source module carrier. -/
theorem select_code_of_source
    (_s : ComponentSieve.FieldComponents.SmallCovers.Mathieu.Placement.Setup
      H K L₁ T G₁ M)
    (d : SourceAction H V₃ V₁)
    (sel : F918Selection d (Source.starImage H K))
    {𝒦 : GroupClass.{u}}
    (classification : B45SelectionData 𝒦
      (sel.I.toRepresentation.comp (Source.starImage H K).subtype)) :
    Nonempty (Witness d (Source.starImage H K)) :=
  select_code sel classification

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Mathieu.Recognition
