module

public import CFSG.KnownSimple.CarrierCatalogue
public import CFSG.Quasithin.ChapterD.Section03.SourceConsequences
public import CFSG.Quasithin.ChapterB.InternalThompsonAction
public import Theory.Representation.BinaryOffender.AmbientSectionTransport
public import Theory.Representation.BinaryOffender.MovedDimension

/-!
# The fixed-component classification input and its D.3.20 consumer

The missing B.5 specialization says that a normal quasisimple component
which moves the entire faithful, offender-generated SQTK quotient module,
and has nonzero fixed space there, makes that module Irr⁺. This file states
that input explicitly; it does not assert its universal truth.

The conditional D.3.20 consumer restricts the original faithful action to
its actual normal offender subgroup. The original SQTK cover supplies its
cover, normality supplies its trivial two-core, and the original component,
commutator and fixed-space data survive unchanged. Irr⁺ minimality then
identifies the original seed with the whole module.

Source: Aschbacher--Smith, combined manuscript of 1 March 2004,
D.3.20, printed p.204, using B.5.6 and B.5.1, pp.99--110.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender

namespace CFSG.Quasithin.Chapter3.Section02.ChosenSource325
universe u v

/-- The genuine D.3.1 hypotheses, with the component, offender containment
and nonzero seed fixed space required by D.3.20. There is no invariance field. -/
structure FixedSeedHypotheses
    {H : Type u} [Group H] [Finite H]
    {W : Type v} [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) H W) (T : Sylow 2 H)
    (X : Subgroup H) (I : Submodule (ZMod 2) W) : Prop
    extends ChapterD.Section03.SourceHypotheses KnownSimple.IsKnownSimple ρ T X I where
  component : IsComponent H X
  offender : X ≤ offenderSubgroup ρ
  fixed : I ⊓ fixedSpace ρ X ≠ ⊥

/-- The remaining B.5 classification implication, stated independently of
any chosen seed, normalizer orbit or numerical bound. Its proof is separate. -/
@[expose] def FixedComponentInput : Prop :=
  ∀ {H : Type u} [Group H] [Finite H]
    {W : Type v} [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) H W)
    (_h : ChapterB.SourceInduction.FFHypothesis KnownSimple.IsKnownSimple ρ)
    (X : Subgroup H) [X.Normal] [IsQuasisimple X],
    subspaceCommutator ρ ⊤ X = ⊤ → fixedSpace ρ X ≠ ⊥ → IsIrrPlus ρ X ⊤

/-- Conditional D.3.20, with every offender restriction and cover input
constructed on the original action. The B.5 implication remains explicit. -/
theorem source_seed_eq_top_of_fixedComponent
    (hclass : FixedComponentInput.{u,v})
    {H : Type u} [Group H] [Finite H]
    {W : Type v} [AddCommGroup W] [Module (ZMod 2) W]
    {ρ : Representation (ZMod 2) H W} {T : Sylow 2 H}
    {X : Subgroup H} {I : Submodule (ZMod 2) W}
    (h : ChapterD.Section03.SourceHypotheses KnownSimple.IsKnownSimple ρ T X I)
    (hX : IsComponent H X) (hXO : X ≤ offenderSubgroup ρ)
    (hfix : I ⊓ fixedSpace ρ X ≠ ⊥) : I = ⊤ := by
  let := h.finiteModule
  let := h.normal
  let O := offenderSubgroup ρ
  let σ := ρ.comp O.subtype
  let X₀ := X.subgroupOf O
  let : X₀.Normal := inferInstance
  let : IsQuasisimple X := hX.2
  let : IsQuasisimple X₀ := IsQuasisimple.of_mulEquiv (subgroupOfEquivOfLe hXO).symm
  obtain ⟨c⟩ := h.sqtkQuotient
  have hf : ChapterB.SourceInduction.FFHypothesis KnownSimple.IsKnownSimple σ :=
    ChapterB.InternalThompsonAction.offender_hypothesis ρ
      (c.equiv.toMonoidHom.comp (QuotientGroup.mk' c.kernel))
      (c.equiv.surjective.comp (QuotientGroup.mk'_surjective _))
      c.sqtk h.faithful h.twoCore_eq_bot
  have hm : subspaceCommutator σ ⊤ X₀ = ⊤ := by
    rw [subspaceCommutator_comp_map, map_subgroupOf_eq_of_le hXO]
    exact h.full_commutator
  have hc : fixedSpace σ X₀ ≠ ⊥ := by
    rw [fixedSpace_comp_map, map_subgroupOf_eq_of_le hXO]
    intro he
    apply hfix
    rw [he, inf_bot_eq]
  have hi : IsIrrPlus ρ X ⊤ :=
    (IsIrrPlus.subgroupOf_iff ρ X O hXO ⊤).mp (hclass σ hf X₀ hm hc)
  exact h.seed.eq_of_le ρ hi le_top
end CFSG.Quasithin.Chapter3.Section02.ChosenSource325
