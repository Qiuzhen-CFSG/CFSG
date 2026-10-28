module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Swapped.LinearTwo.ModuleAlternatives.F918Sections.NoStrong.IrreducibleReduction
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Swapped.LinearTwo.ModuleAlternatives.F918Sections.NoStrong.StrictModels

/-!
# The irreducible reduction for an external PSL₂ component

The universal input below is the complete B.1.5(3) implication, with
faithfulness, equal-weight minimality, two-residual and relative chief-factor
hypotheses. A strong offender which generates the normal component by
commutation gives a genuine faithful irreducible B.4.2 action. The fixed-space
reduction removes the two-core of the generated actor; its vanishing is never
inferred from a larger group's two-core.

Source: Aschbacher–Smith, B.1.5(3), pp.69–70, B.4.2, p.86, and
13.8.20(a), p.954, combined manuscript of 1 March 2004.
-/

@[expose] public noncomputable section

open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped MatrixGroups
open CFSG.Quasithin.ChapterB
open CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearTwo.ModuleAlternatives.F918Sections.NoStrong
open CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearTwo.ModuleAlternatives.F918Sections.NoStrong.IrreducibleReduction
open CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.RepresentationReduction.SourceRestrictions.FFExclusions

namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.LinearTwo.NoStrongMoved

universe u v w

/-- The full source B.1.5(3) implication. Fixing Irr⁺ means stabilizing its
subspaces, not fixing every vector. No special actor or constituent is selected. -/
def FullIrrInvariance : Prop :=
  ∀ (D : Type u) [Group D] [Finite D] (V : Type v)
    [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (ρ : Representation (ZMod 2) D V), Function.Injective ρ →
    ∀ (A X : Subgroup D), IsMinimalBestOffender ρ A → X ≠ ⊥ →
      pResidual 2 X = ⊤ → ⁅X,A⁆ = X → HasCentralPChiefFactors 2 X →
      ∀ I, IsIrrPlus ρ X I → A ≤ subspaceStabilizer ρ I

variable {𝒦 : GroupClass.{u}} {F : Type w} [Field F] [Finite F] [CharP F 2]

/-- Discharge the specialized stabilization premise of the existing reduction. -/
theorem preaction_impossible (hB42 : FullB42.{u,v} 𝒦)
    (hInv : FullIrrInvariance.{u,v}) (a : Preaction.{u,v,w} 𝒦 F) : False := by
  obtain ⟨b⟩ := a.action_of_stabilization (by
    intro A hA I hI
    obtain ⟨hr, hc, hcomm⟩ := a.stabilization_hypotheses hA.1.1
    have hn : generalizedFitting a.Actor ≠ ⊥ := by
      intro he
      exact hI.not_le_fixedSpace a.representation (by rw [he, fixedSpace_bot]; exact le_top)
    exact hInv a.Actor a.Space a.representation a.faithful A _ hA hn hr hcomm hc I hI)
  exact not_strictRatioModel_psl (b.strictRatioModel hB42)

/-- A strong minimal best offender cannot generate a normal characteristic-two
PSL₂ component by commutation. This allows a nontrivial two-core in the actor. -/
theorem not_strong_of_component_commutator
    (hB42 : FullB42.{u,v} 𝒦) (hInv : FullIrrInvariance.{u,v})
    {D : Type u} [Group D] [Finite D]
    {V : Type v} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (ρ : Representation (ZMod 2) D V) (hf : Function.Injective ρ)
    (hS : IsSQTK 𝒦 D) (L A : Subgroup D) [L.Normal] [IsQuasisimple L]
    (e : L ≃* PSL(2,F)) (hc : ⁅L,A⁆ = L)
    (hA : IsMinimalBestOffender ρ A) : ¬ IsStrongOffender ρ A := by
  intro hs
  let E := L ⊔ A
  let L₀ := L.subgroupOf E
  let A₀ := A.subgroupOf E
  let : L₀.Normal := inferInstance
  let : IsQuasisimple L₀ :=
    IsQuasisimple.of_mulEquiv (subgroupOfEquivOfLe (show L ≤ E from le_sup_left)).symm
  have hc₀ : ⁅L₀,A₀⁆ = L₀ := by
    apply Subgroup.map_injective E.subtype_injective
    rw [Subgroup.map_commutator]
    change ⁅(L.subgroupOf E).map E.subtype, (A.subgroupOf E).map E.subtype⁆ =
      (L.subgroupOf E).map E.subtype
    rw [map_subgroupOf_eq_of_le (show L ≤ E from le_sup_left),
      map_subgroupOf_eq_of_le (show A ≤ E from le_sup_right), hc]
  have hg : L₀ ⊔ A₀ = ⊤ := by
    apply Subgroup.map_injective E.subtype_injective
    rw [Subgroup.map_sup]
    change (L.subgroupOf E).map E.subtype ⊔ (A.subgroupOf E).map E.subtype =
      (⊤ : Subgroup E).map E.subtype
    rw [map_subgroupOf_eq_of_le (show L ≤ E from le_sup_left),
      map_subgroupOf_eq_of_le (show A ≤ E from le_sup_right)]
    exact E.range_subtype.symm.trans E.subtype.range_eq_map
  exact preaction_impossible hB42 hInv
    (preaction_of_generated (ρ.comp E.subtype) (hf.comp E.subtype_injective)
      (hS.subgroup E) L₀ A₀ ((subgroupOfEquivOfLe le_sup_left).trans e)
      hc₀ hg (minimal_subgroupOf ρ hA le_sup_right)
      (strongOffender_subgroupOf ρ hs le_sup_right))

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.LinearTwo.NoStrongMoved
