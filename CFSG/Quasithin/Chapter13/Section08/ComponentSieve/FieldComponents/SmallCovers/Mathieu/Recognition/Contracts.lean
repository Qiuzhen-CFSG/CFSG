module

public import CFSG.Quasithin.Chapter13.Section08.SourceDefs
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Basic
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Mathieu.CentralSeed
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Swapped.LinearTwo.ModuleAlternatives.F918Sections.NoStrong.SourceB42
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Suzuki.NaturalSections.RatioRecognition.SmallRatioSource

/-!
# The outstanding M₂₂ representation deductions

These are output contracts for the remaining two mathematical steps. They
are definitions of obligations, not asserted source theorems or assumptions
on the standing group setup.

The first step must derive `NoFaithfulFF` and `SmallQuadraticCode` from the
full universal B.4.2/B.4.5 implications, using actual M₂₂ model comparisons.
In particular the no-FF conclusion quantifies over all finite faithful
modules, as required by F.9.18(7); it is not the assertion that one chosen
Irr⁺ module fails to be an FF-module.

The second step must construct `CentralWitness` from the genuine source
setup, the complete F.9.18 alternatives, and those proved classification
consequences. Its code identification is on the literal central quotient.
`source_central_code_contradiction_of_group_seed` in the surrounding
Mathieu namespace proves that this output suffices for the
final branch, without assuming a splitting of the Irr⁺ space.

The older `Recognition.F918Selection`, `B45SelectionData.filter`, and
`B42M22Exclusion.eliminate` remain valid conditional interfaces, but do not
establish these source deductions. Their conclusions cannot be used as
unproved source inputs in the final assembly.

Source: Aschbacher–Smith, 13.8.21(2), printed p.956; F.9.18(2–4),(7),
pp.325–326; B.4.2/B.4.5, pp.86–87 (1 March 2004 manuscript).
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative
open CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.RepresentationReduction.SourceRestrictions.Cases
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Mathieu.Recognition
universe u

/-- The required absence of every finite faithful FF-module for an SQTK
actor whose entire generalized Fitting subgroup is the actual M₂₂. -/
def NoFaithfulFF (𝒦 : GroupClass.{u}) : Prop :=
  ∀ (D : Type u) [Group D] [Finite D] (V : Type u)
    [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (ρ : Representation (ZMod 2) D V),
    IsSQTK 𝒦 D → Function.Injective ρ →
    Nonempty (Theory.GroupTheory.generalizedFitting D ≃* Sporadic.Mathieu.M22) →
    ¬ IsFFModule ρ

/-- The unfiltered B.4 classifiers must imply this recognition on the
actual generalized-Fitting restriction, including its intertwining map. -/
def SmallQuadraticCode (𝒦 : GroupClass.{u}) : Prop :=
  ∀ (D : Type u) [Group D] [Finite D] (V : Type u)
    [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (ρ : Representation (ZMod 2) D V), B4Hypotheses 𝒦 ρ →
    quadraticRatio ρ ≤ 2 →
    Nonempty (Theory.GroupTheory.generalizedFitting D ≃* Sporadic.Mathieu.M22) →
    MathieuCode.IsM22Code (ρ.comp (Theory.GroupTheory.generalizedFitting D).subtype)

variable {G : Type u} [Group G] [Finite G]
  {H K L₁ T G₁ M V₃ V₁ : Subgroup G}
  [(V₁.subgroupOf (Source.UH H V₃)).Normal]
  [IsElementaryAbelian 2 (Source.Utilde H V₃ V₁)]

/-- Output of the source F.9.18 assembly, consumed by the proved central-seed
contradiction. Constructing this record, rather than projecting it, is the
remaining representation-selection obligation. -/
structure CentralWitness (s : Placement.Setup H K L₁ T G₁ M)
    (d : SourceAction H V₃ V₁) where
  I : Subrepresentation d.representation
  irrPlus : IsIrrPlus d.representation (Source.starImage H K) I.toSubmodule
  moved : I.toSubmodule = subspaceCommutator d.representation ⊤ (Source.starImage H K)
  code : MathieuCode.IsM22Code
    ((sourceCentralRepresentation H K L₁ T G₁ M V₃ V₁ s d I).comp
      (Source.starImage H K).subtype)

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Mathieu.Recognition
