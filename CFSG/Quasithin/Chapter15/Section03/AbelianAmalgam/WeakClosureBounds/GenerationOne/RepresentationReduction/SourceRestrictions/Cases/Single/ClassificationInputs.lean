module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.SourceOrbit.Selection
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Suzuki.NaturalSections.RatioRecognition.SmallRatioSource
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.WeakClosureBounds.GenerationOne.RepresentationReduction.SourceRestrictions.Cases.Single.ActionHypotheses

/-!
# The complete earlier classification inputs

Reuse the existing, unfiltered F.9.18(4), B.4.2 and B.4.5 interfaces.
`FourConclusion` retains the preliminary component list and all three
alternatives for every homogeneous Irr⁺ section. Its third branch retains
all five natural actions, the separate four-dimensional A₇ alternative,
the actual nonstabilizing T element, the sum in V/C_V(K), and nonisomorphism.
`FullB42` retains all eleven source cases (with their small endpoints).
`FullB45` retains all fourteen table rows and both boundary cases.

These are earlier theorem outputs to be supplied on the specified source
action; no classification theorem is proved in this file. The source owner
must derive F.9.18 from its full coset-geometry setup, SQTK hypothesis,
C-component, quasisimple two-core quotient and generation hypotheses.
The B.4 interfaces themselves retain finite faithful actions, SQTK,
quasisimplicity of the entire generalized Fitting subgroup, irreducibility,
and the best-offender or cubic-ratio hypothesis.

The separate quadratic actor contract lists the exact consequences of
F.9.18(2--3) consumed by `section_B45_hypotheses`. Its last condition is
faithfulness on K by conjugation, not an assumption of section faithfulness.
The edge-core placement of the original actor belongs to the F.9 source
setup and is not needed by this generic representation calculation.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), F.9.18(2--4),
printed pp.325--326; B.4.2/B.4.5, pp.86--87; the use on p.1152.
-/

@[expose] public section

open Subgroup Representation Representation.BinaryOffender
open CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.SourceOrbit
open CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearTwo.ModuleAlternatives.F918Sections.NoStrong
open CFSG.Quasithin.Chapter13.Section08.Components.Suzuki.NaturalSections.RatioRecognition.SmallRatioSource
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.RepresentationReduction.SourceRestrictions.Cases.Single
universe u v
variable {D : Type u} [Group D] {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]

/-- The complete earlier outputs, before any local case elimination. -/
structure ClassificationInputs (𝒦 : GroupClass.{u})
    (ρ : Representation (ZMod 2) D V) (K : Subgroup D) (P : Sylow 2 D) : Prop where
  f918 : FourConclusion ρ K P
  b42 : FullB42.{u,v} 𝒦
  b45 : FullB45.{u,v} 𝒦

/-- Relevant consequences of the common source offender on the original action.
The same A is passed through every submodule and quotient construction. -/
structure CommonQuadraticActor (ρ : Representation (ZMod 2) D V)
    (K T A : Subgroup D) : Prop where
  le_sylow : A ≤ T
  elementary : IsElementaryTwo A
  quadratic : IsQuadratic ρ A
  bound : fixedCodim ρ A ≤ 2 * rank A
  faithful_component : A ⊓ centralizer (K : Set D) = ⊥

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.RepresentationReduction.SourceRestrictions.Cases.Single
