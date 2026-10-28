module

public import CFSG.Quasithin.MainForward.SourceCases.At
public import CFSG.Quasithin.Chapter14.Section08.SourceCases.At

/-!
# A guarded source-input bundle for Theorem D

This module packages exactly the source interfaces consumed by the original
14.8.1--2 five-row dispatcher.  The Structural1222 and Earlier1332 inputs are
requested only at the actual `G,T` after the multiple-overgroup guard; no
universal replacement is inferred.  The A₅ field is the strict 13.6.1 pair of
models used by the standalone Theorem D output.  All other rows retain their
literal quotient, module and model hypotheses through the existing
`SourceCases.At` definitions.

The resulting theorem is conditional on this bundle.  It is deliberately
separate from the unconditional Main-Theorem endpoint: the source producers
for DGS rank-one rows, Chapter 12/13 inputs, MS93, the Rudvalis/G₂ and Ree/U₅
applications, and the marked J₄ branch remain obligations of the fields below
or of their existing producers.  The conclusion is the complete
`IsTheoremDModel`, so its rank-two constructor retains the general ReeF4
family and no partial output predicate is introduced.
-/

@[expose] public section

namespace CFSG.Quasithin.MainForward

open Subgroup Theory.GroupTheory ClassificationModels
open Chapter12.Section02
open Chapter14.Section08.SourceCases
open Chapter1.Section02.LocalModels
open Chapter13.Section03.Noncentrality.SupercriticalSource
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension

universe u
variable {G : Type u} [Group G] [Finite G]

/-- The exact guarded source premises for the strict Theorem D output.

`structural` and `caseOne` are indexed by the actual Sylow subgroup and the
multiple-overgroup guard.  The remaining fields are the unchanged source-row
contracts from `Chapter14.Section08.SourceCases`.
-/
structure TheoremDSourceInputs (G : Type u) [Group G] [Finite G] where
  structural : ∀ T : Sylow 2 G,
    1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard →
    Structural1222At KnownSimple.IsKnownSimple T
  caseOne : ∀ T : Sylow 2 G,
    1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard →
    Earlier1332CaseOneAt T
  catalogue : Catalogue G
  unitary : UnitaryExclusion G
  six : SixRecognition G
  nonabelian : NonabelianRecognition G
  abelian : AbelianRecognition G
  /-- The strict A₅ pair from 13.6.1, not the broader full-model endpoint. -/
  five : ∀ (T : Sylow 2 G) (L : Subgroup G),
    1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard →
    Maximal (Counterexample T) L →
    IsAlternating (L ⧸ pCore 2 L) 5 →
      ClassicalGroup.IsPSU G 4 2 ∨ ClassicalGroup.IsPSL G 4 3

/-- The guarded source bundle yields the complete standalone Theorem D model
for every actual nonempty faithful local family. -/
theorem theoremDModel_of_source_inputs_at
    (s : TheoremDSourceInputs G)
    (h : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hne : (faithfulLocalComponents T).Nonempty) :
    IsTheoremDModel G := by
  exact Chapter14.Section08.SourceCases.At.theoremDModel_of_source_branches
    (s.structural T hmany) (s.caseOne T hmany) s.catalogue s.unitary s.six
    s.nonabelian s.abelian s.five h hmany hne

/-- The corresponding pointwise callback has the exact shape required by the
MainForward D branch. -/
theorem theoremD_of_source_inputs_at
    (s : TheoremDSourceInputs G)
    (h : IsSimpleQTKE KnownSimple.IsKnownSimple G) :
    ∀ T : Sylow 2 G,
      1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard →
      (faithfulLocalComponents T).Nonempty → IsTheoremDModel G := by
  intro T hmany hne
  exact theoremDModel_of_source_inputs_at s h T hmany hne

end CFSG.Quasithin.MainForward

