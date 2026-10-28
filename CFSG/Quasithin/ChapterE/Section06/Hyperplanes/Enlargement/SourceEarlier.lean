module
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.SourceOvergroups
public import CFSG.Quasithin.ChapterE.Section06.FrobeniusReduction.SourceInputs
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.BlockInspection.Lifting.SourceInputs
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.BlockInspection.Lifting.Three.Placement.Symplectic
/-!
# Original Chapter 1 local inputs for the E.6.8 and E.6.23 consumers

An actual subgroup with nontrivial two-core embeds in the two-local normalizer
of that core. Hypothesis E.6.1 thus gives SQTK for it and its actual two-core
quotient. The complete 1.2.1(3) source now supplies both relative normality/orbit
size and the four-model list; the original 1.2.4 source supplies unique containment.
No abstract quotient actor or extra ordinary-component hypothesis is introduced.
Source: Aschbacher–Smith, 1.2.1(3),1.2.4 and E.6.8/23, pp.504–505,247,254–255.
-/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.Section06
universe u
variable {G : Type u} [Group G] [Finite G]
variable {K : GroupClass.{u}} {T : Sylow 2 G} {M V : Subgroup G}

namespace Hyperplanes.Enlargement.BlockInspection
open Lifting

theorem source_localContainmentInput
    (h : HypothesisE61 KnownSimple.IsKnownSimple T M V) : LocalContainmentInput G := by
  intro H hH S B hB
  exact FrobeniusReduction.source_localContainment H (source_local_sqtk h hH) S B hB

theorem source_componentOrbits
    (h : HypothesisE61 KnownSimple.IsKnownSimple T M V) :
    Three.Placement.EarlierComponentOrbits (G := G) := by
  intro H hH B hB
  exact source_cComponent_orbits_and_models h hH hB
end Hyperplanes.Enlargement.BlockInspection
end CFSG.Quasithin.ChapterE.Section06
