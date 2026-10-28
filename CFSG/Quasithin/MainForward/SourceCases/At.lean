module

public import CFSG.Quasithin.MainForward.SourceCases
public import CFSG.Quasithin.Chapter14.Section08.SourceCases.At

/-!
# The forward classification from guarded local Chapter12 inputs

The completed Chapter2 theorem handles the unique-overgroup case. Only after
the existing MainForward reduction produces |M(T)| > 1 and a nonempty faithful
family do we request structure and naturality at that same G,T. The Chapter14
dispatcher then supplies the full model output, including the A₅ terminal case.

The separate E input and all source recognition premises remain explicit.
This is the local conditional counterpart of `forward_of_local_source_branches`;
the existing universal API is unchanged. Source: Aschbacher--Smith, 14.8.1--2
and the Main Theorem proof on printed p.1166.
-/

public section
namespace CFSG.Quasithin.MainForward

open Subgroup Theory.GroupTheory ClassificationModels
open Chapter12.Section02 Chapter14.Section08.SourceCases

universe u
variable {G : Type u} [Group G] [Finite G]

/-- Request the two local predecessors only in the multiple-overgroup branch
where their independent producers apply. -/
theorem forward_of_local_source_branches_at
    (structural : ∀ T : Sylow 2 G,
      1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard →
      Structural1222At KnownSimple.IsKnownSimple T)
    (caseOne : ∀ T : Sylow 2 G,
      1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard → Earlier1332CaseOneAt T)
    (catalogue : Catalogue G) (unitary : UnitaryExclusion G)
    (six : SixRecognition G) (nonabelian : NonabelianRecognition G)
    (abelian : AbelianRecognition G) (five : FiveRecognition G)
    (h : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hE : ∀ T : Sylow 2 G,
      1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard →
      faithfulLocalComponents T = ∅ → IsTheoremEModel G) : IsQTKEModel G := by
  apply forward_of_nonempty_models_and_theoremE h ?_ hE
  intro T hmany hne
  exact At.qtkeModel_of_source_branches (structural T hmany) (caseOne T hmany)
    catalogue unitary six nonabelian abelian five h hmany hne

end CFSG.Quasithin.MainForward
