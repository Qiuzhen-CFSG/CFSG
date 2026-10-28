module

public import CFSG.Quasithin.ChapterB.Section04.SourceClassification.Triality.RemainingEven
public import CFSG.Quasithin.ChapterA.Section02.SourceAssembly.Complete

/-!
# The original B.4.2 source domain with the full catalogue instantiated

Unconditional Theorems A and C supply the actual central-quotient catalogue.
The completed model-family dispatcher leaves only the even-exponent triality
proper-extension case. Every other source action has a proved corrected row.
Source: Aschbacher--Smith B.4.2 and A.2.1--3.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterB.SourceClassification
universe u v
variable {G : Type u} [Group G] [Finite G]
  {V : Type v} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} {L : Subgroup G}

theorem source_case_or_even_triality
    (h : ChapterK.RankOne.SourceHypotheses ρ L) (hff : IsFFModule ρ) :
    SourceInduction.ProjectiveLine.IrreducibleActionCase ρ L (offenderSubgroup ρ) ∨
      ∃ n : ℕ, 0<n ∧ Even n ∧ Triality.Standard.IsTrialityGroupAt (2^n) (L ⧸ center L) :=
  case_or_even_triality h hff (quotient_model_of_theoremsAC
    ChapterA.Section02.theoremA_knownSimple ChapterA.Section02.theoremC_knownSimple h)

end CFSG.Quasithin.ChapterB.SourceClassification
