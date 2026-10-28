module

public import CFSG.Quasithin.Chapter1.Section01QuasisimpleInvolutions.Reduction
public import Theory.SpecificGroups.Held.Automorphisms.Realization.MarkedConjugacy.NormalizedPairs.ClassB.Closure.Application

/-!
# The complete marked quasisimple involution classification

The original marked involution and full Theorem C central-quotient list
imply the six-constructor model/action conclusion. The source-family
reduction settles every family except Held. The proved permutation
realization of every automorphism of the actual Held carrier discharges
that final branch through its pointwise Sylow-two calculation.

No action classification, cover bound or concrete-family realization is
an input to this theorem. The ambient source application supplies only
the original marked hypotheses and the earlier Theorem C quotient list.
Source: Aschbacher--Smith 1.1.5(3), printed pp.501--503.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter1.QuasisimpleInvolutions
open Chapter15.Section03.Candidates.ComponentStructure ChapterA.Section02
variable {L : Type*} [Group L] [Finite L] [IsQuasisimple L]
  {α : MulAut L} {P : Sylow 2 L}

/-- Full source classification from the original marked hypotheses and the
complete earlier central-quotient catalogue. -/
theorem MarkedInvolution.classify (d : MarkedInvolution α P)
    (h : IsTheoremCModel (L ⧸ center L)) : ModelAction115 L α := by
  rcases d.source_reduction_he h with hm | hh
  · exact hm
  · obtain ⟨e⟩ := hh
    exact d.modelAction_he_of_realization e Held.Realization.normalizer_surjective

end CFSG.Quasithin.Chapter1.QuasisimpleInvolutions
