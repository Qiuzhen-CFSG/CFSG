module

public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.ExceptionalExtension.SplitCase
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.ExceptionalExtension.NonsplitCase.Assembly
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.ExceptionalExtension.NonsplitCase.ExceptionalSplitting.Source
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.ExceptionalExtension.Geometry

/-!
# The exceptional extension argument in the proof of B.5.6

The literal B.5.9--12 configuration supplies G₁, G₂=C_G(G₁), W=[V,G₁]
and V₂=C_V(G₁). Exceptionality constructs a faithful indecomposable four-space
U₁=W+⟨u⟩ and identifies it with V/V₂. Split on whether V is the direct sum
of [V,F*(G₂)] and C_V(F*(G₂)). In the split case, the proved displacement
control makes the saturated first space invariant and gives both summands
in the original quotient V/C_V(G).

In the nonsplit case, a fixed supplement gives the same two-factor alternative.
Otherwise actual cohomology restricts the ordinary second action to natural
SL₂ or at most two binary natural SL₃ copies, giving the full moved-space
hyperplane alternative. For an exceptional second four-space, the proved
chief-factor flags allow B.4.8(4) to construct the required complement and
fixed supplement. Both quotient summands retain every B.4.8(3) clause.

`adequate_of_exceptional` completes this endgame on the original action.
Its only earlier-source inputs are the full `EarlierB48Three` and
`Nonsplit.EarlierB48Four`, owned by `qt-b-04-natural-extensions`. The component
configuration, first exceptionality, nontriviality of G₂ and factor conclusion
remain intermediate inputs for `qt-b05-general-source-induction` to supply.
Final strong induction and earlier-source discharge remain with that parent
and `qt-b05-general-classification`; this is not the universal classifier.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, printed p.110.
-/

public section

namespace CFSG.Quasithin.ChapterB.SourceInduction.ExceptionalExtension

open ComponentReduction

universe u v

variable {G : Type u} [Group G] [Finite G]
  {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V}

/-- The complete exceptional endgame of B.5.6 on the original action.
The split/nonsplit alternative is discharged here; no complement, cohomology
conclusion or classification at the original group order is assumed. -/
theorem adequate_of_exceptional {K : GroupClass.{u}}
    (hyp : FFHypothesis K ρ)
    (h483 : EarlierB48Three.{u,v}) (h484 : Nonsplit.EarlierB48Four.{u,v})
    (c : Conclusion ρ) (he : IsExceptional ρ c.first c.sectionData.space)
    [Nontrivial (second c)] (f : FactorModuleConclusion (secondAction c)) :
    AdequateAlternative ρ := by
  by_cases hs : SplitAtSecond c
  · exact adequate_of_split h483 hyp c he f hs
  · exact Nonsplit.adequate_of_nonsplit hyp h483 h484 c he f hs

end CFSG.Quasithin.ChapterB.SourceInduction.ExceptionalExtension
