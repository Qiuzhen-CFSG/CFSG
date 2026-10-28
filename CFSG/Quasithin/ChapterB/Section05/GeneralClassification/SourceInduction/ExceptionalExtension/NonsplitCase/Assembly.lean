module

public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.ExceptionalExtension.Construction
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.ExceptionalExtension.Geometry
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.ExceptionalExtension.NonsplitCase.Ordinary
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.ExceptionalExtension.NonsplitCase.ExceptionalSplitting.Source

/-!
# The nonsplit second-core branch of B.5.6

First separate the case C_V(G₂) + V₂ = V, where the fixed supplement
already constructs the two quotient summands. Failure of splitting over
F*(G₂) alone does not imply that this supplement is proper.

When the supplement is proper, the ordinary cohomology theorem identifies
the action on the actual second moved space: a natural SL₂ action on its
fixed quotient, or at most two natural binary SL₃ copies. The moved-space
supplement equality then gives the full hyperplane conclusion. The other
factor alternative supplies an exceptional four-dimensional section;
genuine B.4.8(4) constructs its ambient complement and a vector fixed by G₂,
giving both full B.4.8(3) records on the summands in V/C_V(G).

The only earlier-source inputs are `ExceptionalExtension.EarlierB48Three`
and `Nonsplit.EarlierB48Four`, owned by `qt-b-04-natural-extensions`. The
component configuration, first exceptionality and factor conclusion are the
supplied B.5.9–12 outputs; their construction and the split/nonsplit assembly
remain with `qt-b05-induction-exceptional-extension`. No cohomology, fixed
kernel, supplement, complement or original-order classification premise is
left in the theorem below.

This leaf sits above both branch modules. Importing it from NonsplitCase
would cycle through the exceptional splitting consumer; the final assembly
owner should import this leaf directly.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), final proof
of B.5.6, printed p.110, source text lines 5733–5744; B.4.8(3)–(4), p.91.
-/

public section

open Subgroup Representation Representation.BinaryOffender

namespace CFSG.Quasithin.ChapterB.SourceInduction.ExceptionalExtension.Nonsplit

open ComponentReduction

universe u v

variable {G : Type u} [Group G] [Finite G]
  {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V}

/-- The nonsplit L₂ branch retains both the full hyperplane alternative and
the two-factor alternative on V/C_V(G), including all B.4.8(3) clauses. -/
theorem adequate_of_nonsplit {K : CFSG.Quasithin.GroupClass.{u}}
    (hyp : FFHypothesis K ρ)
    (h483 : EarlierB48Three.{u,v}) (h484 : EarlierB48Four.{u,v})
    (c : Conclusion ρ) (he : IsExceptional ρ c.first c.sectionData.space)
    [Nontrivial (second c)]
    (f : FactorModuleConclusion (secondAction c)) (hns : ¬ SplitAtSecond c) :
    AdequateAlternative ρ := by
  let := hyp.finite_module
  by_cases hs : fixedSpace ρ (second c) ⊔ c.productConfiguration.fixed.toSubmodule = ⊤
  · exact adequate_of_fixed_second_supplement h483 c he f hs
  · rcases factor_cases c f with hf | hq
    · exact adequate_of_second_action c he
        (second_supplement_of_moved_factor c he f hf.1)
        (ordinary_secondCase_of_nonsplit hyp h484 c he f hf hns hs)
    · obtain ⟨q⟩ := hq
      exact ExceptionalSplitting.adequate_of_exceptional_fourSection h483 h484 c he f q

end CFSG.Quasithin.ChapterB.SourceInduction.ExceptionalExtension.Nonsplit
