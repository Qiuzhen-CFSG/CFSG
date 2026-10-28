module
public import CFSG.Quasithin.Chapter12.Section02.ModuleClassification.Catalogue
public import CFSG.Quasithin.Chapter12.Section02.ModuleClassification.RankOneRecovery
public import CFSG.Quasithin.Chapter12.Section02.ModuleClassification.RankOne
public import CFSG.Quasithin.Chapter12.Section02.ModuleClassification.SourceComparison
public import CFSG.Quasithin.Chapter12.Section02.ModuleClassification.NormalizerTransport
public import CFSG.Quasithin.Chapter12.Section02.ModuleClassification.FFSource
public import CFSG.Quasithin.Chapter12.Section02.ModuleClassification.FullNormalizer

/-!
# Conditional assembly of the actual B.5 row comparisons

The source conclusion now gives a printed module alternative, a recovered
PSL2 actor, or precisely the existing nonbinary-natural input. The rank-one
and Chapter11 source implications remain explicit and must be discharged
by their source producers. Every B.5 sum row is consumed in this assembly.
Source: Aschbacher--Smith 6.2.20, 11.0.1 and 12.2.2, pp.691,759--760,795.
-/
public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule.LiteralComparison
open ChapterB.QuasisimpleSource ChapterB.QuasisimpleSource.ExtensionConsequences
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : ChosenModule T L V} {H : Type*} [Group H] [Finite H]
    {ρ : Representation (ZMod 2) H D.space} {K : Subgroup H}
    (c : D.LiteralComparison ρ K)
include c

theorem alternatives_of_irreducible_source_exits_of_many
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (horbits : componentOrbit V (normalizer (L : Set G)) = V ∨
      (componentOrbit V (T : Subgroup G) = V ∧ V ⊓ centralizer (L : Set G) = ⊥))
    (hff : IsFFModule (normalizerRepresentation D.chosenAction))
    (hrank : ∀ n, 1 < n → ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n) →
      Chapter6.Source.IsConjugationModel L V Chapter6.Source.a5Module)
    (hnonbinary : D.NonbinaryNaturalInput → False)
    (s : MovedSection ρ K) (hi : IrreducibleAlternative K s) :
    ModuleAlternatives1222 D := by
  have hr := c.irreducible_rows h.quasisimple s hi
  rcases hr with hm | ⟨F,⟨e⟩⟩ | ⟨F,hF,hn⟩
  · exact hm
  · obtain ⟨hF,hpsl⟩ := c.rankOne_marking h.quasisimple F e.groupEquiv
    exact D.alternatives_of_a5_conjugationModel (hrank F.degree hF hpsl)
  · obtain ⟨S⟩ := c.nonbinaryInput_of_source_branch h hmany horbits hff s
      (hi.faithful.comp K.subtype_injective) F hF hn
    exact (hnonbinary S).elim

theorem alternatives_of_source_exits_of_many
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (horbits : componentOrbit V (normalizer (L : Set G)) = V ∨
      (componentOrbit V (T : Subgroup G) = V ∧ V ⊓ centralizer (L : Set G) = ⊥))
    (hff : IsFFModule (normalizerRepresentation D.chosenAction))
    (hrank : ∀ n, 1 < n → ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n) →
      Chapter6.Source.IsConjugationModel L V Chapter6.Source.a5Module)
    (hnonbinary : D.NonbinaryNaturalInput → False)
    (b : QuasisimpleSourceConclusion ρ K) : ModuleAlternatives1222 D := by
  have hr := c.source_irreducible_or_single b
  rcases hr with hi | ⟨d,hd,⟨e⟩⟩
  · exact c.alternatives_of_irreducible_source_exits_of_many
      h hmany horbits hff hrank hnonbinary b.sectionData hi
  · have hp := c.projection_injective_of_binaryLinear h.quasisimple hd e.groupEquiv
    exact .linear d (Or.inr hd) ((c.wholeMarking b.sectionData hp).trans e)

end CFSG.Quasithin.Chapter12.Section02.ChosenModule.LiteralComparison
