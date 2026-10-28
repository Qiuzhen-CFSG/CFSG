module

public import Theory.SpecificGroups.Alternating.LargeInvolutoryTwoComponents

/-!
# The large alternating branch of the known-simple B₂ input

For every n ≥ 8, every genuine two-component in the fixed subgroup of an
order-two automorphism of Aₙ is quasisimple. The underlying proof uses the
actual permutation centralizer and its normal product base. Catalogue transport
and the combination with A₅, A₆ and A₇ remain with the known-simple assembly.

Sources: GLS II, Definition 2.4 and Lemma 5.28; GLS III, §5.2;
Aschbacher--Smith, I.3, printed p.414.
-/

public section

namespace CFSG.Quasithin.ChapterI.Section03.KnownSimpleB2

/-- The alternating catalogue's full degree-at-least-eight branch. -/
theorem alternating_large (n : ℕ) (hn : 8 ≤ n) :
    Theory.GroupTheory.HasInvolutoryB2 (alternatingGroup (Fin n)) :=
  alternatingGroup.large_hasInvolutoryB2 n hn

end CFSG.Quasithin.ChapterI.Section03.KnownSimpleB2
