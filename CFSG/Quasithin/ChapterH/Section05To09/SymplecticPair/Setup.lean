module

public import Theory.Representation.SymplecticConjugatePair
public import Theory.GroupTheory.SolvableResidual

/-!
# The actual paired symplectic action for H.7

The source action is identified on the underlying binary space of two natural
four-dimensional modules over the same coefficient field. The second action
is twisted by an actual automorphism exchanging the Dynkin types. The acting
group contains the genuine derived symplectic group as its solvable residual,
and contains an element exchanging the two summands.

These data retain the distinction between Sp₄(2) and Sp₄(2)′. They do not
assume a full Sp₄(2) subgroup in the acting group, any parameter values,
fixed-space bounds, offender exclusions, or the SQTK-image hypothesis (!).
The latter must be supplied separately when proving the β bound.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
standing setup on printed p.377, H.7 on pp.388–389, and the paired-summand
case preceding Table 7.1.1 on p.696. The original module can be transported
to this coordinate carrier by its actual intertwining equivalence.
-/

@[expose] public section

namespace CFSG.Quasithin.ChapterH.Section05To09.SymplecticPair
open Theory.SpecificGroups.SymplecticFour SymplecticConjugatePair

/-- The paired action on the source solvable residual, with an actual acting
overgroup and summand interchange. No numerical conclusions are fields. -/
structure Setup (F M : Type*) [Field F] [Algebra (ZMod 2) F] [Group M] where
  twist : MulAut (Sp F)
  movesDiagram : ¬ DiagramAutomorphisms.PreservesDiagram twist
  action : Representation (ZMod 2) M (Space F)
  faithful : Function.Injective action
  embedding : commutator (Sp F) →* M
  embedding_injective : Function.Injective embedding
  range_eq_residual : embedding.range = Subgroup.solvableResidual M
  restriction : action.comp embedding = derivedPair twist
  interchange : ∃ t : M,
    (∀ v ∈ firstSummand, action t v ∈ secondSummand) ∧
    (∀ v ∈ secondSummand, action t v ∈ firstSummand)

end CFSG.Quasithin.ChapterH.Section05To09.SymplecticPair
