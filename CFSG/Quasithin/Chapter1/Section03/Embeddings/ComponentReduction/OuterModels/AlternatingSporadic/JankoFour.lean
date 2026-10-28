module

public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.AdequateLocal
public import Theory.GroupTheory.CyclicNormalOddQuotient

/-!
# The J₄ outer inspection

The binary carrier here is exactly `Janko4.Model`, used by the `.j4` branch of
`ClassificationModels/Families`. Full innerness in `Janko4.AdequateLocal` proves
that its actual outer quotient is trivial, hence a two-group. Transport by
`MulAut.outerCongr` gives the structural restriction for any group equipped
with an actual isomorphism to that carrier. No simplicity or perfectness
assumption is needed by this route.

The original conditional generator-orbit reduction is retained as a separate
API. Its stronger orbit premises are not inferred from the two-group conclusion.

Source: Aschbacher–Smith, combined 1 March 2004 manuscript, Theorem C on
printed p.33 and the proof of 1.3.4 on p.510; GLS3, Table 5.3i.
-/

public section

namespace CFSG.Quasithin.Chapter1.XiEmbedding.OuterModels

open Theory.GroupTheory Janko4.OuterReduction

/-- The retained alternative reduction from two explicit generator-orbit facts. -/
theorem jankoFour_outer_cyclicNormalOddQuotient_of_generator_orbits
    {S : Type*} [Group S] (e : S ≃* Janko4.Model)
    (hfirst : FirstGeneratorSquareConjugacy) (hfixed : FixedGeneratorSquareOrbit) :
    HasCyclicNormalOddQuotient (MulAut.Outer S) := by
  have h := hasCyclicNormalOddQuotient_of_isPGroup_two
    (outer_isPGroup_two_of_generator_orbits hfirst hfixed)
  exact h.of_injective (MulAut.outerCongr e).toMonoidHom
    (MulAut.outerCongr e).injective

/-- Actual carrier transport completes the J₄ outer restriction. -/
theorem jankoFour_outer_cyclicNormalOddQuotient
    {S : Type*} [Group S] (e : S ≃* Janko4.Model) :
    HasCyclicNormalOddQuotient (MulAut.Outer S) := by
  exact (hasCyclicNormalOddQuotient_of_isPGroup_two
    Janko4.AdequateLocal.outer_isPGroup_two).of_injective
      (MulAut.outerCongr e).toMonoidHom (MulAut.outerCongr e).injective

end CFSG.Quasithin.Chapter1.XiEmbedding.OuterModels
