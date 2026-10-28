module

public import CFSG.Quasithin.MainConverse.OddClassicalSections.UnitaryFour.IrreducibleSections.Envelope
public import CFSG.Quasithin.MainConverse.OddClassicalSections.UnitaryFour.IrreducibleSections.MaximalCover.Pullback
public import CFSG.Quasithin.MainConverse.OddClassicalSections.UnitaryFour.IrreducibleSections.MaximalCover.Monomial

/-!
# Maximal irreducible preimages in PSU₄(3): geometric reduction

The basis-line case is proved by its four-letter permutation action with
abelian kernel. General projective models lift through the full scalar kernel,
including a relative normal subgroup and its solvable outer quotient.

The remaining assembly below is conditional. Its three inputs are absolute
irreducibility of an irreducible unitary representation in dimension four,
the remaining imprimitive cases, and coverage of absolutely irreducible
primitive maximal subgroups. None of these inputs is asserted by a definition
or imported maximal-subgroup table. This module retains the final coverage
assembly until all three inputs are proved.

Source: Aschbacher–Smith, Theorem 0.1.2(4) and condition K, printed pp.4 and
482 of `refs/quasithin.pdf`; GLS3, §2.7 for the concrete unitary conventions.
-/

public section
namespace CFSG.Quasithin.MainConverse.UnitaryFourIrreducible

open Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree

/-- Explicit branch reduction, not the unconditional maximal-cover theorem.
The monomial branch has no further premise; the other inputs remain obligations. -/
theorem maximal_preimage_hasSolvableLayersModel_of_geometric_cases
    (habsolute : ∀ U : Subgroup (Carrier 4), ¬ IsReducible U →
      Representation.IsAbsolutelyIrreducible (liftedRepresentation U))
    (himprimitive : ∀ M : Subgroup (Carrier 4), IsCoatom M → ¬ IsReducible M →
      IsImprimitive M → HasSolvableLayersModel (fullPreimage M))
    (hprimitive : ∀ M : Subgroup (Carrier 4), IsCoatom M → ¬ IsReducible M →
      ¬ IsImprimitive M →
      Representation.IsAbsolutelyIrreducible (liftedRepresentation M) →
      HasSolvableLayersModel (fullPreimage M))
    (M : Subgroup (Carrier 4)) (hM : IsCoatom M) (hred : ¬ IsReducible M) :
    HasSolvableLayersModel (fullPreimage M) := by
  classical
  by_cases hmono : IsMonomial M
  · exact .direct (hmono.hasSolvableKernelModel M)
  by_cases himp : IsImprimitive M
  · exact himprimitive M hM hred himp
  exact hprimitive M hM hred himp (habsolute M hred)

end CFSG.Quasithin.MainConverse.UnitaryFourIrreducible
