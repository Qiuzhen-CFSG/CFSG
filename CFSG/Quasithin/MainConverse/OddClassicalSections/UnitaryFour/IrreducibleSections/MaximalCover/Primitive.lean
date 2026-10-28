module

public import CFSG.Quasithin.MainConverse.OddClassicalSections.UnitaryFour.IrreducibleSections.Envelope
public import CFSG.Quasithin.MainConverse.OddClassicalSections.UnitaryFour.IrreducibleSections.MaximalCover.Geometry
public import CFSG.Quasithin.MainConverse.OddClassicalSections.UnitaryFour.IrreducibleSections.MaximalCover.Primitive.SymplecticSubfield
public import Theory.PGroupCore

/-!+# Primitive absolutely irreducible maximals in PSU₄(3)

The symplectic subfield case is proved using actual matrices and an exact
calculation of the scalar kernel. Outside that case, partition by the
two-core of the projective subgroup, with normality taken inside that subgroup.
The two remaining branch results below are explicit premises and remain to be
proved; this module does not yet assert unconditional primitive coverage.

Source obligation: Aschbacher–Smith, Theorem 0.1.2(4), condition K, printed
pp.4 and 482 of `refs/quasithin.pdf`; GLS3, §2.7 for model conventions.
The inherited ambient simplicity and noncommutativity hypotheses may be used
when constructing the two branch inputs. The assembly itself does not need them.
-/

public section
namespace CFSG.Quasithin.MainConverse.UnitaryFourIrreducible

open Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree
open Primitive

/-- Conditional assembly with the concrete symplectic branch discharged.
Both two-core premises must be established before asserting exhaustive coverage. -/
theorem primitive_preimage_hasSolvableLayersModel_of_twoCore_cases
    (htwo : ∀ M : Subgroup (Carrier 4), IsCoatom M → ¬ IsReducible M →
      ¬ IsImprimitive M →
      Representation.IsAbsolutelyIrreducible (liftedRepresentation M) →
      pCore 2 M ≠ ⊥ → HasSolvableLayersModel (fullPreimage M))
    (hzero : ∀ M : Subgroup (Carrier 4), IsCoatom M → ¬ IsReducible M →
      ¬ IsImprimitive M →
      Representation.IsAbsolutelyIrreducible (liftedRepresentation M) →
      pCore 2 M = ⊥ → ¬ IsSymplecticSubfield M →
      HasSolvableLayersModel (fullPreimage M))
    (M : Subgroup (Carrier 4)) (hM : IsCoatom M) (hred : ¬ IsReducible M)
    (hprim : ¬ IsImprimitive M)
    (habs : Representation.IsAbsolutelyIrreducible (liftedRepresentation M)) :
    HasSolvableLayersModel (fullPreimage M) := by
  classical
  by_cases hsymp : IsSymplecticSubfield M
  · exact .direct (hsymp.fullPreimage_hasSolvableKernelModel M)
  by_cases hcore : pCore 2 M = ⊥
  · exact hzero M hM hred hprim habs hcore hsymp
  · exact htwo M hM hred hprim habs hcore

end CFSG.Quasithin.MainConverse.UnitaryFourIrreducible
