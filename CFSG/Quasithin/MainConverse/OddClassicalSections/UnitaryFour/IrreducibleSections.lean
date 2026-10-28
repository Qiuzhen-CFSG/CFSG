module

public import CFSG.Quasithin.MainConverse.SolvableSections
public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree.Model
public import CFSG.Quasithin.MainConverse.OddClassicalSections.UnitaryFour.IrreducibleSections.Envelope
public import CFSG.Quasithin.MainConverse.OddClassicalSections.UnitaryFour.IrreducibleSections.Models

/-!
# Irreducible proper subgroups of PSU₄(3): section reduction

Source: Aschbacher–Smith, Theorem 0.1.2(4), condition K, printed pp.4
and 482 of `refs/quasithin.pdf`; GLS3, §2.7 for the matrix conventions.

Pass from a proper irreducible subgroup to a maximal overgroup. Its full
SU inverse image remains irreducible. A representation with solvable kernel,
possibly on a normal subgroup with solvable outer quotient, reduces its
simple sections to those of the actual smaller target group. Projecting back
to the projective subgroup and restricting to the original subgroup
preserves the section conclusion.

The theorem below is conditional: exhaustive maximal-subgroup coverage and
the three smaller-model section calculations have not yet been assembled.
It is not the completed irreducible branch of condition K. This module
retains ownership of that final assembly and of discharging every premise.
-/

namespace CFSG.Quasithin.MainConverse

open CFSG.KnownSimple
open Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree
open UnitaryFourIrreducible

/-- Conditional maximal-overgroup reduction, using the full scalar preimage.
The quotient normal subgroup is normal inside U, as required by condition K. -/
public theorem psu4_three_irreducible_simpleQuotient_of_maximal_preimage_models
    (hcover : ∀ M : Subgroup (Carrier 4), IsCoatom M → ¬ IsReducible M →
      HasSolvableLayersModel (fullPreimage M))
    (hperm : IsKGroup IsConstructedCarrier PermutationTarget)
    (hlinear : IsKGroup IsConstructedCarrier LinearTarget)
    (hsymp : IsKGroup IsConstructedCarrier SymplecticTarget)
    (U : Subgroup (Carrier 4)) (hU : U ≠ ⊤) (hred : ¬ IsReducible U)
    (N : Subgroup U) [N.Normal] [IsSimpleGroup (U ⧸ N)] :
    IsConstructedCarrier (U ⧸ N) := by
  obtain ⟨M, hM, hUM, hMred⟩ := exists_irreducible_coatom U hU hred
  have hpre : IsKGroup IsConstructedCarrier (fullPreimage M) :=
    (hcover M hM hMred).isKGroup hperm hlinear hsymp
  have hMk : IsKGroup IsConstructedCarrier M :=
    hpre.of_surjective (preimageProjection M) (preimageProjection_surjective M)
  have hUk : IsKGroup IsConstructedCarrier U :=
    hMk.of_injective (Subgroup.inclusion hUM) (Subgroup.inclusion_injective hUM)
  exact (hUk.quotient N).mem

end CFSG.Quasithin.MainConverse
