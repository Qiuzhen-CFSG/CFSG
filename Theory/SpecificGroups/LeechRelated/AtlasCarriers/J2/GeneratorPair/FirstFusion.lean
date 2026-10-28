module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.GeneratorPair
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.GeneratorPair.FirstFusion.Reduction
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.GeneratorPair.FirstFusion.LocalFusion
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.GeneratorPair.FirstFusion.CommutatorCheck

/-!
# First-generator fusion for the ATLAS J₂ generating pair

Every pair satisfying the published word tests has first entry conjugate to
the defining generator `a`, by a conjugator in the actual degree-100 carrier.
The odd centralizer index 315 and Sylow conjugacy move every involution into
the centralizer of `t = (abab⁻¹)⁶`. The checked centralizer enumeration fuses
its nonidentity involutions to `a` or `t`. In the latter case, the checked
commutator implication contradicts the pair's fourth-power inequality.

This assembles the finite certificates without further premises. Source:
ATLAS `J2G1-p100B0`; the two involution classes and the outer-automorphism
application are recorded in GLS3, Table 5.3g.
-/

public section
namespace Sporadic.LeechRelated.J2.GeneratorPair

/-- The first entry of any pair passing the word tests is conjugate to the
standard first generator inside the ATLAS carrier. -/
theorem first_generator_conjugate (x y : Carrier) (h : PairProfile x y) :
    ∃ g : Carrier, x = MulAut.conj g a :=
  first_generator_conjugate_of_finite_checks
    FirstFusion.centralizerElement_cover
    FirstFusion.centralizerElement_involution_fusion
    FirstFusion.commutator_four_on_representatives x y h

end Sporadic.LeechRelated.J2.GeneratorPair
