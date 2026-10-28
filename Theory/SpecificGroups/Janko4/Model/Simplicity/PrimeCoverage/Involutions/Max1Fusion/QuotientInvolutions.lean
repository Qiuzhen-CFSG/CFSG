module

public import Theory.SpecificGroups.Janko4.Model.Simplicity.PrimeCoverage.Involutions.Max1Fusion.QuotientInvolutions.Bridge
public import Theory.SpecificGroups.Janko4.Model.Simplicity.PrimeCoverage.Involutions.Max1Fusion.QuotientInvolutions.SylowReduction
public import Theory.SpecificGroups.Janko4.Model.Simplicity.PrimeCoverage.Involutions.Max1Fusion.QuotientInvolutions.SylowCard
public import Theory.SpecificGroups.Janko4.Model.Simplicity.PrimeCoverage.Involutions.Max1Fusion.QuotientInvolutions.SylowFusion
public import Theory.SpecificGroups.Janko4.Model.Simplicity.PrimeCoverage.Involutions.Max1Fusion.OutsideReduction

/-!
# Assembly of the quotient-involution coverage from finite Sylow certificates

The actual local quotient is identified with the concrete star group, with
both local generators preserved. A subgroup-order certificate and a fusion
certificate inside the fixed Sylow candidate then give exactly the quotient
premise needed by `outside_coverage_of_quotient_and_fibers`.

The certified order 1024 makes the candidate a Sylow 2-subgroup. Its exhaustive
word table and checked conjugators establish fusion to the two marked words.
Sylow conjugacy and the marked quotient isomorphism therefore give coverage
of every involution in the actual local quotient, with no certificate premises.
Source: the literal ATLAS `J4G1-max1W1` program, documented in
`Cardinality.Subgroup`, and the concrete star certificates in `LocalOrder`.
-/

public section
namespace Janko4.Simplicity.Max1Fusion
open Cardinality Cardinality.QuotientCount.Image QuotientInvolutions

/-- The precise outside-reduction premise, conditional only on the two
concrete certificates for the fixed star Sylow candidate. -/
theorem quotient_involution_coverage_of_sylow_certificates
    (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1)
    (hcard : Nat.card sylowCandidate = 1024)
    (hlocal : ∀ w : StarGroup, w ∈ sylowCandidate → orderOf w = 2 →
      ∃ g : StarGroup,
        starFirst = g * w * g⁻¹ ∨ (starFirst * starSecond)^7 = g * w * g⁻¹) :
    ∀ w : LocalQuotient hA hB, orderOf w = 2 → ∃ g : LocalQuotient hA hB,
      QuotientGroup.mk' (localKernel hA hB) (localX hA hB) = g * w * g⁻¹ ∨
      QuotientGroup.mk' (localKernel hA hB) ((localX hA hB * localY hA hB)^7) =
        g * w * g⁻¹ :=
  quotient_coverage_of_star_coverage hA hB
    (star_coverage_of_sylow_certificates hcard hlocal)

/-- Every involution in the actual local quotient is conjugate, within that
quotient, to the image of `x` or `(xy)^7`. This discharges the quotient premise
of `outside_coverage_of_quotient_and_fibers`. -/
theorem quotient_involution_coverage
    (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1) :
    ∀ w : LocalQuotient hA hB, orderOf w = 2 → ∃ g : LocalQuotient hA hB,
      QuotientGroup.mk' (localKernel hA hB) (localX hA hB) = g * w * g⁻¹ ∨
      QuotientGroup.mk' (localKernel hA hB) ((localX hA hB * localY hA hB)^7) =
        g * w * g⁻¹ :=
  quotient_involution_coverage_of_sylow_certificates hA hB
    sylowCandidate_card sylowCandidate_involution_coverage

end Janko4.Simplicity.Max1Fusion
