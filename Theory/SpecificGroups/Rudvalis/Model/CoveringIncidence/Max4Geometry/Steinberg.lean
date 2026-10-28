module

public import Theory.SpecificGroups.Rudvalis.Model.CoveringIncidence.Max4Geometry.Natural
public import Theory.SpecificGroups.Rudvalis.Model.CoveringIncidence.Max4Geometry.Words
public import Theory.SpecificGroups.Rudvalis.Model.CoveringIncidence.Max4Geometry.Steinberg.Assembly
public import Theory.SpecificGroups.Rudvalis.Model.CoveringIncidence.Max4Geometry.Steinberg.WordCertificates

/-!
# The actual max4 central quotient as the binary Steinberg module

The first eight fixed words give coordinates on the literal quotient P/Z(P).
An explicit invertible matrix identifies their two conjugation tables with
conjugation on trace-zero endomorphisms of the marked natural module. The
permutation identities are kernel checked on the original Rudvalis carrier;
generation extends equivariance to every element of max4 and every coset.

The only structural premises are that the marked eight-group is Z(P), the
eleven shared words generate P, and P/Z(P) is elementary abelian. Their
independent producer is the special-core calculation; this module does not
claim that the full source theorem follows without that calculation.

Source: Aschbacher--Smith I.2.2(7), printed pp.412--413, and GLS3 Table 5.3r
with its justification on pp.291--292. The original ATLAS words, source
attribution and inverse point-action convention are preserved.
-/

open Subgroup Rudvalis.SylowOvergroups
open Rudvalis.SylowOvergroups.RadicalCoverage.LocalCover
namespace Rudvalis.CoveringIncidence
open Max4Steinberg

variable (hcenter : max4CoreCenter = elementary 2)
variable (hgen : closure (Set.range Max4Words.generator) = max4Core)
variable [IsElementaryAbelian 2 Max4CentralQuotient]

/-- An actual group equivalence on the literal central quotient of the intrinsic core. -/
public noncomputable def max4SteinbergEquiv :
    Max4CentralQuotient ≃* Multiplicative BinaryLinearThree.Steinberg :=
  quotientEquiv hgen hcenter WordCertificates.centralWordIdentities

/-- Both module factors use exactly the actor fixed by the marked natural basis. -/
public theorem max4_steinberg (g : max4) (x : Max4CentralQuotient) :
    (max4SteinbergEquiv hcenter hgen (max4CentralQuotientAction g x)).toAdd =
      BinaryLinearThree.S (max4NaturalActor (QuotientGroup.mk' (pCore 2 max4) g))
        (max4SteinbergEquiv hcenter hgen x).toAdd :=
  quotientEquiv_action_of_wordIdentities hgen hcenter
    WordCertificates.centralWordIdentities WordCertificates.conjugateWordIdentities g x

/-- The intertwiner respects the original projection and actual core conjugation. -/
public theorem max4_steinberg_mk (g : max4) (x : max4Core) :
    (max4SteinbergEquiv hcenter hgen
      (QuotientGroup.mk' (center max4Core) (max4CoreAction g x))).toAdd =
      BinaryLinearThree.S (max4NaturalActor (QuotientGroup.mk' (pCore 2 max4) g))
        (max4SteinbergEquiv hcenter hgen (QuotientGroup.mk' (center max4Core) x)).toAdd := by
  rw [← max4CentralQuotientAction_mk]
  exact max4_steinberg hcenter hgen g _

end Rudvalis.CoveringIncidence
