module

public import Theory.Representation.SU3.FiveSmallModules.Degrees.PrincipalSeriesFiltration.CubicCalculation.ModelFlag.Coordinates.FiniteGroup.Transport
public import Theory.Representation.SU3.FiveSmallModules.Degrees.PrincipalSeriesFiltration.CubicCalculation.ModelFlag.Coordinates.FiniteGroup.RootWitness
public import Theory.Representation.SU3.FiveSmallModules.Degrees.PrincipalSeriesFiltration.CubicCalculation.ModelFlag.Coordinates.FiniteGroup.CosetSeparation
public import Theory.Representation.SU3.FiveSmallModules.Degrees.PrincipalSeriesFiltration.CubicCalculation.ModelFlag.Coordinates.FiniteGroup.Generation

/-!
# Canonical group-certificate assembly for the cubic principal series

The checked finite matrices give 126 distinct right cosets of the literal
upper-root-and-full-torus Borel. The fixed pair generates that entire Borel
and every representative; the canonical coset count then proves generation
of the full special-unitary group. Transport through the actual field and
Borel isomorphisms gives every field of `GroupCertificate`, including all
252 root–torus transitions and their retained cubic exponents.

`group_certificate_of_canonical_card` discharges both geometric inputs using
only the supplied count. The parent coordinate comparison applies this
certificate to the literal induction quotient.

Source motivation: Guralnick–Malle Proposition 4.3, p.10, and
Aschbacher–Smith K.2, p.453.
-/

public noncomputable section
namespace Representation.SU3.FiveSmallModules.Degrees.CubicCalculation.ModelFlag

/-- All other fields of the actual canonical certificate have been discharged. -/
theorem group_certificate_of_finite_separation_and_generation
    (hsep : ∀ i j, FiniteGroup.representative i * (FiniteGroup.representative j)⁻¹ ∈
      standardBorel FiniteGroup.fieldForm → i = j)
    (hgen : Subgroup.closure (Set.range FiniteGroup.generator) = ⊤) :
    Nonempty GroupCertificate :=
  ⟨FiniteGroup.certificate hsep hgen⟩

/-- The complete canonical group certificate, with only the canonical coset count assumed. -/
theorem group_certificate_of_canonical_card
    (hcard : Nat.card TrivialCalculation.CanonicalPoints = 126) :
    Nonempty GroupCertificate :=
  ⟨FiniteGroup.certificate_of_canonical_card hcard FiniteGroup.representatives_separate⟩

end Representation.SU3.FiveSmallModules.Degrees.CubicCalculation.ModelFlag
