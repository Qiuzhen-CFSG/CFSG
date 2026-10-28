module

public import Theory.SpecificGroups.HigherClassicalCovers.UnitaryOrdinary.FiveFourClosure.Reduction
public import Theory.SpecificGroups.HigherClassicalCovers.UnitaryOrdinary.Universality

/-!+# Local-section assembly for the SU₅(4) natural cover

The prime-degree local sections feed the arbitrary-form central-closure
reduction. Perfectness of SU₅(4) is already proved, so this gives precisely
the premise of `naturalCover_isUniversal_of_closed` for the literal natural
projection to PSU₅(4), in every target universe.

This module currently retains the two local-section premises. It does not
assert central closure or the source multiplier theorem without them.
Their defining-prime and odd-prime constructions are independent; this
module owns their eventual discharge and assembly.

Source: Aschbacher--Smith I.1.4(4), printed p.408 of `refs/quasithin.pdf`,
and GLS3 Section 6.1. The scalar kernel C₅ is a separate proved calculation.
-/

public section

open BenderSuzuki.MatrixGroups Theory.GroupTheory
open HermitianForm.IdentityGram

namespace Theory.SpecificGroups.HigherClassicalCovers.UnitaryOrdinary.FiveFourClosure

universe u w
variable {F : Type u} [Field F] [Finite F]

/-- Application to the actual natural covering. Only the two local prime-degree
section calculations remain; form transport, perfectness, arbitrary kernel
orders, and the universal-property comparison are all discharged.
-/
theorem naturalCover_isUniversal_of_identity_primary_sections
    (J : HermitianForm 5 F) (hcard : Nat.card F = 16)
    (hconj : ∀ x, J.conj x = x ^ 4)
    [IsQuasisimple (ProjectiveSpecialUnitaryMatrixGroup J)]
    (htwo : PrimeLocalSections (identityGram J) 2)
    (hodd : ∀ p : ℕ, p.Prime → p ≠ 2 → PrimeLocalSections (identityGram J) p) :
    letI := fiveFour_isPerfect J hcard hconj
    letI := natural_isQuasisimple J
    Covering.IsUniversal.{u, u, w} (naturalCover J) := by
  let := fiveFour_isPerfect J hcard hconj
  exact naturalCover_isUniversal_of_closed J
    (fun E _ _ c => injective_of_identity_primary_sections J hcard hconj htwo hodd c)

end Theory.SpecificGroups.HigherClassicalCovers.UnitaryOrdinary.FiveFourClosure
