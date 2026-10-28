module

public import Theory.SpecificGroups.ReeTwo.ParabolicLinearAction.Restrictions
public import Theory.LinearAlgebra.BinaryFivePointStabilizer

/-!
# The concrete marked linear representation of the Ree local group

The derived-coordinate representation is induced by actual conjugation, fixes
the last-root mark, and has kernel exactly the derived centralizer. Its faithful
quotient representation sends the core quotient onto the full displacement
kernel of the binary point stabilizer. The explicit core preimages also lie in
the characteristic omega subgroup, so the same conclusion holds for all three
specified character kernels, with their relative centralizers.

This module records the image equalities using the intrinsic two-core of the
point stabilizer, as needed for pulling normality back through the faithful
quotient maps. It makes no ambient Ree or Tits identification.

Source: Aschbacher--Smith, Lemma 14.2.21, printed p.989 (PDF p.1006), and
Aschbacher, *The Tits group as a standard subgroup* (1982), Section 3.
-/

namespace ReeTwo.Centralizer
open Subgroup Theory.LinearAlgebra.BinaryFivePointStabilizer

/-- The actual core quotient maps precisely onto the point stabilizer's two-core. -/
public theorem core_quotient_image_eq_pCore :
    (core.map (QuotientGroup.mk' (centralizer (derived : Set Centralizer)))).map
      faithfulMarkedRepresentation = pCore 2 (stabilizer markedVector) := by
  rw [pCore_eq_kernel markedVector markedVector_ne_zero derivedSpace_finrank]
  exact core_quotient_markedRepresentation_image

/-- The same equality for any restricted actor containing the characteristic omega subgroup. -/
public theorem restricted_core_quotient_image_eq_pCore (L : Subgroup Centralizer)
    (hL : (omega₁ Core (p := 2)).map
      (SemidirectProduct.inl : Core →* Centralizer) ≤ L) :
    ((core.subgroupOf L).map (QuotientGroup.mk' (derivedCentralizerIn L))).map
      (restrictedFaithfulMarkedRepresentation L) = pCore 2 (stabilizer markedVector) := by
  rw [pCore_eq_kernel markedVector markedVector_ne_zero derivedSpace_finrank]
  exact restricted_core_quotient_markedRepresentation_image L hL

/-- Each specified character kernel supplies the full two-core image for its faithful quotient. -/
public theorem character_kernel_core_quotient_image_eq_pCore
    (χ : Centralizer →* FiveFour.Cyclic 2)
    (hχ : χ = character ∨ χ = coreCharacter ∨ χ = mixedCharacter) :
    ((core.subgroupOf χ.ker).map (QuotientGroup.mk' (derivedCentralizerIn χ.ker))).map
      (restrictedFaithfulMarkedRepresentation χ.ker) = pCore 2 (stabilizer markedVector) := by
  rw [pCore_eq_kernel markedVector markedVector_ne_zero derivedSpace_finrank]
  exact character_kernel_core_quotient_image χ hχ

end ReeTwo.Centralizer
