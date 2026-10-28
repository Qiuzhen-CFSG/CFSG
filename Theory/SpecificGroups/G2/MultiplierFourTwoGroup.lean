module

public import Theory.SpecificGroups.G2.MultiplierFourBound
public import Theory.SpecificGroups.G2.MultiplierFourBound.OddPrimary
public import Theory.GroupTheory.PerfectCentralCoverPGroupKernel
public import Theory.AtlasPort.LinearGroups.G2.FieldTransport

/-!
# The two-primary property of the G₂(4) multiplier

The existing odd-primary exclusions eliminate three and five; cyclic Sylow
transfer eliminates every other odd prime. Thus the actual universal kernel
is a two-group without needing its exact order. Universal covering transfers
this property along the coefficientwise octonion isomorphism to any field
of order four, including a coefficient field in a different universe.

This is the part of the exceptional multiplier calculation consumed by
Chapter 13's literal action-kernel reduction. It allows a nontrivial double
cover and does not assert the unresolved exact multiplier bound.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
I.1.3(1), printed p.407, used in the higher-field branch of 13.6.19, p.931.
The existing octonion field transport retains its ATLAS attribution.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
namespace Atlas.G2.FiniteCover.MultiplierFourBound

/-- The exceptional multiplier's odd-primary calculations already suffice;
no bound on its two-part or assertion of a trivial kernel is necessary. -/
theorem kernel_isPGroup :
    IsPGroup 2 (Atlas.G2.FiniteCover.Kernel Atlas.G2.FiniteCover.FourField) := by
  apply (isPGroup_iff_primeFactors_card_subset (by decide : 2 ≠ 0)).mpr
  intro p hp
  have hp' := Nat.mem_primeFactors.mp hp
  have heq : p = 2 := by
    by_contra h2
    by_cases h3 : p = 3
    · subst p
      exact Atlas.G2.FiniteCover.MultiplierFourBound.OddPrimary.not_three_dvd_card_kernel hp'.2.1
    by_cases h5 : p = 5
    · subst p
      exact Atlas.G2.FiniteCover.MultiplierFourBound.OddPrimary.not_five_dvd_card_kernel hp'.2.1
    exact Atlas.G2.FiniteCover.MultiplierFourBound.not_dvd_card_universal_kernel_of_ne_two_three_five
      hp'.1 h2 h3 h5 hp'.2.1
  norm_num [heq]

variable {F : Type*} [Field F] [Finite F] [Fact (2 < Nat.card F)]

/-- The exceptional calculation applies to every four-element coefficient
field via the actual coefficientwise octonion group isomorphism. -/
theorem universalKernel_isPGroup_of_card_four (hF : Nat.card F = 4) :
    IsPGroup 2 (Atlas.G2.FiniteCover.Kernel F) := by
  let a : F ≃+* Atlas.G2.FiniteCover.FourField := by
    let := Fintype.ofFinite F
    let := Fintype.ofFinite Atlas.G2.FiniteCover.FourField
    apply FiniteField.ringEquivOfCardEq
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hF,
      GaloisField.card 2 2 (by decide)]
    decide
  let b := Atlas.G2.fieldEquiv a
  let c : Covering (Atlas.G2.FiniteCover.CoverGroup F) Atlas.G2.FiniteCover.FourBase :=
    (Covering.ofMulEquiv b).comp (Atlas.G2.FiniteCover.cover F)
  have hp := c.ker_isPGroup_of_universal
    (Atlas.G2.FiniteCover.cover Atlas.G2.FiniteCover.FourField)
    (Atlas.G2.FiniteCover.cover_isUniversal Atlas.G2.FiniteCover.FourField)
    kernel_isPGroup
  have hk : c.toMonoidHom.ker = Atlas.G2.FiniteCover.Kernel F := by
    change (b.toMonoidHom.comp (PerfectCentralCovering.universalProjection
      (Atlas.G2.Model F))).ker = _
    rw [MonoidHom.ker_comp_of_injective _ _ b.injective]
  rwa [hk] at hp

end Atlas.G2.FiniteCover.MultiplierFourBound
