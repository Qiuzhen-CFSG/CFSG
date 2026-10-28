module

public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalOrder.QuotientCount.Action
public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalOrder.QuotientCount.Image
public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalOrder.QuotientCount.UpperBound
public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalOrder.QuotientCount.UpperBound.PresentationBound
public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalOrder.QuotientCount.UpperBound.RelatorCertificates
public import Theory.Mathieu.M24.Properties.Order

/-!
# Cardinality of the concrete local quotient

The quotient order is a concrete certification obligation.  This module
provides the checked group-theoretic interface used by such a certificate:
one may either give an isomorphism with the existing permutation model of
`M24`, or give a homomorphism whose descended map is bijective.  The matrix
identities and the faithfulness/kernel checks belong to the certificate that
instantiates these hypotheses; no external order computation is imported.

The certified conjugation image supplies the lower bound
`localQuotient_card_ge`. The upper bound follows from the finite bound for
the explicit presentation and the checked membership of all its evaluated
relators in the actual normal closure. `localQuotient_card` combines these
certificates to prove that the quotient has order 244823040.

The generator words come from the ATLAS `J4G1-max1W1` program; see
`Cardinality.Subgroup` and `UpperBound/source/README.md` for provenance.
-/

@[expose] public section
namespace Janko4.Cardinality

/-- The certified conjugation image gives a lower bound for the actual quotient. -/
theorem localQuotient_card_ge
    (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1) :
    244823040 ≤ Nat.card (LocalQuotient hA hB) := by
  rw [← QuotientCount.actionImage_card hA hB]
  exact QuotientCount.image_card_le_quotient_card hA hB
    (QuotientCount.localKernel_le_action_ker_certified hA hB)

/-- Only the matching upper bound remains after the concrete image certificate. -/
theorem localQuotient_card_of_upper_bound
    (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1)
    (hupper : Nat.card (LocalQuotient hA hB) ≤ 244823040) :
    Nat.card (LocalQuotient hA hB) = 244823040 :=
  Nat.le_antisymm hupper (localQuotient_card_ge hA hB)

/-- Final assembly from independently certified presentation size and relators.
Both premises concern the explicit presentation from `UpperBound.Data`; the
relator membership premise refers to the actual matrix subgroup. -/
theorem localQuotient_card_of_presentation_certificates
    (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1)
    (hrel : ∀ i, QuotientCount.UpperBound.localRelator hA hB i ∈ localKernel hA hB)
    (hbound : Finite QuotientCount.UpperBound.Presentation ∧
      Nat.card QuotientCount.UpperBound.Presentation ≤ 244823040) :
    Nat.card (LocalQuotient hA hB) = 244823040 :=
  localQuotient_card_of_upper_bound hA hB
    (QuotientCount.UpperBound.card_le_of_relators hA hB hrel hbound)

/-- The actual local quotient has order 244823040, by the certified conjugation
image and the independent presentation upper bound. -/
theorem localQuotient_card
    (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1) :
    Nat.card (LocalQuotient hA hB) = 244823040 :=
  localQuotient_card_of_presentation_certificates hA hB
    (QuotientCount.UpperBound.localRelator_mem hA hB)
    QuotientCount.UpperBound.PresentationBound.presentation_bound

/-- A certified isomorphism with the repository's concrete `M24` has the
expected quotient cardinality. -/
theorem localQuotient_card_of_equiv
    (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1)
    (e : LocalQuotient hA hB ≃* Sporadic.Mathieu.M24) :
    Nat.card (LocalQuotient hA hB) = 244823040 := by
  exact (Nat.card_congr e.toEquiv).trans Sporadic.Mathieu.m24_order

/-- A bijective homomorphism from the concrete quotient also certifies its
cardinality.  This is useful when a faithful permutation action is checked
directly rather than packaged as a `MulEquiv`. -/
theorem localQuotient_card_of_bijective
    (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1)
    {G : Type*} [Group G]
    (f : LocalQuotient hA hB →* G)
    (hf : Function.Bijective f) (hG : Nat.card G = 244823040) :
    Nat.card (LocalQuotient hA hB) = 244823040 := by
  rw [Nat.card_congr (Equiv.ofBijective f hf), hG]

/-- Descend a homomorphism on the local subgroup after the normal-closure
kernel check.  A quotient certificate can use this definition together with
`localQuotient_card_of_bijective`. -/
def localQuotientLift
    (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1)
    {G : Type*} [Monoid G]
    (f : max1Subgroup hA hB →* G)
    (hf : localKernel hA hB ≤ f.ker) : LocalQuotient hA hB →* G :=
  QuotientGroup.lift (localKernel hA hB) f hf

@[simp] theorem localQuotientLift_mk'
    (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1)
    {G : Type*} [Monoid G]
    (f : max1Subgroup hA hB →* G)
    (hf : localKernel hA hB ≤ f.ker) (g : max1Subgroup hA hB) :
    localQuotientLift hA hB f hf (QuotientGroup.mk' (localKernel hA hB) g) = f g := by
  exact QuotientGroup.lift_mk' (N := localKernel hA hB) hf g

end Janko4.Cardinality
