module

public import Mathlib.GroupTheory.QuotientGroup.Defs

/-!
# Incidence and covering of group sections

A group section consists of ambient subgroups `K ≤ U`, with `K` normal in `U`.
`Covers` means the ordered-product containment `U ⊆ H K`, not generation by
`H` and `K`. The quotient-image theorem identifies this with the full image of
`H ∩ U` in the actual quotient `U / K`: a product representative lies in `U`
because both the element represented and its kernel factor do.

Two sections are incident when their numerators cover each other and their
kernels agree on the intersection of the numerators. Thus the intersection
induces the same quotient section on both sides. For nested numerators this
kernel equality reduces to `K₁ = U₁ ∩ K₂`. The predicate bodies are deliberately
exposed as the shared interface for constructing and using incident sections.

These are the group-section notions used in ABG II.8 Lemmas 5–6, article
pp64–65 / PDF65–66, unrelated to projective-plane incidence. This module is
the shared prerequisite for the covering transfer and the finite isomorphic
section recognition. Its definitions and proofs require no finiteness.
-/

public section

structure GroupSection (G : Type*) [Group G] where
  numerator : Subgroup G
  denominator : Subgroup G
  denominator_le : denominator ≤ numerator
  normal : (denominator.subgroupOf numerator).Normal

attribute [instance] GroupSection.normal

namespace GroupSection

variable {G : Type*} [Group G]

@[expose] def Covers (factor : GroupSection G) (H : Subgroup G) : Prop :=
  ∀ element ∈ factor.numerator,
    ∃ representative ∈ H, ∃ kernel ∈ factor.denominator, representative * kernel = element

@[expose] def Incident (first second : GroupSection G) : Prop :=
  first.Covers second.numerator ∧ second.Covers first.numerator ∧
    first.denominator ⊓ second.numerator = first.numerator ⊓ second.denominator

theorem covers_iff_quotient_image_eq_top (factor : GroupSection G) (H : Subgroup G) :
    factor.Covers H ↔
      (H.subgroupOf factor.numerator).map
        (QuotientGroup.mk' (factor.denominator.subgroupOf factor.numerator)) = ⊤ := by
  constructor
  · intro covering
    apply top_unique
    intro quotient _
    obtain ⟨element, rfl⟩ := QuotientGroup.mk'_surjective
      (factor.denominator.subgroupOf factor.numerator) quotient
    obtain ⟨representative, representative_mem, kernel, kernel_mem, product⟩ :=
      covering element element.property
    have representative_num : representative ∈ factor.numerator := by
      rw [← mul_inv_cancel_right representative kernel, product]
      exact factor.numerator.mul_mem element.property
        (factor.numerator.inv_mem (factor.denominator_le kernel_mem))
    refine Subgroup.mem_map.mpr ⟨⟨representative, representative_num⟩, representative_mem, ?_⟩
    apply QuotientGroup.eq.mpr
    change representative⁻¹ * (element : G) ∈ factor.denominator
    rw [← product, inv_mul_cancel_left]
    exact kernel_mem
  · intro image element element_mem
    have quotient_mem : QuotientGroup.mk' (factor.denominator.subgroupOf factor.numerator)
        ⟨element, element_mem⟩ ∈ (H.subgroupOf factor.numerator).map
          (QuotientGroup.mk' (factor.denominator.subgroupOf factor.numerator)) := by
      rw [image]
      trivial
    obtain ⟨representative, representative_mem, same_image⟩ := Subgroup.mem_map.mp quotient_mem
    have kernel_mem := QuotientGroup.eq.mp same_image
    refine ⟨representative, representative_mem, (representative : G)⁻¹ * element,
      kernel_mem, ?_⟩
    exact mul_inv_cancel_left _ _

theorem Incident.denominator_eq_inf_of_le {first second : GroupSection G}
    (incident : first.Incident second) (nested : first.numerator ≤ second.numerator) :
    first.denominator = first.numerator ⊓ second.denominator := by
  rw [← incident.2.2, inf_eq_left.mpr (first.denominator_le.trans nested)]

end GroupSection
