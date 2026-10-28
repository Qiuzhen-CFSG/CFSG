module

public import Theory.GroupTheory.GroupSection

/-!
# Covering transfers along nested incident sections

ABG II.8 Lemma 5, article p64 / PDF65, states that if `U₁ / K₁` and `U₂ / K₂`
are incident, `H` covers the first section, and `U₁ ≤ U₂`, then `H` covers the
second. The argument works for arbitrary groups, so in particular for the
finite groups in the source development.

Incidence gives `U₂ ⊆ U₁ K₂` and, under nesting, `K₁ = U₁ ∩ K₂`. Factor an
element of `U₂` first through `U₁`, then through `H`. Both remaining factors
belong to `K₂`; multiplying them proves the ordered-product containment
`U₂ ⊆ H K₂`. The shared covering API equates this with full quotient image
of `H ∩ U₂`, rather than merely generation by a subgroup join.
-/

public section

namespace GroupSection

variable {G : Type*} [Group G]

theorem covers_of_incident_of_le {first second : GroupSection G} {H : Subgroup G}
    (incident : first.Incident second) (covering : first.Covers H)
    (nested : first.numerator ≤ second.numerator) : second.Covers H := by
  have kernel_le : first.denominator ≤ second.denominator := by
    rw [incident.denominator_eq_inf_of_le nested]
    exact inf_le_right
  intro element element_mem
  obtain ⟨middle, middle_mem, outer, outer_mem, outer_product⟩ :=
    incident.2.1 element element_mem
  obtain ⟨representative, representative_mem, inner, inner_mem, inner_product⟩ :=
    covering middle middle_mem
  refine ⟨representative, representative_mem, inner * outer,
    second.denominator.mul_mem (kernel_le inner_mem) outer_mem, ?_⟩
  rw [← mul_assoc, inner_product, outer_product]

end GroupSection
