module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Reduction.LocalGeometry

/-!
# The quotient and parabolic boundaries after replacing H

Shrinking H shrinks its conjugate span of V₃. The induced map between the
literal quotients by V₁ is injective; on representatives it is inclusion.
Its conjugation equation retains the actual subgroup action. There is no
claim that the smaller and larger modules coincide, nor a map between
H/O₂(H) and J/O₂(J) without a separate comparison of the two-cores.

Ordinary maximality of the overlap descends through the two-core quotient
when the overlap contains the kernel. A separate identification of its
image with (L₁T)* then supplies the maximality used for point marking.
This transport does not establish the parabolic identification itself.

Source: Aschbacher--Smith, 13.8.21(2), printed p.956 (PDF p.973),
combined manuscript of 1 March 2004.
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Reduction.LocalGeometry
variable {G : Type*} [Group G]

/-- The new source module numerator is its own conjugate span. -/
theorem UH_mono (H J V₃ : Subgroup G) (hJH : J ≤ H) :
    Source.UH J V₃ ≤ Source.UH H V₃ := conjugateSpanBy_mono le_rfl hJH

/-- Relative normality of the line restricts to the smaller conjugate span. -/
theorem line_normal_in_smaller_span (H J V₃ V₁ : Subgroup G) (hJH : J ≤ H)
    [(V₁.subgroupOf (Source.UH H V₃)).Normal] :
    (V₁.subgroupOf (Source.UH J V₃)).Normal := by
  let f := inclusion (UH_mono H J V₃ hJH)
  change ((V₁.subgroupOf (Source.UH H V₃)).comap f).Normal
  infer_instance

section Quotient
variable (H J V₃ V₁ : Subgroup G) (hJH : J ≤ H)
  [(V₁.subgroupOf (Source.UH H V₃)).Normal]
  [(V₁.subgroupOf (Source.UH J V₃)).Normal]

/-- The map induced by the literal inclusion of the two conjugate spans. -/
def utildeInclusion : Source.Utilde J V₃ V₁ →* Source.Utilde H V₃ V₁ :=
  QuotientGroup.map _ _ (inclusion (UH_mono H J V₃ hJH)) (fun _ hx => hx)

theorem utildeInclusion_mk (u : Source.UH J V₃) :
    utildeInclusion H J V₃ V₁ hJH (QuotientGroup.mk' _ u) =
      QuotientGroup.mk' (V₁.subgroupOf (Source.UH H V₃))
        (inclusion (UH_mono H J V₃ hJH) u) := rfl

/-- The kernel comparison uses the same actual denominator V₁ on both sides. -/
theorem utildeInclusion_injective : Function.Injective (utildeInclusion H J V₃ V₁ hJH) := by
  intro a b he
  obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective (V₁.subgroupOf (Source.UH J V₃)) a
  obtain ⟨b, rfl⟩ := QuotientGroup.mk'_surjective (V₁.subgroupOf (Source.UH J V₃)) b
  rw [utildeInclusion_mk, utildeInclusion_mk] at he
  have hi := (QuotientGroup.eq (s := V₁.subgroupOf (Source.UH H V₃))
    (a := inclusion (UH_mono H J V₃ hJH) a)
    (b := inclusion (UH_mono H J V₃ hJH) b)).mp he
  exact QuotientGroup.eq.mpr hi

/-- Compatibility with the source conjugation action, on actual representatives. -/
theorem utildeInclusion_conjugate (j : J) (u : Source.UH J V₃) :
    utildeInclusion H J V₃ V₁ hJH
      (QuotientGroup.mk' (V₁.subgroupOf (Source.UH J V₃))
        ⟨j.val * u.val * j.val⁻¹,
          le_normalizer_iff.mp (le_normalizer_conjugateSpanBy V₃ J)
            j.val j.property u.val u.property⟩) =
      QuotientGroup.mk' (V₁.subgroupOf (Source.UH H V₃))
        ⟨j.val * u.val * j.val⁻¹,
          le_normalizer_iff.mp (le_normalizer_conjugateSpanBy V₃ H)
            j.val (hJH j.property) u.val (UH_mono H J V₃ hJH u.property)⟩ := rfl

end Quotient

private theorem isCoatom_map_of_surjective {A B : Type*} [Group A] [Group B]
    (f : A →* B) (hf : Function.Surjective f) (P : Subgroup A)
    (hP : IsCoatom P) (hker : f.ker ≤ P) : IsCoatom (P.map f) := by
  refine ⟨?_, ?_⟩
  · intro he
    have hc := congrArg (comap f) he
    rw [comap_map_eq_self hker, comap_top] at hc
    exact hP.1 hc
  · intro Q hQ
    have hlt : P < Q.comap f := by
      rw [← comap_map_eq_self hker]
      exact (comap_lt_comap_of_surjective hf).mpr hQ
    have hc := hP.2 _ hlt
    have hm := congrArg (map f) hc
    simpa only [map_comap_eq_self_of_surjective hf, map_top_of_surjective f hf] using hm

/-- A maximal overlap containing the actual two-core stays maximal in H*. -/
theorem star_overlap_isCoatom (H M : Subgroup G)
    (hmax : IsCoatom ((H ⊓ M).subgroupOf H)) (hQ : Source.QH H ≤ M) :
    IsCoatom (Source.starImage H (H ⊓ M)) := by
  apply isCoatom_map_of_surjective _ (QuotientGroup.mk'_surjective _) _ hmax
  rw [QuotientGroup.ker_mk']
  intro h hh
  exact ⟨h.property, hQ (mem_map.mpr ⟨h, hh, rfl⟩)⟩

/-- The marked parabolic inherits maximality after identifying its actual image.
The kernel containment cannot be dropped from this implication. -/
theorem star_base_isCoatom (H M L₁ T : Subgroup G)
    (hmax : IsCoatom ((H ⊓ M).subgroupOf H)) (hQ : Source.QH H ≤ M)
    (hmark : Source.starImage H (H ⊓ M) = Source.starImage H (L₁ ⊔ T)) :
    IsCoatom (Source.starImage H (L₁ ⊔ T)) :=
  hmark ▸ star_overlap_isCoatom H M hmax hQ

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Reduction.LocalGeometry
