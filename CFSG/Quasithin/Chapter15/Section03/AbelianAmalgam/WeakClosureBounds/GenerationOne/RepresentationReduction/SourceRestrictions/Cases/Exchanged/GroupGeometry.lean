module
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.WeakClosureBounds.GenerationOne.RepresentationReduction.SourceRestrictions.Cases.Exchanged.Assembly

/-!
# Source group geometry for the exchanged deduction

An index-two component normalizer gives the return condition for every
element of T, without requiring that the exchanger be an involution.
The commuting disjoint component pair then constructs the marked product
used by the module deduction. Conversely the explicit pair geometry
identifies K₀ with the actual T-conjugate span of K and makes K<K₀.

The hypotheses below are group-theoretic source obligations, independent
of the F.9.18 module classification. Their original local construction
remains with the E.2.2/component-orbit assembly.

Source: Aschbacher--Smith, E.2.2 and its proof, printed pp.215--216;
the component orbit and exchanged branch on p.1152.
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.RepresentationReduction.SourceRestrictions.Cases.Exchanged
variable {D : Type*} [Group D] {K K₀ T B C : Subgroup D}

/-- A square in the component normalizer is the precise return condition. -/
theorem rightConjugate_return_of_square {t : D}
    (h : t ^ 2 ∈ normalizer (K : Set D)) : K.conjBy t = K.conjBy t⁻¹ := by
  have he : K.conjBy (t ^ 2) = K := mem_normalizer_iff_map_conj_eq.mp h
  have hh := congrArg (fun A : Subgroup D => A.conjBy t⁻¹) he
  rw [conjBy_conjBy] at hh
  simpa [pow_two, mul_assoc] using hh

/-- The return equality follows from the genuine two-element component orbit;
the chosen element need not have order two. -/
theorem rightConjugate_return_of_index_two
    (hindex : ((normalizer (K : Set D)).subgroupOf T).index = 2)
    {t : D} (ht : t ∈ T) : K.conjBy t = K.conjBy t⁻¹ :=
  rightConjugate_return_of_square
    (((normalizer (K : Set D)).subgroupOf T).sq_mem_of_index_two hindex ⟨t, ht⟩)

/-- Construct all group inputs to the module deduction, deriving the return
condition from the index. No representation hypothesis is used here. -/
theorem exchangedGeometry_of_index_two
    (hK : K ≤ K₀) (hN : K₀ ≤ normalizer (K : Set D))
    (hC : C ≤ K) (hB : T ≤ normalizer (B : Set D))
    (hmoved : ∃ t ∈ T, t ∉ normalizer (K : Set D))
    (hindex : ((normalizer (K : Set D)).subgroupOf T).index = 2)
    (hpair : ∀ t ∈ T, t ∉ normalizer (K : Set D) →
      K ⊔ K.conjBy t⁻¹ = K₀ ∧ Disjoint K (K.conjBy t⁻¹) ∧
      K ≤ centralizer (K.conjBy t⁻¹ : Set D) ∧ B = C ⊔ C.conjBy t⁻¹) :
    ExchangedGeometry K K₀ T B C := by
  refine ⟨hK, hN, hC, hB, hmoved, ?_⟩
  intro t ht hout
  obtain ⟨hs, hd, hc, hb⟩ := hpair t ht hout
  exact ⟨hs, hd, hc, rightConjugate_return_of_index_two hindex ht, hb⟩

/-- The supplied pair is exactly the source component orbit. -/
theorem ExchangedGeometry.orbit_eq (geo : ExchangedGeometry K K₀ T B C)
    (hT : T ≤ normalizer (K₀ : Set D)) : conjugateSpanBy K T = K₀ := by
  apply le_antisymm (conjugateSpanBy_le geo.component_le hT)
  obtain ⟨t, ht, hout⟩ := geo.moved
  rw [← (geo.pair t ht hout).1]
  apply sup_le (le_conjugateSpanBy K T)
  rintro _ ⟨k, hk, rfl⟩
  exact subset_closure ⟨t⁻¹, T.inv_mem ht, k, hk, rfl⟩

/-- The chosen source component is properly smaller than its orbit. -/
theorem ExchangedGeometry.component_lt (geo : ExchangedGeometry K K₀ T B C)
    (hT : T ≤ normalizer (K₀ : Set D)) : K < K₀ := by
  apply lt_of_le_of_ne geo.component_le
  intro he
  obtain ⟨t, ht, hout⟩ := geo.moved
  exact hout (he ▸ hT ht)

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.RepresentationReduction.SourceRestrictions.Cases.Exchanged
