module
public import Theory.SpecificGroups.Janko3.SourceRecognition.CubicNormalizerThirdModel
public import Theory.SpecificGroups.Janko3.SourceRecognition.CubicNormalizerFiveAlignment

/-!
# The fixed third overlap can be aligned without changing the pair

Every actual A₅ in the projective complement containing the canonical
order-ten pair subgroup can be moved to `thirdFive` by an automorphism
fixing the entire full pair pointwise. The full preimage, including its
cubic kernel, is carried to `thirdOverlap`.
-/

public noncomputable section
namespace Sporadic.Janko3.SourceRecognition.CubicNormalizerModel
open Subgroup

/-- A canonical full-pair correction retains the whole complement and
cubic kernel while aligning the full third-overlap preimage. -/
theorem exists_canonical_third_alignment (H : Subgroup P)
    (hH : Nonempty (H ≃* alternatingGroup (Fin 5))) (hB : pairTen ≤ H) :
    ∃ τ : MulAut Model,
      (∀ x ∈ pair, τ x = x) ∧
      (∀ x ∈ projection.ker, τ x = x) ∧
      (SemidirectProduct.inr : P →* Model).range.map τ.toMonoidHom =
        (SemidirectProduct.inr : P →* Model).range ∧
      (H.comap projection).map τ.toMonoidHom = thirdOverlap := by
  obtain ⟨t,ht2,htd,htQ⟩ := exists_projective_pair_inverter
  have hQt : projectivePair ≤ centralizer ({t} : Set P) := by
    intro x hx
    exact mem_centralizer_singleton_iff.mpr (htQ x hx)
  have hQeq : projectivePair = centralizer ({t} : Set P) :=
    eq_of_le_of_card_ge hQt (by
      rw [projectivePair_card,
        AlternatingSix.PGLNineOuterCentralizer.outer_involution_centralizer_card t ht2 htd])
  have htmem : t ∈ projectivePair := by rw [hQeq]; exact mem_centralizer_singleton_iff.mpr rfl
  have htB : t ∈ centralizer (pairTen : Set P) := centralizer_le (by
    intro x hx
    exact hx.1) htQ
  have hgen : pairTen ⊔ zpowers t = projectivePair := by
    apply eq_of_le_of_card_ge (sup_le inf_le_left (zpowers_le.mpr htmem))
    change Nat.card projectivePair ≤ Nat.card (pairTen ⊔ zpowers t : Subgroup P)
    rw [projectivePair_card,card_sup_zpowers_of_normalizing_involution pairTen t
      (by simpa only [ht2] using pow_orderOf_eq_one t) (fun h => htd h.2)
      (centralizer_le_normalizer (pairTen : Set P) htB),pairTen_card]
  obtain ⟨τ,σ,_hσ,hfix,hl,hr,hmap,_hm⟩ := exists_pair_fixing_five_alignment
    pairTen H thirdFive t pairTen_card hH thirdFive_equiv hB pairTen_le_thirdFive htd htB
  have hfixpair : ∀ x ∈ pair, τ x = x := by
    rw [hgen] at hfix
    exact hfix
  have hproj (x : Model) : projection (τ x) = σ (projection x) := by
    nth_rw 1 [←SemidirectProduct.inl_left_mul_inr_right x]
    rw [map_mul,hl,hr,map_mul]
    change 1 * σ x.right = σ x.right
    exact one_mul _
  refine ⟨τ,hfixpair,fun x hx => hfixpair x (kernel_le_pair hx),?_,?_⟩
  · apply le_antisymm
    · rintro _ ⟨_,⟨p,rfl⟩,rfl⟩
      exact ⟨σ p,(hr p).symm⟩
    · rintro _ ⟨p,rfl⟩
      refine ⟨SemidirectProduct.inr (σ.symm p),⟨_,rfl⟩,?_⟩
      change τ (SemidirectProduct.inr (σ.symm p)) = SemidirectProduct.inr p
      rw [hr,σ.apply_symm_apply]
  · apply le_antisymm
    · rintro _ ⟨x,hx,rfl⟩
      change projection (τ x) ∈ thirdFive
      rw [hproj,←hmap]
      exact mem_map_of_mem _ hx
    · intro x hx
      refine ⟨τ.symm x,?_,τ.apply_symm_apply x⟩
      change projection (τ.symm x) ∈ H
      have hh : σ (projection (τ.symm x)) ∈ H.map σ.toMonoidHom := by
        rw [hmap,←hproj,τ.apply_symm_apply]
        exact hx
      obtain ⟨p,hp,he⟩ := hh
      exact σ.injective he ▸ hp
end Sporadic.Janko3.SourceRecognition.CubicNormalizerModel
