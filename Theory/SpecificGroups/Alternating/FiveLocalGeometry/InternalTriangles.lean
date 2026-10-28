module

public import Theory.SpecificGroups.Alternating.FiveLocalGeometry.CubicEdges

/-!
# Transporters between the internal third vertices of an A₄ edge

In the marked A₅ model the two cubic subgroups inside the edge join other
than its endpoints are C 3 and C 6. The existing edge reversal exchanges
them. Transport through the marked-edge equivalence gives an actual
setwise-edge transporter, inside the A₄ join itself.

This supplements the existing local triangle construction; it supplies
the internal orbit in Aschbacher, *Sporadic Groups* (1994), 47.6(5), p.264.
-/

@[expose] public section

open Subgroup
namespace alternatingGroup.FiveLocalGeometry.InternalTriangles
open CubicEdges

private theorem internal_cases (R : Subgroup A5) (hR : Nat.card R = 3)
    (hle : R ≤ C 0 ⊔ C 1) (hne₀ : R ≠ C 0) (hne₁ : R ≠ C 1) :
    R = C 3 ∨ R = C 6 := by
  obtain ⟨i, rfl⟩ := cubic_representative R hR
  have hf : (cycle i).val 4 = 4 :=
    (mem_fourEmbedding _).mp (join_model ▸ hle (mem_zpowers _))
  have hc : ∀ i : Fin 10, (cycle i).val 4 = 4 →
      i = 0 ∨ i = 1 ∨ i = 3 ∨ i = 6 := by decide +kernel
  rcases hc i hf with rfl | rfl | rfl | rfl
  · exact (hne₀ rfl).elim
  · exact (hne₁ rfl).elim
  · exact Or.inl rfl
  · exact Or.inr rfl

private theorem reversal_internal :
    (C 3).map (MulAut.conj reversal).toMonoidHom = C 6 ∧
      (C 6).map (MulAut.conj reversal).toMonoidHom = C 3 := by
  constructor <;> apply map_C_of_cycle <;> decide +kernel

private theorem internal_transporter_model (R S : Subgroup A5)
    (hR : Nat.card R = 3) (hS : Nat.card S = 3)
    (hRle : R ≤ C 0 ⊔ C 1) (hSle : S ≤ C 0 ⊔ C 1)
    (hR₀ : R ≠ C 0) (hR₁ : R ≠ C 1) (hS₀ : S ≠ C 0) (hS₁ : S ≠ C 1) :
    ∃ g : A5, g ∈ C 0 ⊔ C 1 ∧ g ∈ pairStabilizer (C 0) (C 1) ∧
      R.map (MulAut.conj g).toMonoidHom = S := by
  have hr : reversal ∈ C 0 ⊔ C 1 := by
    rw [join_model, mem_fourEmbedding]
    decide +kernel
  have hs : reversal ∈ pairStabilizer (C 0) (C 1) := Or.inr reversal_maps
  rcases internal_cases R hR hRle hR₀ hR₁ with rfl | rfl <;>
    rcases internal_cases S hS hSle hS₀ hS₁ with rfl | rfl
  · exact ⟨1, one_mem _, one_mem _, by change (C 3).map (MonoidHom.id _) = _; exact Subgroup.map_id _⟩
  · exact ⟨reversal, hr, hs, reversal_internal.1⟩
  · exact ⟨reversal, hr, hs, reversal_internal.2⟩
  · exact ⟨1, one_mem _, one_mem _, by change (C 6).map (MonoidHom.id _) = _; exact Subgroup.map_id _⟩

variable {H : Type*} [Group H]

/-- Both internal third subgroups are in one setwise edge orbit. The transporter
belongs to the endpoint join, retaining its embedding in the given carrier. -/
theorem exists_transporter (e : H ≃* A5) (P Q R S : Subgroup H)
    (hP : Nat.card P = 3) (hQ : Nat.card Q = 3)
    (hR : Nat.card R = 3) (hS : Nat.card S = 3)
    (eJ : ↥(P ⊔ Q) ≃* alternatingGroup (Fin 4))
    (hRle : R ≤ P ⊔ Q) (hSle : S ≤ P ⊔ Q)
    (hRP : R ≠ P) (hRQ : R ≠ Q) (hSP : S ≠ P) (hSQ : S ≠ Q) :
    ∃ g : H, g ∈ P ⊔ Q ∧ g ∈ pairStabilizer P Q ∧
      R.map (MulAut.conj g).toMonoidHom = S := by
  obtain ⟨a, hp, hq⟩ := exists_marking e P Q hP hQ eJ
  have hj : (P ⊔ Q).map a.toMonoidHom = C 0 ⊔ C 1 := by
    rw [Subgroup.map_sup, hp, hq]
  have hc (T : Subgroup H) (hT : Nat.card T = 3) :
      Nat.card (T.map a.toMonoidHom) = 3 := by
    rw [card_map_of_injective a.injective, hT]
  have hl (T : Subgroup H) (hT : T ≤ P ⊔ Q) :
      T.map a.toMonoidHom ≤ C 0 ⊔ C 1 := hj ▸ map_mono hT
  have hn (T U : Subgroup H) (h : T ≠ U) :
      T.map a.toMonoidHom ≠ U.map a.toMonoidHom :=
    fun he => h (map_injective a.injective he)
  obtain ⟨g, hg, hs, ht⟩ := internal_transporter_model
    (R.map a.toMonoidHom) (S.map a.toMonoidHom) (hc R hR) (hc S hS)
    (hl R hRle) (hl S hSle) (hp ▸ hn R P hRP) (hq ▸ hn R Q hRQ)
    (hp ▸ hn S P hSP) (hq ▸ hn S Q hSQ)
  have lift (T U : Subgroup H)
      (h : (T.map a.toMonoidHom).map (MulAut.conj g).toMonoidHom = U.map a.toMonoidHom) :
      T.map (MulAut.conj (a.symm g)).toMonoidHom = U := by
    apply map_injective (f := a.toMonoidHom) a.injective
    rwa [map_conj_equiv, a.apply_symm_apply]
  refine ⟨a.symm g, ?_, ?_, lift R S ht⟩
  · have hmem : a (a.symm g) ∈ (P ⊔ Q).map a.toMonoidHom := by
      simpa only [a.apply_symm_apply, hj] using hg
    simpa only [a.symm_apply_apply] using (mem_map_equiv.mp hmem)
  · rcases hs with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · exact Or.inl ⟨lift P P (by simpa only [hp] using h₁),
        lift Q Q (by simpa only [hq] using h₂)⟩
    · exact Or.inr ⟨lift P Q (by simpa only [hp, hq] using h₁),
        lift Q P (by simpa only [hp, hq] using h₂)⟩

end alternatingGroup.FiveLocalGeometry.InternalTriangles
