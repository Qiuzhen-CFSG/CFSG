module
public import Theory.Representation.SL2FourQuadraticRecognition.Consequences
public import Theory.Representation.SL2FourNaturalOrbits.SylowDisplacement

/-!
# A natural Sylow's moved span covers its fixed space

A quadratic Sylow two-action whose global-fixed quotient is the natural
SL₂(4) module has its moved span covering its full fixed space modulo the
global fixed space. On the natural module, displacements of any vector
outside the fixed plane exhaust that plane. Surjectivity lifts such
displacements, and the difference of the two lifts lies in the actual
global fixed space. No splitting or dimension bound is assumed.

Source: Niles, *Pushing-up in finite groups* (1979), Proposition 4.6(g) and
Theorem 4.7(d), using the natural-module displacement assertions of 4.1.
-/

public section
open Subgroup Representation Representation.BinaryOffender
open SL2FourNatural SL2FourNatural.ProjectiveRecognition
namespace Representation.SL2FourQuadraticRecognition
variable {H M : Type*} [Group H] [AddCommGroup M] [Module (ZMod 2) M]

/-- A quadratic Sylow action with natural global-fixed quotient has its
moved span covering the full Sylow fixed space modulo the global fixed space.
No splitting of the fixed attachment is required. -/
theorem sylow_moved_covers_fixed_of_natural_quotient [Finite H]
    (ρ : Representation (ZMod 2) H M) (q : H →* SL) (hq : Function.Surjective q)
    (e : (M ⧸ fixedSpace ρ ⊤) ≃ₗ[ZMod 2] SL2FourNatural.V)
    (he : ∀ h v, e (fixedQuotient ρ ⊤ h v) = specialLinearNatural 2 (q h) (e v))
    (S : Sylow 2 H) (hquad : IsQuadratic ρ (S : Subgroup H)) :
    subspaceCommutator ρ ⊤ (S : Subgroup H) ⊔ fixedSpace ρ ⊤ =
      fixedSpace ρ (S : Subgroup H) := by
  let f : M →ₗ[ZMod 2] SL2FourNatural.V := e.toLinearMap.comp (fixedSpace ρ ⊤).mkQ
  have hf : Function.Surjective f := e.surjective.comp (fixedSpace ρ ⊤).mkQ_surjective
  have hfe (h : H) (v : M) : f (ρ h v) = action (q h) (f v) :=
    he h ((fixedSpace ρ ⊤).mkQ v)
  have hk (v : M) : f v = 0 ↔ v ∈ fixedSpace ρ ⊤ := by
    change e ((fixedSpace ρ ⊤).mkQ v) = 0 ↔ _
    rw [LinearEquiv.map_eq_zero_iff]
    exact Submodule.Quotient.mk_eq_zero _
  obtain ⟨W, hWcard, hWfixed, hWdisp⟩ := sylow_fixed_plane_displacements (S.mapSurjective hq)
  have hWne : W ≠ ⊤ := by
    intro hW
    have hc : Nat.card W = Nat.card SL2FourNatural.V := by
      rw [hW]
      exact Nat.card_congr Submodule.topEquiv.toEquiv
    rw [hWcard, Nat.card_eq_fintype_card, SL2FourNatural.card_vector] at hc
    norm_num at hc
  have hex : ∃ v : SL2FourNatural.V, v ∉ W := by
    by_contra hn
    push Not at hn
    exact hWne (top_unique (fun v _ => hn v))
  obtain ⟨v₀, hv₀⟩ := hex
  obtain ⟨u₀, hu₀⟩ := hf v₀
  apply le_antisymm
  · refine sup_le ?_ (fixedSpace_antitone ρ le_top)
    apply Submodule.span_le.mpr
    rintro _ ⟨s, hs, v, _, rfl⟩ t
    exact hquad t t.property s hs v
  · intro w hw
    have hfw : f w ∈ W := by
      apply (hWfixed _).mpr
      intro s hs
      obtain ⟨h, hh, rfl⟩ := hs
      rw [← hfe]
      exact congrArg f (hw ⟨h, hh⟩)
    obtain ⟨s, hs, hsw⟩ := hWdisp v₀ hv₀ (f w) hfw
    obtain ⟨h, hh, rfl⟩ := hs
    have hdiff : f (ρ h u₀ - u₀) = f w := by
      rw [map_sub, hfe, hu₀]
      exact hsw
    have hres : w - (ρ h u₀ - u₀) ∈ fixedSpace ρ ⊤ := by
      apply (hk _).mp
      rw [map_sub, hdiff, sub_self]
    have hm : ρ h u₀ - u₀ ∈ subspaceCommutator ρ ⊤ (S : Subgroup H) :=
      Submodule.subset_span ⟨h, hh, u₀, Submodule.mem_top, rfl⟩
    exact Submodule.mem_sup.mpr ⟨ρ h u₀ - u₀, hm, w - (ρ h u₀ - u₀), hres, by abel⟩

end Representation.SL2FourQuadraticRecognition
