module
public import Theory.Representation.SL2FourQuadraticRecognition.NaturalCovering

/-!
# Pointwise covering in a natural fixed quotient

A Sylow fixed codimension at most two matches the two-dimensional natural
fixed plane. Rank-nullity therefore identifies the original Sylow fixed
space with its full preimage, including every central fixed attachment.
For any original vector outside that fixed space, natural Sylow
displacements cover the fixed plane; lifting through the same quotient
covers every original fixed vector modulo the global fixed space.

Source: Niles, *Pushing-up in finite groups* (1979), Theorem 4.7(d),
printed page 48, the per-vector Sylow covering assertion.
-/

public section
open Subgroup Representation Representation.BinaryOffender
open SL2FourNatural SL2FourNatural.ProjectiveRecognition
namespace Representation.SL2FourQuadraticRecognition
variable {H M : Type*} [Group H] [Finite H]
  [AddCommGroup M] [Module (ZMod 2) M] [FiniteDimensional (ZMod 2) M]

/-- Equality in the Sylow fixed-index bound removes all fixed attachment
obstructions for a natural fixed vector. -/
theorem sylow_fixed_iff_natural_of_fixedCodim
    (ρ : Representation (ZMod 2) H M) (q : H →* SL) (hq : Function.Surjective q)
    (e : (M ⧸ fixedSpace ρ ⊤) ≃ₗ[ZMod 2] SL2FourNatural.V)
    (he : ∀ h v, e (fixedQuotient ρ ⊤ h v) = specialLinearNatural 2 (q h) (e v))
    (S : Sylow 2 H) (hd : fixedCodim ρ (S : Subgroup H) ≤ 2) :
    ∀ u : M, u ∈ fixedSpace ρ (S : Subgroup H) ↔
      ∀ g ∈ (S : Subgroup H).map q,
        action g (e ((fixedSpace ρ ⊤).mkQ u)) = e ((fixedSpace ρ ⊤).mkQ u) := by
  let f : M →ₗ[ZMod 2] SL2FourNatural.V := e.toLinearMap.comp (fixedSpace ρ ⊤).mkQ
  have hf : Function.Surjective f := e.surjective.comp (fixedSpace ρ ⊤).mkQ_surjective
  have hfe (h : H) (v : M) : f (ρ h v) = action (q h) (f v) :=
    he h ((fixedSpace ρ ⊤).mkQ v)
  obtain ⟨W, hWcard, hWfixed, hWdisp⟩ := sylow_fixed_plane_displacements (S.mapSurjective hq)
  have hWdim : Module.finrank (ZMod 2) W = 2 := by
    have hc := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := W)
    rw [hWcard, Nat.card_zmod] at hc
    exact (Nat.pow_right_injective (by decide : 1 < (2 : ℕ)) hc).symm
  have hle : fixedSpace ρ (S : Subgroup H) ≤ W.comap f := by
    intro u hu
    apply (hWfixed _).mpr
    rintro g ⟨h, hh, rfl⟩
    rw [← hfe]
    exact congrArg f (hu ⟨h,hh⟩)
  have hdim := Submodule.finrank_quotient_add_finrank (W.comap f)
  have hcodim : Module.finrank (ZMod 2) (M ⧸ W.comap f) = 2 := by
    let g := W.mkQ.comp f
    have hg : Function.Surjective g := W.mkQ_surjective.comp hf
    have hk : g.ker = W.comap f := by
      ext x
      exact Submodule.Quotient.mk_eq_zero W
    let E : (M ⧸ W.comap f) ≃ₗ[ZMod 2] (SL2FourNatural.V ⧸ W) :=
      (Submodule.quotEquivOfEq _ _ hk.symm).trans (g.quotKerEquivOfSurjective hg)
    have hn := W.finrank_quotient_add_finrank
    rw [finrank_vector,hWdim] at hn
    rw [E.finrank_eq]
    omega
  have hfixed := fixedCodim_add_finrank ρ (S : Subgroup H)
  have heq : fixedSpace ρ (S : Subgroup H) = W.comap f := by
    apply Submodule.eq_of_le_of_finrank_eq hle
    rw [hcodim] at hdim
    have hmono := Submodule.finrank_mono hle
    omega
  intro u
  rw [heq]
  exact hWfixed _

end Representation.SL2FourQuadraticRecognition

namespace Representation.SL2FourQuadraticRecognition
variable {H M : Type*} [Group H] [Finite H]
  [AddCommGroup M] [Module (ZMod 2) M] [FiniteDimensional (ZMod 2) M]

/-- Every vector outside the Sylow fixed space produces all fixed vectors
modulo the global fixed space by its literal Sylow displacements. -/
theorem sylow_vector_displacements_cover_fixed
    (ρ : Representation (ZMod 2) H M) (q : H →* SL) (hq : Function.Surjective q)
    (e : (M ⧸ fixedSpace ρ ⊤) ≃ₗ[ZMod 2] SL2FourNatural.V)
    (he : ∀ h v, e (fixedQuotient ρ ⊤ h v) = specialLinearNatural 2 (q h) (e v))
    (S : Sylow 2 H) (hd : fixedCodim ρ (S : Subgroup H) ≤ 2)
    (v : M) (hv : v ∉ fixedSpace ρ (S : Subgroup H)) :
    ∀ w ∈ fixedSpace ρ (S : Subgroup H),
      ∃ s ∈ (S : Subgroup H), w - (ρ s v - v) ∈ fixedSpace ρ ⊤ := by
  let f : M →ₗ[ZMod 2] SL2FourNatural.V := e.toLinearMap.comp (fixedSpace ρ ⊤).mkQ
  have hfe (h : H) (u : M) : f (ρ h u) = action (q h) (f u) :=
    he h ((fixedSpace ρ ⊤).mkQ u)
  have hk (u : M) : f u = 0 ↔ u ∈ fixedSpace ρ ⊤ := by
    change e ((fixedSpace ρ ⊤).mkQ u) = 0 ↔ _
    rw [LinearEquiv.map_eq_zero_iff]
    exact Submodule.Quotient.mk_eq_zero _
  obtain ⟨W, _, hWfixed, hWdisp⟩ := sylow_fixed_plane_displacements (S.mapSurjective hq)
  have hvW : f v ∉ W := by
    intro hv'
    apply hv
    apply (sylow_fixed_iff_natural_of_fixedCodim ρ q hq e he S hd v).mpr
    exact (hWfixed _).mp hv'
  intro w hw
  have hwW : f w ∈ W := by
    apply (hWfixed _).mpr
    exact (sylow_fixed_iff_natural_of_fixedCodim ρ q hq e he S hd w).mp hw
  obtain ⟨g, ⟨s, hs, rfl⟩, hgw⟩ := hWdisp (f v) hvW (f w) hwW
  refine ⟨s, hs, (hk _).mp ?_⟩
  rw [map_sub, map_sub, hfe, hgw, sub_self]

end Representation.SL2FourQuadraticRecognition
