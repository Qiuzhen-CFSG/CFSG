module
public import Theory.Representation.SL2FourQuadraticRecognition.NaturalPointCovering
public import Theory.Representation.SL2FourNaturalExtensions.SylowElements

/-!
# A single natural Sylow actor covers the fixed space

A nontrivial element of a natural SL₂(4) Sylow subgroup has displacement
rank two. Quadraticity places its displacement image in the Sylow fixed
plane, also of dimension two, so these spaces agree. Lifting through the
original global-fixed quotient then gives pointwise covering without
assuming a splitting of the fixed attachment.

Source: Niles, *Pushing-up in finite groups* (1979), Theorem 4.7(d),
printed page 48, the per-actor center covering assertion.
-/

public section
open Subgroup Representation Representation.BinaryOffender
open SL2FourNatural SL2FourNatural.ProjectiveRecognition
namespace Representation.SL2FourQuadraticRecognition
variable {H M : Type*} [Group H] [Finite H]
  [AddCommGroup M] [Module (ZMod 2) M]

theorem sylow_actor_displacements_cover_fixed
    (ρ : Representation (ZMod 2) H M) (q : H →* SL) (hq : Function.Surjective q)
    (e : (M ⧸ fixedSpace ρ ⊤) ≃ₗ[ZMod 2] SL2FourNatural.V)
    (he : ∀ h v, e (fixedQuotient ρ ⊤ h v) = specialLinearNatural 2 (q h) (e v))
    (S : Sylow 2 H) (hquad : IsQuadratic ρ (S : Subgroup H))
    (x : H) (hx : x ∈ (S : Subgroup H)) (hxq : q x ≠ 1) :
    ∀ w ∈ fixedSpace ρ (S : Subgroup H),
      ∃ v : M, w - (ρ x v - v) ∈ fixedSpace ρ ⊤ := by
  let f : M →ₗ[ZMod 2] SL2FourNatural.V := e.toLinearMap.comp (fixedSpace ρ ⊤).mkQ
  have hf : Function.Surjective f := e.surjective.comp (fixedSpace ρ ⊤).mkQ_surjective
  have hfe (h : H) (v : M) : f (ρ h v) = action (q h) (f v) :=
    he h ((fixedSpace ρ ⊤).mkQ v)
  have hk (v : M) : f v = 0 ↔ v ∈ fixedSpace ρ ⊤ := by
    change e ((fixedSpace ρ ⊤).mkQ v) = 0 ↔ _
    rw [LinearEquiv.map_eq_zero_iff]
    exact Submodule.Quotient.mk_eq_zero _
  obtain ⟨W, hWcard, hWfixed, _⟩ := sylow_fixed_plane_displacements (S.mapSurjective hq)
  have hWdim : Module.finrank (ZMod 2) W = 2 := by
    have hc := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := W)
    rw [hWcard, Nat.card_zmod] at hc
    exact (Nat.pow_right_injective (by decide : 1 < (2 : ℕ)) hc).symm
  let d : SL2FourNatural.V →ₗ[ZMod 2] SL2FourNatural.V :=
    naturalRepresentation (q x) - LinearMap.id
  have hd : Module.finrank (ZMod 2) d.range = 2 := by
    rw [←fixedCodim_zpowers_eq_displacement_rank]
    exact (SL2FourNaturalExtensions.sylow_element_natural (S.mapSurjective hq)
      (mem_map_of_mem q hx)).2 hxq
  have hle : d.range ≤ W := by
    rintro _ ⟨u,rfl⟩
    obtain ⟨v,rfl⟩ := hf u
    have hdv : d (f v) = f (ρ x v - v) := by
      change action (q x) (f v) - f v = _
      rw [map_sub,hfe]
    rw [hdv]
    apply (hWfixed _).mpr
    rintro g ⟨s,hs,rfl⟩
    rw [←hfe]
    exact congrArg f (hquad s hs x hx v)
  have heq : d.range = W := Submodule.eq_of_le_of_finrank_eq hle (hd.trans hWdim.symm)
  intro w hw
  have hfw : f w ∈ W := by
    apply (hWfixed _).mpr
    rintro g ⟨s,hs,rfl⟩
    rw [←hfe]
    exact congrArg f (hw ⟨s,hs⟩)
  obtain ⟨u,hu⟩ := heq ▸ hfw
  obtain ⟨v,rfl⟩ := hf u
  refine ⟨v,(hk _).mp ?_⟩
  rw [map_sub,map_sub,hfe]
  change f w - d (f v) = 0
  rw [hu,sub_self]

end Representation.SL2FourQuadraticRecognition
