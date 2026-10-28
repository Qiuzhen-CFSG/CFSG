module
public import Theory.Representation.BinaryOffender.NoncentralMoved

/-!
# Two noncentral layers in a perfect actor module

A surjective intertwiner maps the full commutator space onto the quotient
commutator space. Thus a faithful fully moved quotient makes the original
moved space faithful. If both its kernel and quotient are noncentral, the
original moved space cannot be Irr⁺: the kernel would generate the entire
moved space and kill the quotient movement.

Source application: Aschbacher–Smith13.7.16(2), printed p.944.
-/

public section
open Subgroup Representation

namespace Representation.BinaryOffender
variable {G V W : Type*} [Group G]
  [AddCommGroup V] [Module (ZMod 2) V]
  [AddCommGroup W] [Module (ZMod 2) W]

theorem map_moved_of_surjective_intertwining
    (ρ : Representation (ZMod 2) G V) (σ : Representation (ZMod 2) G W)
    (K : Subgroup G) (f : V →ₗ[ZMod 2] W) (hf : Function.Surjective f)
    (he : ∀ k : K, ∀ v, f (ρ k v) = σ k (f v)) :
    (subspaceCommutator ρ ⊤ K).map f = subspaceCommutator σ ⊤ K := by
  apply le_antisymm
  · apply Submodule.map_le_iff_le_comap.mpr
    apply Submodule.span_le.mpr
    rintro _ ⟨k,hk,v,_,rfl⟩
    change f (ρ k v-v) ∈ subspaceCommutator σ ⊤ K
    rw [map_sub,he ⟨k,hk⟩]
    exact Submodule.subset_span ⟨k,hk,f v,Submodule.mem_top,rfl⟩
  · apply Submodule.span_le.mpr
    rintro _ ⟨k,hk,w,_,rfl⟩
    obtain ⟨v,rfl⟩ := hf w
    refine ⟨ρ k v-v,Submodule.subset_span ⟨k,hk,v,Submodule.mem_top,rfl⟩,?_⟩
    rw [map_sub,he ⟨k,hk⟩]

theorem eq_one_of_fixes_moved_of_faithful_quotient
    (ρ : Representation (ZMod 2) G V) (σ : Representation (ZMod 2) G W)
    (K : Subgroup G) (f : V →ₗ[ZMod 2] W) (hf : Function.Surjective f)
    (he : ∀ k v, f (ρ k v) = σ k (f v))
    (hσ : Function.Injective σ) (hwhole : subspaceCommutator σ ⊤ K = ⊤)
    (g : G) (hg : ∀ v ∈ subspaceCommutator ρ ⊤ K, ρ g v = v) : g = 1 := by
  have htop : (subspaceCommutator ρ ⊤ K).map f = ⊤ :=
    (map_moved_of_surjective_intertwining ρ σ K f hf (fun k v => he k v)).trans hwhole
  apply hσ
  ext w
  obtain ⟨v,hv,rfl⟩ := (show w ∈ (subspaceCommutator ρ ⊤ K).map f from
    htop.symm ▸ Submodule.mem_top)
  rw [map_one,Module.End.one_apply,←he,hg v hv]

theorem not_isIrrPlus_moved_of_two_noncentral_layers
    (ρ : Representation (ZMod 2) G V) (σ : Representation (ZMod 2) G W)
    (K : Subgroup G) [Group.IsPerfect K]
    (f : V →ₗ[ZMod 2] W) (hf : Function.Surjective f)
    (he : ∀ k : K, ∀ v, f (ρ k v) = σ k (f v))
    (hk : ¬ f.ker ≤ fixedSpace ρ K)
    (hm : subspaceCommutator σ ⊤ K ≠ ⊥) :
    ¬ IsIrrPlus ρ K (subspaceCommutator ρ ⊤ K) := by
  intro hi
  have hker : K ≤ subspaceStabilizer ρ f.ker := by
    apply le_subspaceStabilizer
    intro k hk v hv
    change f (ρ k v) = 0
    rw [he ⟨k,hk⟩, show f v = 0 from hv, map_zero]
  have hI : subspaceCommutator ρ ⊤ K ≤ f.ker := by
    rw [← moved_eq_of_noncentral_invariant ρ K hi f.ker hker hk]
    exact subspaceCommutator_le_of_invariant ρ hker
  apply hm
  apply le_bot_iff.mp
  apply Submodule.span_le.mpr
  rintro _ ⟨k,hk,w,_,rfl⟩
  obtain ⟨v,rfl⟩ := hf w
  have hz := hI (Submodule.subset_span ⟨k,hk,v,Submodule.mem_top,rfl⟩)
  change σ k (f v) - f v = 0
  change f (ρ k v-v) = 0 at hz
  rwa [map_sub,he ⟨k,hk⟩] at hz
end Representation.BinaryOffender

