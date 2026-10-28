module

public import Theory.Representation.BinaryOffender.PerfectMoved
public import Theory.Representation.BinaryOffender.IrreducibleMovedTransport

/-!
# Central-surjective transport of Irr⁺

A perfect actor cannot acquire a proper nonfixed invariant subspace through a
central kernel. This is the literal transport used in Chapter 13.7.16(3):
`U_H/V₁` projects onto `U_H/U₀`, and fixed-layer centrality puts the kernel
inside the actor fixed space. -/

public section
open Subgroup Representation
namespace Representation.BinaryOffender
variable {G V W : Type*} [Group G]
  [AddCommGroup V] [Module (ZMod 2) V]
  [AddCommGroup W] [Module (ZMod 2) W]

theorem IsIrrPlus.of_central_surjection
    (ρ : Representation (ZMod 2) G V) (σ : Representation (ZMod 2) G W)
    (K : Subgroup G) [Group.IsPerfect K]
    (f : V →ₗ[ZMod 2] W) (hf : Function.Surjective f)
    (he : ∀ k : K, ∀ v, f (ρ k v) = σ k (f v))
    (hk : f.ker ≤ fixedSpace ρ K) (hi : IsIrrPlus σ K ⊤) :
    IsIrrPlus ρ K (subspaceCommutator ρ ⊤ K) := by
  let I := subspaceCommutator ρ ⊤ K
  have hmap (J : Submodule (ZMod 2) V) :
      (subspaceCommutator ρ J K).map f = subspaceCommutator σ (J.map f) K := by
    apply le_antisymm
    · apply Submodule.map_le_iff_le_comap.mpr
      apply Submodule.span_le.mpr
      rintro _ ⟨k,hk,v,hv,rfl⟩
      change f (ρ k v - v) ∈ subspaceCommutator σ (J.map f) K
      rw [map_sub,he ⟨k,hk⟩]
      exact Submodule.subset_span ⟨k,hk,f v,⟨v,hv,rfl⟩,rfl⟩
    · apply Submodule.span_le.mpr
      rintro _ ⟨k,hk,_,⟨v,hv,rfl⟩,rfl⟩
      refine ⟨ρ k v-v,Submodule.subset_span ⟨k,hk,v,hv,rfl⟩,?_⟩
      rw [map_sub,he ⟨k,hk⟩]
  have hItop : I.map f = ⊤ := by
    rw [hmap,Submodule.map_top,LinearMap.range_eq_top.mpr hf,hi.choose_spec.1]
  have hI : K ≤ subspaceStabilizer ρ I := subspaceCommutator_invariant ρ ⊤ K
  apply isIrrPlus_of_minimal ρ hI
    (subspaceCommutator_idempotent_of_perfect ρ K)
  · intro hfixed
    apply hi.not_le_fixedSpace σ
    intro w _ k
    obtain ⟨v,hv,rfl⟩ := (show w ∈ I.map f from hItop.symm ▸ Submodule.mem_top)
    change σ k (f v) = f v
    rw [← he k]
    exact congrArg f (hfixed hv k)
  · intro J hJ hJI
    have hJmap : K ≤ subspaceStabilizer σ (J.map f) := by
      apply le_subspaceStabilizer
      rintro k hk _ ⟨v,hv,rfl⟩
      exact ⟨ρ k v,(hJ hk v).2 hv,he ⟨k,hk⟩ v⟩
    rcases hi.eq_or_le_fixedSpace σ hJmap le_top with htop | hfixed
    · left
      apply le_antisymm hJI
      have hsup : I ≤ J ⊔ fixedSpace ρ K := by
        intro v hv
        obtain ⟨j,hj,hjv⟩ := (show f v ∈ J.map f from htop.symm ▸ Submodule.mem_top)
        refine Submodule.mem_sup.mpr ⟨j,hj,v-j,?_,by abel⟩
        apply hk
        change f (v-j)=0
        rw [map_sub,hjv,sub_self]
      change subspaceCommutator ρ ⊤ K ≤ J
      rw [←subspaceCommutator_idempotent_of_perfect ρ K]
      exact subspaceCommutator_le_of_le_sup_fixedSpace ρ hJ hsup
    · right
      apply le_fixedSpace_of_commutator_le_fixedSpace ρ K J hJ
      apply le_trans (b := f.ker) ?_ hk
      apply Submodule.span_le.mpr
      rintro _ ⟨k,hk,v,hv,rfl⟩
      change f (ρ k v-v)=0
      rw [map_sub,he ⟨k,hk⟩]
      have hz : σ k (f v) = f v := hfixed ⟨v,hv,rfl⟩ ⟨k,hk⟩
      rw [hz,sub_self]

end Representation.BinaryOffender
