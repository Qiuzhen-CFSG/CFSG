module
public import Theory.Representation.BinaryOffender.MovedSpaceTransport

/-!
# Moved subspaces of a split central extension

An equivariant section of a quotient identifies the literal moved subspace
when the quotient kernel is fixed by the actor. Subtract the section of
each vector image; this difference is fixed, so every original displacement
is the section of its quotient displacement.
Source application: Aschbacher–Smith E.2.3(3), the actual A5 moved modules.
-/

public section
open Subgroup Representation
namespace Representation.BinaryOffender
variable {G V W : Type*} [Group G]
  [AddCommGroup V] [Module (ZMod 2) V] [AddCommGroup W] [Module (ZMod 2) W]

/-- An equivariant section identifies moved spaces when the complementary
kernel is fixed by the stated actor. -/
theorem moved_eq_map_of_fixed_kernel_section
    (ρ : Representation (ZMod 2) G V) (σ : Representation (ZMod 2) G W)
    (p : V →ₗ[ZMod 2] W) (s : W →ₗ[ZMod 2] V)
    (hs : ∀ w, p (s w) = w) (he : ∀ g w, s (σ g w) = ρ g (s w))
    (K : Subgroup G) (hk : ∀ v, p v = 0 → ∀ g ∈ K, ρ g v = v) :
    subspaceCommutator ρ ⊤ K = (subspaceCommutator σ ⊤ K).map s := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨g,hg,v,_,rfl⟩
    have hkv : p (v-s (p v)) = 0 := by rw [map_sub,hs,sub_self]
    have hh := hk (v-s (p v)) hkv g hg
    rw [map_sub,←he] at hh
    refine ⟨σ g (p v)-p v,Submodule.subset_span ⟨g,hg,p v,Submodule.mem_top,rfl⟩,?_⟩
    rw [map_sub]
    exact (sub_eq_sub_iff_sub_eq_sub.mpr hh).symm
  · rw [Submodule.map_le_iff_le_comap]
    apply Submodule.span_le.mpr
    rintro _ ⟨g,hg,v,_,rfl⟩
    change s (σ g v-v) ∈ subspaceCommutator ρ ⊤ K
    rw [map_sub,he]
    exact Submodule.subset_span ⟨g,hg,s v,Submodule.mem_top,rfl⟩

end Representation.BinaryOffender
