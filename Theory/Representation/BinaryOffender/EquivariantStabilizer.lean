module

public import Theory.Representation.BinaryOffender.SubspaceAction

/-!
# Stabilizers under equivariant coordinates

A group equivalence and a compatible binary linear equivalence carry the
setwise stabilizer of a specified subspace to the stabilizer of its image.
Intersecting with any acting subgroup preserves this equivalence, so a
quotient of the model stabilizer transports to the original stabilizer.

The vector compatibility equation is essential: an abstract group
isomorphism alone does not identify the stabilizers. This is the transport
step used for the definite plane in Aschbacher–Smith, *The Classification
of Quasithin Groups*, printed p.1155 (combined manuscript, 1 March 2004).
-/

@[expose] public section

namespace Representation.BinaryOffender

variable {G K V W : Type*} [Group G] [Group K]
  [AddCommGroup V] [AddCommGroup W] [Module (ZMod 2) V] [Module (ZMod 2) W]
  (ρ : Representation (ZMod 2) G V) (τ : Representation (ZMod 2) K W)
  (f : G ≃* K) (e : V ≃ₗ[ZMod 2] W)
  (he : ∀ g v, e (ρ g v) = τ (f g) (e v))

include he

theorem mem_subspaceStabilizer_equivariant (P : Submodule (ZMod 2) V) (g : G) :
    g ∈ subspaceStabilizer ρ P ↔
      f g ∈ subspaceStabilizer τ (P.map e.toLinearMap) := by
  have hm (v : V) : e v ∈ P.map e.toLinearMap ↔ v ∈ P := by
    constructor
    · rintro ⟨u, hu, huv⟩
      exact e.injective huv ▸ hu
    · intro hv
      exact ⟨v, hv, rfl⟩
  constructor
  · intro hg w
    obtain ⟨v, rfl⟩ := e.surjective w
    rw [← he, hm, hm]
    exact hg v
  · intro hg v
    have h := hg (e v)
    rwa [← he, hm, hm] at h

theorem map_subspaceStabilizer_equivariant (P : Submodule (ZMod 2) V) :
    (subspaceStabilizer ρ P).map f.toMonoidHom =
      subspaceStabilizer τ (P.map e.toLinearMap) := by
  ext k
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact (mem_subspaceStabilizer_equivariant ρ τ f e he P g).mp hg
  · intro hk
    refine ⟨f.symm k, ?_, f.apply_symm_apply k⟩
    apply (mem_subspaceStabilizer_equivariant ρ τ f e he P (f.symm k)).mpr
    simpa only [f.apply_symm_apply] using hk

def equivariantStabilizerEquiv (A : Subgroup G) (P : Submodule (ZMod 2) V) :
    (A ⊓ subspaceStabilizer ρ P : Subgroup G) ≃*
      (A.map f.toMonoidHom ⊓ subspaceStabilizer τ (P.map e.toLinearMap) : Subgroup K) :=
  (f.subgroupMap _).trans (MulEquiv.subgroupCongr (by
    exact (Subgroup.map_inf _ _ f.toMonoidHom f.injective).trans
      (congrArg (fun S => A.map f.toMonoidHom ⊓ S)
        (map_subspaceStabilizer_equivariant ρ τ f e he P))))

theorem exists_surjective_equivariantStabilizer_hom
    {L : Type*} [Group L] (A : Subgroup G) (P : Submodule (ZMod 2) V)
    (q : (A.map f.toMonoidHom ⊓
      subspaceStabilizer τ (P.map e.toLinearMap) : Subgroup K) →* L)
    (hq : Function.Surjective q) :
    ∃ q' : (A ⊓ subspaceStabilizer ρ P : Subgroup G) →* L,
      Function.Surjective q' :=
  ⟨q.comp (equivariantStabilizerEquiv ρ τ f e he A P).toMonoidHom,
    hq.comp (equivariantStabilizerEquiv ρ τ f e he A P).surjective⟩

end Representation.BinaryOffender
