module
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.MovedEmbedding
public import Theory.Representation.BinaryOffender.EquivariantOffender

/-!
# Component actions under restriction and equivariant embeddings

Pulling an actual moved section back along a homomorphism preserves its
literal moved and fixed carriers. Consequently, sections in different
ambient actor groups can be compared through an isomorphism of their
components and an equivariant inclusion of their modules. This is used
when the canonical module changes the offender-generated overgroup.
Source application: Aschbacher–Smith C.2.7(3)(a), pp.146–147.
-/

public section
open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterB.QuasisimpleSource
variable {G D V : Type*} [Group G] [Group D]
  [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} {L : Subgroup G}

theorem moved_comp_map (f : D →* G) (K : Subgroup D) :
    moved (ρ.comp f) K = moved ρ (K.map f) := by
  unfold moved subspaceCommutator
  congr 1
  ext w
  constructor
  · rintro ⟨a,ha,v,hv,rfl⟩
    exact ⟨f a,mem_map_of_mem f ha,v,hv,rfl⟩
  · rintro ⟨_,⟨a,ha,rfl⟩,v,hv,rfl⟩
    exact ⟨a,ha,v,hv,rfl⟩

@[expose] noncomputable def MovedSection.comp (s : MovedSection ρ L)
    (f : D →* G) (K : Subgroup D) (hK : K.map f = L) :
    MovedSection (ρ.comp f) K := by
  let U : Subrepresentation (ρ.comp f) :=
    ⟨s.space.toSubmodule,fun g v hv => s.space.apply_mem_toSubmodule (f g) hv⟩
  let C : Subrepresentation U.toRepresentation :=
    ⟨s.central.toSubmodule,fun g v hv => s.central.apply_mem_toSubmodule (f g) hv⟩
  refine ⟨U,?_,C,?_⟩
  · change s.space.toSubmodule = moved (ρ.comp f) K
    rw [moved_comp_map,hK]
    exact s.space_eq
  · change s.central.toSubmodule = fixedSpace (s.space.toRepresentation.comp f) K
    rw [fixedSpace_comp_map,hK]
    exact s.central_eq

theorem MovedSection.comp_action (s : MovedSection ρ L)
    (f : D →* G) (K : Subgroup D) (hK : K.map f = L) :
    (s.comp f K hK).action = s.action.comp f := by
  apply MonoidHom.ext
  intro g
  apply LinearMap.ext
  intro v
  induction v using Submodule.Quotient.induction_on with | _ v => rfl

variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
  {σ : Representation (ZMod 2) D W} {K : Subgroup D}

/-- The component action is preserved even when its two ambient groups differ. -/
noncomputable def MovedSection.componentEmbeddingEquiv
    (s : MovedSection ρ L) (t : MovedSection σ K)
    (φ : K ≃* L) (e : W →ₗ[ZMod 2] V) (he : Function.Injective e)
    (hact : ∀ k : K, ∀ w, e (σ k w) = ρ (φ k) (e w))
    (hm : (moved σ K).map e = moved ρ L) :
    ActionEquiv (t.action.comp K.subtype) (s.action.comp L.subtype) := by
  let f := L.subtype.comp φ.toMonoidHom
  have hf : (⊤ : Subgroup K).map f = L := by
    change (⊤ : Subgroup K).map (L.subtype.comp φ.toMonoidHom) = L
    rw [←Subgroup.map_map,map_top_of_surjective φ.toMonoidHom φ.surjective,
      ←MonoidHom.range_eq_map,L.range_subtype]
  have hg : (⊤ : Subgroup K).map K.subtype = K := by
    rw [←MonoidHom.range_eq_map,K.range_subtype]
  let s' := s.comp f ⊤ hf
  let t' := t.comp K.subtype ⊤ hg
  have hm' : (moved (σ.comp K.subtype) (⊤ : Subgroup K)).map e =
      moved (ρ.comp f) (⊤ : Subgroup K) := by
    rw [moved_comp_map,moved_comp_map,hf,hg]
    exact hm
  let E := s'.embeddingEquiv t' e he hact hm'
  refine ⟨φ,E.toLinearEquiv,?_⟩
  intro k v
  exact E.isIntertwining k v

end CFSG.Quasithin.ChapterB.QuasisimpleSource
