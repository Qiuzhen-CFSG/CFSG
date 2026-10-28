module
public import CFSG.Quasithin.ChapterD.Section02.Defs
public import Theory.Representation.BinaryOffender.ComponentSum
public import Theory.Representation.BinaryOffender.MovedDimension

/-!
# Embeddings of ratio summands

An embedding retains the literal group map and linear inclusion, the original
starred actors, and a fixed complementary span. These data compose through
successive D.2.16 splittings. A fully moved local action has image exactly the
ambient commutator support. Terminal factors retain their faithful action,
starred generation, and indecomposability.

Source: Aschbacher--Smith D.2.16, printed p.187; used to flatten its finite
successive splittings without identifying different subgroup carriers.
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterD.RatioDecomposition
universe u v u' v' u'' v''
variable {G : Type u} {V : Type v} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  {H : Type u'} {W : Type v'} [Group H] [AddCommGroup W] [Module (ZMod 2) W]
  {L : Type u''} {X : Type v''} [Group L] [AddCommGroup X] [Module (ZMod 2) X]

structure Embedding (σ : Representation (ZMod 2) H W)
    (ρ : Representation (ZMod 2) G V) where
  groupMap : H →* G
  spaceMap : W →ₗ[ZMod 2] V
  group_injective : Function.Injective groupMap
  space_injective : Function.Injective spaceMap
  equivariant : ∀ g w, spaceMap (σ g w) = ρ (groupMap g) (spaceMap w)
  fixed_complement : spaceMap.range ⊔ fixedSpace ρ groupMap.range = ⊤
  ratio : cubicRatio σ = cubicRatio ρ
  stars : ∀ A, A ∈ QhatStar σ ↔ A.map groupMap ∈ QhatStar ρ

namespace Embedding
variable {ρ : Representation (ZMod 2) G V} {σ : Representation (ZMod 2) H W}
  {τ : Representation (ZMod 2) L X}

def refl (ρ : Representation (ZMod 2) G V) : Embedding ρ ρ where
  groupMap := MonoidHom.id G
  spaceMap := LinearMap.id
  group_injective := Function.injective_id
  space_injective := Function.injective_id
  equivariant _ _ := rfl
  fixed_complement := by simp
  ratio := rfl
  stars _ := by simp

def trans (a : Embedding τ σ) (b : Embedding σ ρ) : Embedding τ ρ where
  groupMap := b.groupMap.comp a.groupMap
  spaceMap := b.spaceMap.comp a.spaceMap
  group_injective := b.group_injective.comp a.group_injective
  space_injective := b.space_injective.comp a.space_injective
  equivariant g w := by
    change b.spaceMap (a.spaceMap (τ g w)) = _
    rw [a.equivariant, b.equivariant]
    rfl
  fixed_complement := by
    apply top_unique
    intro v _
    obtain ⟨w,hw,z,hz,rfl⟩ := Submodule.mem_sup.mp
      (show v ∈ b.spaceMap.range ⊔ fixedSpace ρ b.groupMap.range from
        b.fixed_complement ▸ Submodule.mem_top)
    obtain ⟨w,rfl⟩ := hw
    obtain ⟨x,hx,y,hy,rfl⟩ := Submodule.mem_sup.mp
      (show w ∈ a.spaceMap.range ⊔ fixedSpace σ a.groupMap.range from
        a.fixed_complement ▸ Submodule.mem_top)
    obtain ⟨x,rfl⟩ := hx
    rw [map_add, add_assoc]
    apply Submodule.mem_sup.mpr
    refine ⟨b.spaceMap (a.spaceMap x), ⟨x,rfl⟩, b.spaceMap y + z, ?_, rfl⟩
    rintro ⟨g,k,rfl⟩
    change ρ (b.groupMap (a.groupMap k)) (b.spaceMap y + z) = _
    rw [map_add, ← b.equivariant, (show σ (a.groupMap k) y = y from hy ⟨a.groupMap k, ⟨k,rfl⟩⟩),
      (show ρ (b.groupMap (a.groupMap k)) z = z from
        hz ⟨b.groupMap (a.groupMap k), ⟨a.groupMap k,rfl⟩⟩)]
  ratio := a.ratio.trans b.ratio
  stars A := by rw [← Subgroup.map_map, ← b.stars, ← a.stars]

theorem moved_le_range (e : Embedding σ ρ) :
    subspaceCommutator ρ ⊤ e.groupMap.range ≤ e.spaceMap.range := by
  apply Submodule.span_le.mpr
  rintro _ ⟨g, ⟨h,rfl⟩,v,_,rfl⟩
  obtain ⟨w,hw,z,hz,rfl⟩ := Submodule.mem_sup.mp
    (show v ∈ e.spaceMap.range ⊔ fixedSpace ρ e.groupMap.range from
      e.fixed_complement ▸ Submodule.mem_top)
  obtain ⟨w,rfl⟩ := hw
  refine ⟨σ h w - w, ?_⟩
  rw [map_sub, e.equivariant, map_add,
    (show ρ (e.groupMap h) z = z from hz ⟨e.groupMap h,⟨h,rfl⟩⟩)]
  abel

theorem support (e : Embedding σ ρ)
    (hfull : subspaceCommutator σ ⊤ ⊤ = ⊤) :
    subspaceCommutator ρ ⊤ e.groupMap.range = e.spaceMap.range := by
  apply le_antisymm e.moved_le_range
  have he := subspaceCommutator_map_embedding (ρ.comp e.groupMap) σ
    (MonoidHom.id H) e.spaceMap (fun g w => (e.equivariant g w).symm)
    ⊤ ⊤
  simp only [Subgroup.map_id, Submodule.map_top, hfull] at he
  rw [subspaceCommutator_comp_map, ← MonoidHom.range_eq_map] at he
  rw [← he]
  exact subspaceCommutator_mono_left ρ le_top _

theorem faithful (e : Embedding σ ρ) (hf : Function.Injective ρ) : Function.Injective σ := by
  intro a b hab
  apply e.group_injective
  apply hf
  ext v
  obtain ⟨w,hw,z,hz,rfl⟩ := Submodule.mem_sup.mp
    (show v ∈ e.spaceMap.range ⊔ fixedSpace ρ e.groupMap.range from
      e.fixed_complement ▸ Submodule.mem_top)
  obtain ⟨w,rfl⟩ := hw
  rw [map_add, map_add, ← e.equivariant, ← e.equivariant,
    (show ρ (e.groupMap a) z = z from hz ⟨e.groupMap a,⟨a,rfl⟩⟩),
    (show ρ (e.groupMap b) z = z from hz ⟨e.groupMap b,⟨b,rfl⟩⟩), hab]


theorem map_fixed (e : Embedding σ ρ) (U : Submodule (ZMod 2) W) (A : Subgroup H)
    (h : U ≤ fixedSpace σ A) :
    U.map e.spaceMap ≤ fixedSpace ρ (A.map e.groupMap) := by
  rintro _ ⟨w,hw,rfl⟩ ⟨g,k,hk,rfl⟩
  change ρ (e.groupMap k) (e.spaceMap w) = e.spaceMap w
  rw [← e.equivariant, show σ k w = w from h hw ⟨k,hk⟩]

end Embedding

structure Factor (ρ : Representation (ZMod 2) G V) where
  Carrier : Type u
  [group : _root_.Group Carrier]
  [finiteGroup : Finite Carrier]
  [nontrivialGroup : Nontrivial Carrier]
  Space : Type v
  [add : AddCommGroup Space]
  [moduleSpace : Module (ZMod 2) Space]
  [finiteSpace : FiniteDimensional (ZMod 2) Space]
  action : Representation (ZMod 2) Carrier Space
  embedding : Embedding action ρ
  faithful : Function.Injective action
  indecomposable : IsRatioIndecomposable action
  generated : Jhat action = ⊤
  full : subspaceCommutator action ⊤ ⊤ = ⊤
attribute [instance] Factor.group Factor.finiteGroup Factor.nontrivialGroup
  Factor.add Factor.moduleSpace Factor.finiteSpace

namespace Factor
variable {ρ : Representation (ZMod 2) G V}
  {D : Type u} {Y : Type v} [Group D] [AddCommGroup Y] [Module (ZMod 2) Y]
  {σ : Representation (ZMod 2) D Y}

def actor (a : Factor ρ) : Subgroup G := a.embedding.groupMap.range
def space (a : Factor ρ) : Submodule (ZMod 2) V := a.embedding.spaceMap.range

theorem space_eq_support (a : Factor ρ) :
    a.space = subspaceCommutator ρ ⊤ a.actor := (a.embedding.support a.full).symm

def map (a : Factor σ) (e : Embedding σ ρ) : Factor ρ where
  Carrier := a.Carrier
  Space := a.Space
  action := a.action
  embedding := a.embedding.trans e
  faithful := a.faithful
  indecomposable := a.indecomposable
  generated := a.generated
  full := a.full

@[simp] theorem map_actor (a : Factor σ) (e : Embedding σ ρ) :
    (a.map e).actor = a.actor.map e.groupMap := MonoidHom.range_comp _ _

@[simp] theorem map_space (a : Factor σ) (e : Embedding σ ρ) :
    (a.map e).space = a.space.map e.spaceMap := LinearMap.range_comp _ _

end Factor
end CFSG.Quasithin.ChapterD.RatioDecomposition
