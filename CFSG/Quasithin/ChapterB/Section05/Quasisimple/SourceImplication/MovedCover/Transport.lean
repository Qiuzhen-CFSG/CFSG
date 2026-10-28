module
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.MovedCover.Elementary

/-!
# Transport of a moved cover to an embedded component

An injective ambient homomorphism transports the canonical moved cover to
its literal image subgroup. The resulting component actor is surjective,
acts by conjugation in the target group, and retains the centralizer kernel.
This supplies the graph-vertex realization of MS93 (3.2)(vi).
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender Representation.OneCohomology
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterB.QuasisimpleSource.ElementaryMovedCover
variable {H J : Type*} [Group H] [Group J]
  (X K : Subgroup H) [X.Normal] [IsElementaryAbelian 2 X]
  (q : H →* J) (hq : Function.Surjective q)
  (hker : q.ker = centralizer (X : Set H)) [(K.map q).Normal]
local notation "ρ" => NormalElementaryQuotient.representation X q hq hker
local notation "s" => MovedSection.ofNormal ρ (K.map q)
variable {A W G : Type*} [Group A] [AddCommGroup W] [Module (ZMod 2) W] [Group G]
  {τ : Representation (ZMod 2) A W}

theorem exists_conjugationActor (i : H →* G) (hi : Function.Injective i)
    (L : Subgroup G) (hL : K.map i = L)
    (e : ActionEquiv ((s).action.comp (K.map q).subtype) τ) :
    ∃ f : L →* A, Function.Surjective f ∧
      (∀ (k : L) (v : (s).space.toSubmodule),
        i (embedding X K q hq hker (Multiplicative.ofAdd
          (MovedSection.coverAction s e (f k) v))) =
          (k:G) * i (embedding X K q hq hker (Multiplicative.ofAdd v)) * (k:G)⁻¹) ∧
      (∀ v : (s).space.toSubmodule, MovedSection.coverProjection s e v = 0 ↔
        i (embedding X K q hq hker (Multiplicative.ofAdd v)) ∈ centralizer (L : Set G)) := by
  let d : K ≃* L := (K.equivMapOfInjective i hi).trans (MulEquiv.subgroupCongr hL)
  have hds (k : L) : i (d.symm k) = (k : G) := by
    exact congrArg Subtype.val (d.apply_symm_apply k)
  let f : L →* A := e.groupEquiv.toMonoidHom.comp
    ((q.subgroupMap K).comp d.symm.toMonoidHom)
  refine ⟨f,e.groupEquiv.surjective.comp
    ((q.subgroupMap_surjective K).comp d.symm.surjective),?_,?_⟩
  · intro k v
    have hh := congrArg i (cover_action_conjugate X K q hq hker e (d.symm k) v)
    simpa only [f,MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom,map_mul,map_inv,hds] using hh
  · intro v
    rw [cover_kernel_iff]
    constructor
    · intro hv k hk
      obtain ⟨x,hx,rfl⟩ := show k ∈ K.map i from hL.symm ▸ hk
      simpa only [map_mul] using congrArg i (hv x hx)
    · intro hv k hk
      apply hi
      simpa only [map_mul] using hv (i k) (hL ▸ mem_map_of_mem i hk)
end CFSG.Quasithin.ChapterB.QuasisimpleSource.ElementaryMovedCover
