module
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.MovedRestriction
/-!
# Marked automorphisms of actual moved sections

A linear automorphism compatible with a specified automorphism of L preserves
[V,L] and its L-fixed subspace. It therefore acts on the actual moved space
and central quotient, retaining the given actor marking. Transport through
an action equivalence supplies the corresponding intertwiner on a model.
No invariance of a larger offender group is required.

Source application: Aschbacher–Smith B.5.1 and15.3.20, pp.99–103,1127–1128.
-/
public section
open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterB.QuasisimpleSource
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} {L : Subgroup G}

private theorem moved_map_le_twisted
    (α : L →* L) (f : V →ₗ[ZMod 2] V)
    (hf : ∀ l : L, ∀ v, f (ρ l v) = ρ (α l) (f v)) :
    (moved ρ L).map f ≤ moved ρ L := by
  apply Submodule.map_le_iff_le_comap.mpr
  apply Submodule.span_le.mpr
  rintro _ ⟨l,hl,v,_,rfl⟩
  change f (ρ l v - v) ∈ moved ρ L
  rw [map_sub, hf ⟨l,hl⟩]
  exact Submodule.subset_span ⟨α ⟨l,hl⟩,(α ⟨l,hl⟩).property,f v,Submodule.mem_top,rfl⟩

theorem moved_map_eq_twisted
    (α : MulAut L) (f : V ≃ₗ[ZMod 2] V)
    (hf : ∀ l : L, ∀ v, f (ρ l v) = ρ (α l) (f v)) :
    (moved ρ L).map f.toLinearMap = moved ρ L := by
  refine le_antisymm (moved_map_le_twisted α.toMonoidHom f.toLinearMap hf) ?_
  have hi : ∀ l : L, ∀ v, f.symm (ρ l v) = ρ (α.symm l) (f.symm v) := by
    intro l v
    apply f.injective
    rw [f.apply_symm_apply,hf,α.apply_symm_apply,f.apply_symm_apply]
  intro v hv
  refine ⟨f.symm v,?_,f.apply_symm_apply v⟩
  exact moved_map_le_twisted α.symm.toMonoidHom f.symm.toLinearMap hi ⟨v,hv,rfl⟩

noncomputable def MovedSection.twistedSpaceEquiv
    (s : MovedSection ρ L) (α : MulAut L) (f : V ≃ₗ[ZMod 2] V)
    (hf : ∀ l : L, ∀ v, f (ρ l v) = ρ (α l) (f v)) :
    s.space.toSubmodule ≃ₗ[ZMod 2] s.space.toSubmodule :=
  f.ofSubmodules _ _ (by rw [s.space_eq]; exact moved_map_eq_twisted α f hf)

theorem MovedSection.twistedSpaceEquiv_intertwines
    (s : MovedSection ρ L) (α : MulAut L) (f : V ≃ₗ[ZMod 2] V)
    (hf : ∀ l : L, ∀ v, f (ρ l v) = ρ (α l) (f v)) (l : L) (v) :
    s.twistedSpaceEquiv α f hf (s.space.toRepresentation l v) =
      s.space.toRepresentation (α l) (s.twistedSpaceEquiv α f hf v) := by
  apply Subtype.ext
  exact hf l v

noncomputable def MovedSection.twistedActionEquiv
    (s : MovedSection ρ L) (α : MulAut L) (f : V ≃ₗ[ZMod 2] V)
    (hf : ∀ l : L, ∀ v, f (ρ l v) = ρ (α l) (f v)) :
    ActionEquiv (s.action.comp L.subtype) (s.action.comp L.subtype) :=
  by
    let a := L.subtype.comp α.toMonoidHom
    have ha : (⊤ : Subgroup L).map a = L := by
      rw [show a = L.subtype.comp α.toMonoidHom from rfl, ←Subgroup.map_map,
        map_top_of_surjective _ α.surjective,←MonoidHom.range_eq_map,L.range_subtype]
    have hi : (⊤ : Subgroup L).map L.subtype = L := by
      rw [←MonoidHom.range_eq_map,L.range_subtype]
    let s' := s.comp a ⊤ ha
    let t' := s.comp L.subtype ⊤ hi
    have hm : (moved (ρ.comp L.subtype) (⊤ : Subgroup L)).map f.toLinearMap =
        moved (ρ.comp a) (⊤ : Subgroup L) := by
      rw [moved_comp_map,moved_comp_map,ha,hi]
      exact moved_map_eq_twisted α f hf
    let E := s'.embeddingEquiv t' f.toLinearMap f.injective hf hm
    exact ⟨α,E.toLinearEquiv,fun l v => E.isIntertwining l v⟩

theorem MovedSection.twistedActionEquiv_actor
    (s : MovedSection ρ L) (α : MulAut L) (f : V ≃ₗ[ZMod 2] V)
    (hf : ∀ l : L, ∀ v, f (ρ l v) = ρ (α l) (f v)) :
    (s.twistedActionEquiv α f hf).groupEquiv = α := by rfl

theorem MovedSection.twistedActionEquiv_intertwines
    (s : MovedSection ρ L) (α : MulAut L) (f : V ≃ₗ[ZMod 2] V)
    (hf : ∀ l : L, ∀ v, f (ρ l v) = ρ (α l) (f v)) (l : L) (v) :
    (s.twistedActionEquiv α f hf).linearEquiv ((s.action.comp L.subtype) l v) =
      (s.action.comp L.subtype) (α l) ((s.twistedActionEquiv α f hf).linearEquiv v) := by
  have hh := (s.twistedActionEquiv α f hf).intertwines l v
  rw [s.twistedActionEquiv_actor α f hf] at hh
  exact hh

variable {D W : Type*} [Group D] [AddCommGroup W] [Module (ZMod 2) W]
  {σ : Representation (ZMod 2) D W}

theorem ActionEquiv.conjugate_intertwiner
    (e : ActionEquiv ρ σ) (α : MulAut G) (f : V ≃ₗ[ZMod 2] V)
    (hf : ∀ g v, f (ρ g v) = ρ (α g) (f v)) :
    ∀ g w, (e.linearEquiv.symm.trans (f.trans e.linearEquiv)) (σ g w) =
      σ ((e.groupEquiv.symm.trans (α.trans e.groupEquiv)) g)
        ((e.linearEquiv.symm.trans (f.trans e.linearEquiv)) w) := by
  intro g w
  obtain ⟨g,rfl⟩ := e.groupEquiv.surjective g
  obtain ⟨v,rfl⟩ := e.linearEquiv.surjective w
  simp only [LinearEquiv.trans_apply,MulEquiv.trans_apply,
    MulEquiv.symm_apply_apply,LinearEquiv.symm_apply_apply]
  rw [←e.intertwines, e.linearEquiv.symm_apply_apply,hf,e.intertwines]

end CFSG.Quasithin.ChapterB.QuasisimpleSource
