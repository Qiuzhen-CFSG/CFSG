module
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.MovedSection
public import Theory.Representation.RepEquiv
public import Theory.Representation.BinaryOffender.IrreducibleTransport
public import Theory.Representation.BinaryOffender.NoncentralMoved

/-!
# Restricting the original moved central quotient

An equivariant embedding identifying the actual moved spaces induces an
equivalence of their quotients by their actual fixed spaces. For a perfect
actor with an irreducible moved central quotient, every noncentral invariant
submodule supplies that equality. Both constructions preserve the complete
ambient action rather than merely the module dimension or group model.
Source application: Aschbacher–Smith C.2.7(3)(a), pp.146–147.
-/

public section
open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterB.QuasisimpleSource
variable {G V W : Type*} [Group G]
  [AddCommGroup V] [Module (ZMod 2) V] [AddCommGroup W] [Module (ZMod 2) W]
  {ρ : Representation (ZMod 2) G V} {σ : Representation (ZMod 2) G W}
  {L : Subgroup G}

noncomputable def MovedSection.embeddingEquiv
    (s : MovedSection ρ L) (t : MovedSection σ L)
    (e : W →ₗ[ZMod 2] V) (he : Function.Injective e)
    (hact : ∀ g w, e (σ g w) = ρ g (e w))
    (hm : (moved σ L).map e = moved ρ L) : RepEquiv t.action s.action := by
  have hmap : t.space.toSubmodule.map e = s.space.toSubmodule := by
    rw [t.space_eq,s.space_eq]; exact hm
  let f : t.space.toSubmodule →ₗ[ZMod 2] s.space.toSubmodule :=
    (e.comp t.space.toSubmodule.subtype).codRestrict s.space.toSubmodule
      (fun v => hmap ▸ (show e v ∈ t.space.toSubmodule.map e from ⟨v,v.property,rfl⟩))
  have hf : Function.Bijective f := by
    constructor
    · intro a b hab
      exact Subtype.ext (he (congrArg Subtype.val hab))
    · intro v
      obtain ⟨w,hw,hew⟩ := (show (v : V) ∈ t.space.toSubmodule.map e from hmap.symm ▸ v.property)
      exact ⟨⟨w,hw⟩,Subtype.ext hew⟩
  let E := LinearEquiv.ofBijective f hf
  have hE (g : G) (v : t.space.toSubmodule) :
      E (t.space.toRepresentation g v) = s.space.toRepresentation g (E v) := by
    apply Subtype.ext
    exact hact g v
  have hc : t.central.toSubmodule.map E.toLinearMap = s.central.toSubmodule := by
    rw [t.central_eq,s.central_eq]
    ext v
    constructor
    · rintro ⟨w,hw,rfl⟩ l
      change s.space.toRepresentation (l : G) (E w) = E w
      rw [←hE]
      exact congrArg E (hw l)
    · intro hv
      refine ⟨E.symm v,?_,E.apply_symm_apply v⟩
      intro l
      apply E.injective
      change E (t.space.toRepresentation (l : G) (E.symm v)) = E (E.symm v)
      rw [hE,E.apply_symm_apply]
      exact hv l
  refine ⟨Submodule.Quotient.equiv _ _ E hc,?_⟩
  intro g
  apply LinearMap.ext
  intro v
  induction v using Submodule.Quotient.induction_on with | _ v =>
  change Submodule.Quotient.mk (E (t.space.toRepresentation g v)) =
    Submodule.Quotient.mk (s.space.toRepresentation g (E v))
  rw [hE]

/-- Restriction to a noncentral invariant module preserves the literal moved
central quotient, including the action of the entire group. -/
noncomputable def MovedSection.embeddingEquiv_of_noncentral
    [Group.IsPerfect L]
    (s : MovedSection ρ L) (t : MovedSection σ L)
    (e : W →ₗ[ZMod 2] V) (he : Function.Injective e)
    (hact : ∀ g w, e (σ g w) = ρ g (e w))
    (hi : IsIrrPlus ρ L (moved ρ L))
    (hn : ¬ LinearMap.range e ≤ fixedSpace ρ L) : RepEquiv t.action s.action := by
  have hstab : L ≤ subspaceStabilizer ρ (LinearMap.range e) := by
    apply le_subspaceStabilizer
    rintro g hg _ ⟨w,rfl⟩
    exact ⟨σ g w,hact g w⟩
  have hmove := moved_eq_of_noncentral_invariant ρ L hi (LinearMap.range e) hstab hn
  have hmap := subspaceCommutator_map_embedding ρ σ (MonoidHom.id G) e
    (fun g w => (hact g w).symm) L ⊤
  have hm : (moved σ L).map e = moved ρ L := by
    change (subspaceCommutator σ ⊤ L).map e = subspaceCommutator ρ ⊤ L
    have hh : subspaceCommutator ρ (LinearMap.range e) L =
        (subspaceCommutator σ ⊤ L).map e := by
      simpa only [Submodule.map_top,Subgroup.map_id] using hmap
    exact hh.symm.trans hmove
  exact s.embeddingEquiv t e he hact hm

end CFSG.Quasithin.ChapterB.QuasisimpleSource
