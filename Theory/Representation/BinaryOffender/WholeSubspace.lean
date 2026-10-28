module
public import Theory.Representation.BinaryOffender.Restriction
public import Theory.Representation.BinaryOffender.EquivariantBest
public import Theory.Representation.BinaryOffender.AmbientSectionTransport

/-!
# Faithful restriction to a whole invariant subspace

If an invariant subspace detects every group element, its literal restricted
representation is faithful. The action image is then isomorphic to the original
group, so a best offender of the image is a best offender on the same actor.
This retains the original actor in the tilde-component application of
Aschbacher--Smith13.7.16(2), printed p.944.
-/
public section
open Subgroup Representation Representation.BinaryOffender
namespace Representation.BinaryOffender
variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V]
 [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
 (ρ : Representation (ZMod 2) G V) (I : Submodule (ZMod 2) V)
 (hs : (⊤ : Subgroup G) ≤ subspaceStabilizer ρ I)
 (hp : ∀ k : G, (∀ v ∈ I,ρ k v = v) → k = 1)

@[expose] def wholeSubspaceAction : Representation (ZMod 2) G I :=
  ρ.subrepresentation I (fun g _ hv => (hs (mem_top g) _).2 hv)

omit [Finite G] [FiniteDimensional (ZMod 2) V] in
theorem wholeSubspaceAction_apply (g : G) (v : I) :
    ((wholeSubspaceAction ρ I hs g v : I) : V) = ρ g v := rfl

omit [Finite G] [FiniteDimensional (ZMod 2) V] in
include hp in
theorem wholeSubspaceAction_faithful : Function.Injective (wholeSubspaceAction ρ I hs) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply bot_unique
  intro k hk
  apply mem_bot.mpr
  apply hp k
  intro v hv
  have he := LinearMap.congr_fun hk (⟨v,hv⟩ : I)
  exact congrArg Subtype.val he

noncomputable def wholeSubspaceImageEquiv : G ≃* subspaceActionImage ρ I :=
  MulEquiv.ofBijective
    ((subspaceActionHom ρ I).comp
      (show G →* subspaceStabilizer ρ I from
        {toFun g := ⟨g,hs (mem_top g)⟩,map_one' := rfl,map_mul' _ _ := rfl}))
    ⟨by
      apply (MonoidHom.ker_eq_bot_iff _).mp
      apply bot_unique
      intro g hg
      apply mem_bot.mpr
      apply hp g
      intro v hv
      have he := congrArg (fun k => subspaceImageRepresentation ρ I k (⟨v,hv⟩ : I)) hg
      exact congrArg Subtype.val he,
    by
      intro y
      obtain ⟨g,hg⟩ := (stabilizerRepresentation ρ I).asGroupHom.rangeRestrict_surjective y
      exact ⟨g.val,hg⟩⟩

omit [Finite G] in
include hp in
theorem wholeSubspaceAction_bestOffender {D : Subgroup G}
    (hD : IsBestOffender (subspaceImageRepresentation ρ I) (restrictedSubgroup ρ I D)) :
    IsBestOffender (wholeSubspaceAction ρ I hs) D := by
  let e := wholeSubspaceImageEquiv ρ I hs hp
  have he : (restrictedSubgroup ρ I D).map e.symm.toMonoidHom = D := by
    ext g
    constructor
    · rintro ⟨x,hx,rfl⟩
      obtain ⟨k,hk,rfl⟩ := hx
      have he : e k.val = subspaceActionHom ρ I k := rfl
      rw [←he]
      change e.symm (e k.val) ∈ D
      rw [e.symm_apply_apply]
      exact hk
    · intro hg
      refine ⟨e g,?_,e.symm_apply_apply g⟩
      exact ⟨⟨g,hs (mem_top g)⟩,hg,rfl⟩
  rw [←he]
  apply hD.map_equivariant (subspaceImageRepresentation ρ I)
    (wholeSubspaceAction ρ I hs) e.symm (LinearEquiv.refl (ZMod 2) I)
  intro k v
  change subspaceImageRepresentation ρ I k v = wholeSubspaceAction ρ I hs (e.symm k) v
  have hact : ∀ g : G, ∀ v : I,
      subspaceImageRepresentation ρ I (e g) v = wholeSubspaceAction ρ I hs g v :=
    fun _ _ => rfl
  simpa only [e.apply_symm_apply] using hact (e.symm k) v

end Representation.BinaryOffender
