module

public import Stellmacher.SectionTwo.LemmaTwoFiveDefs
public import Mathlib.GroupTheory.Subgroup.Centralizer

/-!
# Transporting a normalizer action to the supplied Sylow subgroup

An injective ambient map identifies a supplied Sylow subgroup with its exact
image. Conjugation by a subgroup of the image normalizer then gives an action
on that original Sylow subgroup. The image action has odd order whenever the
acting subgroup does. The ambient join of its Section Two module translates
is exactly the conjugate closure of the ambient module under the actors.

The proof retains the image equivalence, verifies conjugation pointwise, and
compares the two generated subgroups in both directions. Containment of the
native module in the supplied Sylow is necessary for the reverse inclusion.
This is the transport step of Stellmacher (8.2)'s use of (2.5), independent of
the separate mathematical identification of the smaller group's module.
Source: refs/latex/stellmacher-n-group.tex, printed pp.37–38.
-/

namespace Stellmacher.SectionTwo

universe u v

@[expose] public noncomputable def sylowImageEquiv
    {G : Type u} {H : Type v} [Group G] [Group H]
    (T : Sylow 2 G) (f : G →* H) (hf : Function.Injective f)
    (B : Subgroup H) (hT : (T : Subgroup G).map f = B) : T ≃* B :=
  ((T : Subgroup G).equivMapOfInjective f hf).trans (MulEquiv.subgroupCongr hT)

@[expose] public noncomputable def sylowImageNormalizerAction
    {G : Type u} {H : Type v} [Group G] [Group H]
    (T : Sylow 2 G) (f : G →* H) (hf : Function.Injective f)
    (B : Subgroup H) (hT : (T : Subgroup G).map f = B)
    (U : Subgroup H) (hU : U ≤ Subgroup.normalizer (B : Set H)) :
    U →* MulAut T :=
  (MulAut.congr (sylowImageEquiv T f hf B hT).symm).toMonoidHom.comp
    (B.normalizerMonoidHom.comp (Subgroup.inclusion hU))

public theorem sylowImageNormalizerAction_apply
    {G : Type u} {H : Type v} [Group G] [Group H]
    (T : Sylow 2 G) (f : G →* H) (hf : Function.Injective f)
    (B : Subgroup H) (hT : (T : Subgroup G).map f = B)
    (U : Subgroup H) (hU : U ≤ Subgroup.normalizer (B : Set H))
    (actor : U) (element : T) :
    f ((sylowImageNormalizerAction T f hf B hT U hU actor element : T) : G) =
      (actor : H) * f (element : G) * (actor : H)⁻¹ := by
  let e := sylowImageEquiv T f hf B hT
  change (e (e.symm (B.normalizerMonoidHom (Subgroup.inclusion hU actor)
    (e element))) : H) = _
  rw [e.apply_symm_apply]
  rfl

public theorem sylowImageNormalizerAction_range_odd
    {G : Type u} {H : Type v} [Group G] [Group H]
    (T : Sylow 2 G) (f : G →* H) (hf : Function.Injective f)
    (B : Subgroup H) (hT : (T : Subgroup G).map f = B)
    (U : Subgroup H) (hU : U ≤ Subgroup.normalizer (B : Set H))
    (hodd : Odd (Nat.card U)) :
    Odd (Nat.card (sylowImageNormalizerAction T f hf B hT U hU).range) :=
  hodd.of_dvd_nat (Subgroup.card_range_dvd _)

public theorem map_sylowImageNormalizerAction_translate_join
    {G : Type u} {H : Type v} [Group G] [Group H]
    (T : Sylow 2 G) (f : G →* H) (hf : Function.Injective f)
    (B : Subgroup H) (hT : (T : Subgroup G).map f = B)
    (U : Subgroup H) (hU : U ≤ Subgroup.normalizer (B : Set H))
    (hV : vSubgroup T ≤ (T : Subgroup G)) :
    (⨆ actor : (sylowImageNormalizerAction T f hf B hT U hU).range,
      automorphismTranslateV T (actor : MulAut T)).map f =
      conjugateClosure ((vSubgroup T).map f) U := by
  let action := sylowImageNormalizerAction T f hf B hT U hU
  rw [Subgroup.map_iSup]
  apply le_antisymm
  · refine iSup_le fun actor => ?_
    obtain ⟨actorU, hactor⟩ := actor.property
    rintro element ⟨elementG, ⟨elementT, ⟨original, horiginal, rfl⟩, rfl⟩, rfl⟩
    apply Subgroup.subset_closure
    refine ⟨actorU, ⟨f (original : G), Subgroup.mem_map_of_mem f horiginal⟩, ?_⟩
    change f ((actor : MulAut T) original : G) = _
    rw [← hactor]
    exact sylowImageNormalizerAction_apply T f hf B hT U hU actorU original
  · apply (Subgroup.closure_le _).mpr
    rintro element ⟨actorU, original, rfl⟩
    obtain ⟨originalG, horiginalG, heq⟩ := original.property
    let originalT : T := ⟨originalG, hV horiginalG⟩
    let actor : action.range := ⟨action actorU, ⟨actorU, rfl⟩⟩
    apply (le_iSup (fun actor : action.range =>
      (automorphismTranslateV T (actor : MulAut T)).map f) actor)
    refine ⟨((action actorU) originalT : G), ?_, ?_⟩
    · exact ⟨(action actorU) originalT, ⟨originalT, horiginalG, rfl⟩, rfl⟩
    · rw [sylowImageNormalizerAction_apply T f hf B hT U hU actorU originalT]
      exact congrArg (fun element : H => (actorU : H) * element * (actorU : H)⁻¹) heq

end Stellmacher.SectionTwo
