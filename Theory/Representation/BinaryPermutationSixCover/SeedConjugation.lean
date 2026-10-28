module
public import Theory.Representation.BinaryPermutationSixCover.SeedPreimage
public import Theory.Representation.BinaryGroupAction
public import Theory.GroupTheory.PCoreLocalSetup

/-!
# Conjugation on an eight-element six-core seed

A surjective faithful actor marking identifies the original fixed point with
its constant word. An invariant seed of order eight then has a natural image
of order four. The two-core of a two-perfect seed normalizer fixes that image
and its core lifts, hence centralizes the original seed.

Source application: Aschbacher–Smith, reduction 13.3.14(g), printed p.893.
-/
public section
open Subgroup Representation BinaryPermutation
namespace BinaryPermutation.SixCover

/-- Transport the invariant seed to the actual core, keeping its fixed point. -/
theorem core_model_twoCore_centralizes_seed
    {G : Type*} [Group G] [Finite G]
    (B A W U P : Subgroup G) (hAB : A ≤ B) (hA : IsPPerfect 2 A)
    (hBW : B ≤ normalizer (W : Set G)) (hAU : A ≤ normalizer (U : Set G))
    (hUW : U ≤ W) (hPU : P ≤ U) (hPB : P ≤ centralizer (B : Set G))
    (hU : Nat.card U = 8) (hP : Nat.card P = 2)
    (β : B →* alternatingGroup (Fin 6)) (hβ : Function.Surjective β)
    (c : W ≃* Multiplicative (core (Fin 6)))
    (hc : ∀ (b : B) (w : W),
      (c (W.normalizerMonoidHom ⟨b,hBW b.property⟩ w)).toAdd =
        alternatingCoreRepresentation (Fin 6) (β b) (c w).toAdd) :
    A.pCoreIn 2 ≤ centralizer (U : Set G) := by
  let S := (U.subgroupOf W).map c.toMonoidHom
  let I : Submodule (ZMod 2) (core (Fin 6)) := BinaryGroupAction.submoduleEquivSubgroup.symm S
  have hI : Nat.card I = 8 := by
    rw [← BinaryGroupAction.card_submoduleEquivSubgroup I]
    change Nat.card S = 8
    rw [card_map_of_injective c.injective,
      Nat.card_congr (subgroupOfEquivOfLe hUW).toEquiv,hU]
  have hzne : P ≠ ⊥ := by intro hz; rw [hz,card_bot] at hP; omega
  obtain ⟨p',hp'⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hzne
  let p : G := p'
  have hp : p ∈ P := p'.property
  have hp1 : p ≠ 1 := fun h => hp' (Subtype.ext h)
  let w : W := ⟨p,hUW (hPU hp)⟩
  have hwfix : ∀ b : B, W.normalizerMonoidHom ⟨b,hBW b.property⟩ w = w := by
    intro b
    apply Subtype.ext
    change (b : G) * p * (b : G)⁻¹ = p
    apply mul_inv_eq_iff_eq_mul.mpr
    exact (mem_centralizer_iff.mp (hPB hp)) b b.property
  have hz : (c w).toAdd = sixCoreConstant := by
    apply ((sixCore_fixed_iff _).mp ?_).resolve_left
    · intro hz
      apply hp1
      have he : c w = 1 := congrArg Multiplicative.ofAdd hz
      exact congrArg Subtype.val (c.injective (he.trans c.map_one.symm))
    · intro a
      obtain ⟨b,rfl⟩ := hβ a
      rw [←hc,hwfix]
  have hzi : sixCoreConstant ∈ I := by
    rw [←hz]
    change c w ∈ S
    exact mem_map_of_mem c.toMonoidHom (show w ∈ U.subgroupOf W from hPU hp)
  let f := β.comp (inclusion hAB)
  have hinv : ∀ a : A, ∀ v ∈ I, alternatingCoreRepresentation (Fin 6) (f a) v ∈ I := by
    intro a v hv
    change Multiplicative.ofAdd v ∈ S at hv
    obtain ⟨x,hx,he⟩ := hv
    have he' : (c x).toAdd = v := congrArg Multiplicative.toAdd he
    rw [←he']
    change alternatingCoreRepresentation (Fin 6) (β (inclusion hAB a))
      (c x).toAdd ∈ I
    rw [←hc (inclusion hAB a) x]
    change c (W.normalizerMonoidHom _ x) ∈ S
    apply mem_map_of_mem
    exact (mem_normalizer_iff.mp (hAU a.property) x).mp hx
  intro g hg u hu
  obtain ⟨a,ha,rfl⟩ := hg
  let x : W := ⟨u,hUW hu⟩
  have hx : (c x).toAdd ∈ I := mem_map_of_mem c.toMonoidHom hu
  have hfix := SixCover.core_seed_twoCore_fixed hA f I hI hzi hinv a ha (c x).toAdd hx
  change alternatingCoreRepresentation (Fin 6) (β (inclusion hAB a))
    (c x).toAdd = (c x).toAdd at hfix
  have he := hc (inclusion hAB a) x
  rw [hfix] at he
  have he' := congrArg (fun y : W => (y : G))
    (c.injective (congrArg Multiplicative.ofAdd he))
  change (a : G) * u * (a : G)⁻¹ = u at he'
  exact (mul_inv_eq_iff_eq_mul.mp he').symm

end BinaryPermutation.SixCover
