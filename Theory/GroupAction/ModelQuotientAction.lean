module
public import Theory.GroupTheory.EquivariantParabolicLift
public import Mathlib.RepresentationTheory.Basic

/-!
# Bundling compatible quotient automorphisms

A surjective model map determines each induced automorphism uniquely.
Pointwise compatible automorphisms therefore assemble into a homomorphism,
while retaining their linear module implementers. This is the action
boundary used by the actual moved-section parabolic consumer in
Aschbacher–Smith 15.3.20, printed p.1127.
-/

public section
open Subgroup
namespace Subgroup.EquivariantLift
variable {G D W : Type*} [Group G] [Group D] [AddCommGroup W] [Module (ZMod 2) W]

theorem model_action (L A : Subgroup G) (q : L →* D) (hq : Function.Surjective q)
    (hn : A ≤ normalizer (L : Set G)) (σ : Representation (ZMod 2) D W)
    (h : ∀ a : A, ∃ α : MulAut D, ∃ f : W ≃ₗ[ZMod 2] W,
      (∀ l : L, q (L.normalizerMonoidHom (inclusion hn a) l) = α (q l)) ∧
        ∀ g w, f (σ g w) = σ (α g) (f w)) :
    ∃ α : A →* MulAut D,
      (∀ a l, q (L.normalizerMonoidHom (inclusion hn a) l) = α a (q l)) ∧
        ∀ a, ∃ f : W ≃ₗ[ZMod 2] W, ∀ g w, f (σ g w) = σ (α a g) (f w) := by
  classical
  choose β f heq himpl using h
  let γ : A →* MulAut L := L.normalizerMonoidHom.comp (inclusion hn)
  have he (a : A) (l : L) : q (γ a l) = β a (q l) := heq a l
  let α : A →* MulAut D :=
    { toFun := β
      map_one' := by
        ext x
        obtain ⟨l,rfl⟩ := hq x
        change β 1 (q l) = q l
        rw [←he, map_one]
        rfl
      map_mul' := by
        intro a b
        ext x
        obtain ⟨l,rfl⟩ := hq x
        change β (a*b) (q l) = β a (β b (q l))
        rw [←he, ←he, ←he, map_mul]
        rfl }
  exact ⟨α,heq,fun a => ⟨f a,himpl a⟩⟩
end Subgroup.EquivariantLift
