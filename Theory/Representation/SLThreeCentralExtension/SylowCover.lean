module
public import Theory.Representation.SLThreeCentralExtension.Sylow
public import Theory.Representation.FirstCohomologyDuality.SimpleCover
public import Theory.Representation.SpecialLinearThreeTransitivity
/-!
# A Sylow-fixed nonzero head point splits a binary SL3 natural cover

The dual H1 bound makes a nonzero central kernel one-dimensional.
That gives a four-dimensional nonsplit cover, whose Sylow-fixed space
is exactly the central kernel by the original fourteen-vector orbit
calculation. A fixed point surviving in the natural head excludes this
case, so the actual covering projection is an isomorphism.

Source: Aschbacher–Smith, B.4.8(2), printed p.91, used in 13.7.6(1), p.939.
-/
@[expose] public section
open Representation Module
namespace Representation.OneCohomology.SLThreeCentralExtension
open BinaryLinearThree
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]
  (ρ : Representation (ZMod 2) BinaryLinearThree.Group V)
/-- The actual natural-cover map is bijective if a Sylow-fixed point survives it. -/
theorem cover_bijective_of_sylow_fixed
    (p : ρ.IntertwiningMap W) (hp : IsCover p)
    (S : Sylow 2 BinaryLinearThree.Group) (u : V) (hu : p u ≠ 0)
    (hfix : ∀ s ∈ S, ρ s u = u) : Function.Bijective p := by
  refine ⟨?_,hp.1⟩
  apply (LinearMap.ker_eq_bot).mp
  by_contra hker
  have hlo : 0 < finrank (ZMod 2) p.toLinearMap.ker := by
    have hn : finrank (ZMod 2) p.toLinearMap.ker ≠ 0 :=
      fun he => hker (Submodule.finrank_eq_zero.mp he)
    omega
  have hle := finrank_ker_le_H1_of_cover p hp
  rw [finrank_H1_dual] at hle
  have hdker : finrank (ZMod 2) p.toLinearMap.ker = 1 := by omega
  have hcard : Nat.card p.toLinearMap.ker = 2 := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod,hdker]
    decide
  obtain ⟨z,hz,huniq⟩ := (Nat.card_eq_two_iff' (0 : p.toLinearMap.ker)).mp hcard
  have hzn : z.val ≠ 0 := fun he => hz (Subtype.ext he)
  have hk : ∀ x, p x = 0 ↔ x = 0 ∨ x = z.val := by
    intro x
    constructor
    · intro hx
      by_cases h0 : x = 0
      · exact Or.inl h0
      · exact Or.inr (congrArg Subtype.val (huniq ⟨x,hx⟩ (fun he => h0 (congrArg Subtype.val he))))
    · rintro (rfl | rfl)
      · exact map_zero p
      · exact z.property
  have hd : finrank (ZMod 2) V = 4 := by
    have he := p.toLinearMap.finrank_range_add_finrank_ker
    rw [LinearMap.range_eq_top.mpr hp.1,finrank_top,hdker] at he
    have hw : finrank (ZMod 2) Vector = 3 := Module.finrank_fin_fun (ZMod 2)
    rw [hw] at he
    omega
  have hs : ∀ X : Submodule (ZMod 2) Vector,
      (∀ g v, v ∈ X → W g v ∈ X) → X = ⊥ ∨ X = ⊤ := by
    intro X hX
    by_cases hb : X = ⊥
    · exact Or.inl hb
    · right
      obtain ⟨x,hx,hx0⟩ := (Submodule.ne_bot_iff X).mp hb
      apply top_unique
      intro y _
      by_cases hy : y = 0
      · exact hy ▸ X.zero_mem
      obtain ⟨g,hg⟩ := Matrix.SpecialLinearGroup.exists_mulVec_eq_three x y hx0 hy
      exact hg ▸ hX g x hx
  have hind := indecomposable_of_cover_of_simple p hp hs
  have he := sylow_fixed_eq_kernel ρ p z hzn hk (fun g => hp.2.1 z.property g) hd hind S
  have hum : u ∈ BinaryOffender.fixedSpace ρ (S : Subgroup Group) := fun s => hfix s s.property
  rw [he] at hum
  exact hu hum
end Representation.OneCohomology.SLThreeCentralExtension
