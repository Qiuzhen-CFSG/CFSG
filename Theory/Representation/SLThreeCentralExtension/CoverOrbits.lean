module
public import Theory.Representation.SLThreeCentralExtension.SylowCover

/-!
# Orbits of commutator-generated binary-three covers

A central cover of the natural SL₃(2) module is indecomposable because its
head is simple. If its kernel is nonzero, the dual H¹ bound makes that kernel
a line. The nonsplit-extension orbit theorem therefore applies to the original
cover: its nonkernel vectors form one orbit and its Sylow-fixed space is its
kernel. No separate indecomposability or dimension premise is required.
Source: Aschbacher--Smith, B.4.8(1--2), p.91, used in 10.2.8--9, pp.749--750.
-/

public section
open Representation Module
namespace Representation.OneCohomology.SLThreeCentralExtension
open BinaryLinearThree
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]
  {ρ : Representation (ZMod 2) BinaryLinearThree.Group V}

private theorem natural_simple (X : Submodule (ZMod 2) Vector)
    (hX : ∀ g v, v ∈ X → W g v ∈ X) : X = ⊥ ∨ X = ⊤ := by
  by_cases hb : X = ⊥
  · exact Or.inl hb
  · right
    obtain ⟨x,hx,hx0⟩ := (Submodule.ne_bot_iff X).mp hb
    apply top_unique
    intro y _
    by_cases hy : y = 0
    · exact hy ▸ X.zero_mem
    obtain ⟨g,hg⟩ := natural_transitive_nonzero x y hx0 hy
    exact hg ▸ hX g x hx

private theorem positive_kernel_line
    (p : ρ.IntertwiningMap W) (hp : IsCover p) (hne : p.toLinearMap.ker ≠ ⊥) :
    ∃ z : V, z ≠ 0 ∧ (∀ x, p x = 0 ↔ x = 0 ∨ x = z) ∧
      (∀ g, ρ g z = z) := by
  have hlo : 0 < finrank (ZMod 2) p.toLinearMap.ker := by
    have hn : finrank (ZMod 2) p.toLinearMap.ker ≠ 0 :=
      fun he => hne (Submodule.finrank_eq_zero.mp he)
    omega
  have hle := finrank_ker_le_H1_of_cover p hp
  rw [finrank_H1_dual] at hle
  have hd : finrank (ZMod 2) p.toLinearMap.ker = 1 := by omega
  have hc : Nat.card p.toLinearMap.ker = 2 := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod,hd]
    decide
  obtain ⟨z,hz,hu⟩ := (Nat.card_eq_two_iff' (0 : p.toLinearMap.ker)).mp hc
  refine ⟨z,fun he => hz (Subtype.ext he),?_,fun g => hp.2.1 z.property g⟩
  intro x
  constructor
  · intro hx
    by_cases h0 : x = 0
    · exact Or.inl h0
    · exact Or.inr (congrArg Subtype.val (hu ⟨x,hx⟩
        (fun he => h0 (congrArg Subtype.val he))))
  · rintro (rfl | rfl)
    · exact map_zero p
    · exact z.property

/-- A positive central cover has one orbit on all vectors outside its actual kernel. -/
theorem transitive_outside_kernel_of_cover
    (p : ρ.IntertwiningMap W) (hp : IsCover p) (hne : p.toLinearMap.ker ≠ ⊥)
    (x y : V) (hx : p x ≠ 0) (hy : p y ≠ 0) : ∃ g, ρ g x = y := by
  obtain ⟨z,hz,hker,hfix⟩ := positive_kernel_line p hp hne
  exact transitive_outside_kernel ρ p z hz hker hfix
    (indecomposable_of_cover_of_simple p hp natural_simple) x y hx hy

/-- In a positive central cover, a Sylow subgroup fixes only kernel vectors. -/
theorem sylow_fixed_eq_kernel_of_cover
    (p : ρ.IntertwiningMap W) (hp : IsCover p) (hne : p.toLinearMap.ker ≠ ⊥)
    (S : Sylow 2 BinaryLinearThree.Group) :
    BinaryOffender.fixedSpace ρ (S : Subgroup BinaryLinearThree.Group) =
      p.toLinearMap.ker := by
  apply le_antisymm
  · intro v hv
    change p v = 0
    by_contra hzero
    have hi := (cover_bijective_of_sylow_fixed ρ p hp S v hzero
      (fun s hs => hv ⟨s,hs⟩)).1
    exact hne ((LinearMap.ker_eq_bot).mpr hi)
  · intro v hv s
    exact hp.2.1 hv s

end Representation.OneCohomology.SLThreeCentralExtension
