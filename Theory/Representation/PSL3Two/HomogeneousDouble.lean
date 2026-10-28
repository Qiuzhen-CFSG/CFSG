module
public import Theory.Representation.PSL3Two.NaturalDualCentralizer
public import Theory.Representation.Quotient

/-!
# A homogeneous double cannot have opposite natural factors

A nonzero map from a simple module into two copies of one simple module has
nonzero projection onto a summand. Dually, a nonzero map from the double onto
a simple module has nonzero restriction to a summand. Schur's lemma identifies
both simple modules. The binary natural and dual SL3 modules are inequivalent,
so they cannot occur on opposite sides of a homogeneous double, even with an
unrelated marking of its repeated constituent.

The concrete surjective-actor application is the representation step for
Aschbacher--Smith 15.3.24: the actual residual core modulo its center has a
natural submodule and a dual quotient, whereas the distance-four MS source
makes it a homogeneous double. No exact sequence or splitting is required.
-/

public section
open Representation
namespace Representation
variable {k G V W X : Type*} [Field k] [Group G]
  [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
  [AddCommGroup X] [Module k X]
  {ρ : Representation k G V} {σ : Representation k G W} {τ : Representation k G X}

/-- A simple module occurring below a homogeneous double and a simple module
occurring above it are equivalent. No splitting or exactness is assumed. -/
theorem equiv_of_nonzero_maps_through_double
    [IsIrreducible ρ] [IsIrreducible σ] [IsIrreducible τ]
    (i : ρ.IntertwiningMap (σ.prod σ)) (hi : i ≠ 0)
    (p : (σ.prod σ).IntertwiningMap τ) (hp : p ≠ 0) : Nonempty (ρ.Equiv τ) := by
  have hi' : ∃ f : ρ.IntertwiningMap σ, f ≠ 0 := by
    let f := (IntertwiningMap.fst k σ σ).comp i
    let g := (IntertwiningMap.snd k σ σ).comp i
    by_cases hf : f = 0
    · refine ⟨g, ?_⟩
      intro hg
      apply hi
      apply IntertwiningMap.ext
      apply LinearMap.ext
      intro v
      apply Prod.ext
      · exact congrArg (fun t : ρ.IntertwiningMap σ => t v) hf
      · exact congrArg (fun t : ρ.IntertwiningMap σ => t v) hg
    · exact ⟨f, hf⟩
  have hp' : ∃ f : σ.IntertwiningMap τ, f ≠ 0 := by
    let f := p.comp (IntertwiningMap.inl k σ σ)
    let g := p.comp (IntertwiningMap.inr k σ σ)
    by_cases hf : f = 0
    · refine ⟨g, ?_⟩
      intro hg
      apply hp
      ext v
      have hsum : v = (v.1, 0) + (0, v.2) := by simp
      rw [hsum, map_add]
      have h₁ := congrArg (fun t : σ.IntertwiningMap τ => t v.1) hf
      have h₂ := congrArg (fun t : σ.IntertwiningMap τ => t v.2) hg
      change p (v.1, 0) = 0 at h₁
      change p (0, v.2) = 0 at h₂
      rw [h₁, h₂, add_zero]
      rfl
    · exact ⟨f, hf⟩
  obtain ⟨f, hf⟩ := hi'
  obtain ⟨g, hg⟩ := hp'
  rcases IsIrreducible.bijective_or_eq_zero f with hf' | hf'
  · rcases IsIrreducible.bijective_or_eq_zero g with hg' | hg'
    · exact ⟨(f.ofBijective hf').trans (g.ofBijective hg')⟩
    · exact (hg hg').elim
  · exact (hf hf').elim

end Representation

namespace BinaryLinearThree.HomogeneousDouble
variable {D X : Type*} [_root_.Group D] [AddCommGroup X] [Module (ZMod 2) X]
  (σ : Representation (ZMod 2) D X) [IsIrreducible σ]
  (actor : D →* Group) (onto : Function.Surjective actor)

include onto in
/-- The natural and dual representations of the same surjective actor cannot
occur respectively below and above any doubled irreducible representation. -/
theorem no_natural_dual_maps
    (i : Representation.IntertwiningMap (W.comp actor) (σ.prod σ)) (hi : i ≠ 0)
    (p : (σ.prod σ).IntertwiningMap (W.dual.comp actor)) (hp : p ≠ 0) : False := by
  let : IsIrreducible (W.comp actor) :=
    (irreducible_comp_surjective_iff actor onto W).mpr IrreducibleCatalogue.natural_irreducible
  let : IsIrreducible (W.dual.comp actor) :=
    (irreducible_comp_surjective_iff actor onto W.dual).mpr IrreducibleCatalogue.dual_irreducible
  obtain ⟨e⟩ := equiv_of_nonzero_maps_through_double i hi p hp
  apply AutomorphismAction.natural_not_equiv_dual
  refine ⟨{ toLinearEquiv := e.toLinearEquiv, isIntertwining' := ?_ }⟩
  intro g
  obtain ⟨d, rfl⟩ := onto g
  exact e.isIntertwining' d

end BinaryLinearThree.HomogeneousDouble
