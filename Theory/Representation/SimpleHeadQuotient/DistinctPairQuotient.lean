module
public import Theory.Representation.SimpleHeadQuotient.DistinctPair

/-!
# Nonzero quotients of two distinct simple modules

A nonzero quotient of a direct sum of two inequivalent simple modules is
one summand or the whole direct sum. Classifying its kernel constructs an
actual representation equivalence in each case. This supplies coordinates,
not only composition factors, for the local natural--dual action.

Source application: Aschbacher--Smith 10.2.9, printed p.752.
-/

public noncomputable section
open Representation
namespace Representation.SimpleHeadQuotient
variable {k H V W E : Type*} [Field k] [Group H]
  [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
  [AddCommGroup E] [Module k E] [Nontrivial E]

/-- A nonzero quotient of two inequivalent simple modules is one summand or
their direct sum, with explicit intertwining coordinates. -/
theorem distinct_pair_quotient (σ : Representation k H V) (τ : Representation k H W)
    [IsIrreducible σ] [IsIrreducible τ]
    (hne : ¬ Nonempty (σ.Equiv τ)) (η : Representation k H E)
    (p : (σ.prod τ).IntertwiningMap η) (hp : Function.Surjective p) :
    Nonempty (η.Equiv σ) ∨ Nonempty (η.Equiv τ) ∨ Nonempty (η.Equiv (σ.prod τ)) := by
  have hstable : ∀ g x, x ∈ p.toLinearMap.ker → (σ.prod τ) g x ∈ p.toLinearMap.ker := by
    intro g x hx
    change p ((σ.prod τ) g x) = 0
    change p x = 0 at hx
    rw [p.isIntertwining,hx,map_zero]
  rcases distinct_pair_submodules σ τ hne p.toLinearMap.ker hstable with h | h | h | h
  · exact Or.inr (Or.inr ⟨(p.ofBijective ⟨LinearMap.ker_eq_bot.mp h,hp⟩).symm⟩)
  · let f : τ.IntertwiningMap η := {
      toLinearMap := p.toLinearMap.comp (LinearMap.inr k V W)
      isIntertwining' g := by
        ext w
        simpa using LinearMap.congr_fun (p.isIntertwining' g) (0,w) }
    have hf : Function.Bijective f := by
      constructor
      · apply LinearMap.ker_eq_bot.mp
        apply bot_unique
        intro w hw
        have hh : (0,w) ∈ p.toLinearMap.ker := hw
        rw [h] at hh
        exact hh.2
      · intro x
        obtain ⟨⟨v,w⟩,hx⟩ := hp x
        have hz : p (v,0) = 0 := by
          apply LinearMap.mem_ker.mp
          rw [h]
          exact ⟨Submodule.mem_top, rfl⟩
        refine ⟨w,?_⟩
        have he : p (v,w) = p (v,0) + p (0,w) := by
          simpa only [Prod.mk_add_mk,add_zero,zero_add,IntertwiningMap.coe_toLinearMap] using p.map_add (v,0) (0,w)
        rw [hz,zero_add] at he
        exact he.symm.trans hx
    exact Or.inr (Or.inl ⟨(f.ofBijective hf).symm⟩)
  · let f : σ.IntertwiningMap η := {
      toLinearMap := p.toLinearMap.comp (LinearMap.inl k V W)
      isIntertwining' g := by
        ext v
        simpa using LinearMap.congr_fun (p.isIntertwining' g) (v,0) }
    have hf : Function.Bijective f := by
      constructor
      · apply LinearMap.ker_eq_bot.mp
        apply bot_unique
        intro v hv
        have hh : (v,0) ∈ p.toLinearMap.ker := hv
        rw [h] at hh
        exact hh.1
      · intro x
        obtain ⟨⟨v,w⟩,hx⟩ := hp x
        have hz : p (0,w) = 0 := by
          apply LinearMap.mem_ker.mp
          rw [h]
          exact ⟨rfl,Submodule.mem_top⟩
        refine ⟨v,?_⟩
        have he : p (v,w) = p (v,0) + p (0,w) := by
          simpa only [Prod.mk_add_mk,add_zero,zero_add,IntertwiningMap.coe_toLinearMap] using p.map_add (v,0) (0,w)
        rw [hz,add_zero] at he
        exact he.symm.trans hx
    exact Or.inl ⟨(f.ofBijective hf).symm⟩
  · obtain ⟨x,hx⟩ := exists_ne (0 : E)
    obtain ⟨w,rfl⟩ := hp x
    exact (hx (LinearMap.mem_ker.mp (h.symm ▸ Submodule.mem_top))).elim
end Representation.SimpleHeadQuotient
