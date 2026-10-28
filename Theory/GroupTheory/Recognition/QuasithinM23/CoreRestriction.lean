module
public import Mathlib.GroupTheory.GroupAction.ConjAct
public import Mathlib.GroupTheory.Subgroup.Centralizer
/-!
# Realizing compatible core automorphisms by conjugation

An automorphism preserving a normal core conjugates its actual action image
to itself. When that image is self-normalizing, its core restriction comes
from an element of the original group. The embeddings are retained pointwise.
-/

public noncomputable section
open Subgroup
namespace Theory.GroupTheory.QuasithinM23

/-- An automorphism compatible with a normal core normalizes its actual
conjugation image. No abstract identification of the image is substituted. -/
theorem core_automorphism_normalizes_action
    {D K : Type*} [Group D] [Group K]
    (i : K →* D) (hi : Function.Injective i) (a : D →* MulAut K)
    (ha : ∀ g u, i (a g u) = g * i u * g⁻¹)
    (α : MulAut D) (c : MulAut K) (hc : ∀ u, α (i u) = i (c u)) :
    c ∈ normalizer (a.range : Set (MulAut K)) := by
  have he (g : D) : c * a g * c⁻¹ = a (α g) := by
    apply MulEquiv.ext
    intro u
    apply hi
    change i (c (a g (c.symm u))) = i (a (α g) u)
    rw [←hc,ha,map_mul,map_mul,map_inv,hc,c.apply_symm_apply,ha]
  apply mem_normalizer_iff.mpr
  intro f
  constructor
  · rintro ⟨g,rfl⟩
    exact ⟨α g,(he g).symm⟩
  · rintro ⟨g,hg⟩
    refine ⟨α.symm g,?_⟩
    have hh := he (α.symm g)
    rw [α.apply_symm_apply,hg] at hh
    exact mul_left_cancel (mul_right_cancel hh)

/-- If the core-action image is self-normalizing, the restriction of a
compatible automorphism is induced by an actual element of the original group. -/
theorem core_automorphism_realized
    {D K : Type*} [Group D] [Group K]
    (i : K →* D) (hi : Function.Injective i) (a : D →* MulAut K)
    (ha : ∀ g u, i (a g u) = g * i u * g⁻¹)
    (hn : normalizer (a.range : Set (MulAut K)) = a.range)
    (α : MulAut D) (c : MulAut K) (hc : ∀ u, α (i u) = i (c u)) :
    ∃ g : D, ∀ u, α (i u) = g * i u * g⁻¹ := by
  have hh := core_automorphism_normalizes_action i hi a ha α c hc
  rw [hn] at hh
  obtain ⟨g,hg⟩ := hh
  exact ⟨g,fun u => by rw [hc,←hg,ha]⟩
end Theory.GroupTheory.QuasithinM23
