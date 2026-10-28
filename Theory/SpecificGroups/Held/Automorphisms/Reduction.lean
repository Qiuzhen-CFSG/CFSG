module

public import Theory.SpecificGroups.Held.Model.Basic
public import Theory.GroupTheory.NormalizerOuterPGroup

/-!
# Two obligations for the full Held outer automorphism calculation

The carrier here remains the exact ATLAS degree-2058 permutation subgroup.
The normalizer quotient uses its copy inside its permutation normalizer.
To control the full outer group, one must both calculate this quotient and
prove that the normalizer realizes every automorphism. The latter reduces
to simultaneous permutation conjugacy of the two distinguished generators.

Source: GLS3, Table 5.3p, states Out(He) = Z₂. The ATLAS representation is
`HeG1-p2058B0`; the two-generation theorem is `Held.closure_pair`.
This module supplies the reduction, not either missing model calculation.
-/

namespace Held

/-- The quotient of the full permutation normalizer by the concrete Held group.
Normality is relative to the normalizer, not to the full symmetric group. -/
public abbrev PermutationNormalizerQuotient : Type :=
  Subgroup.normalizer (permutationGroup : Set (Equiv.Perm (Fin 2058))) ⧸
    permutationGroup.subgroupOf
      (Subgroup.normalizer (permutationGroup : Set (Equiv.Perm (Fin 2058))))

/-- Simultaneous conjugacy on the actual generating pair realizes every
automorphism in the full permutation normalizer. No presentation injectivity
or classification of the automorphism group is assumed. -/
public theorem normalizer_surjective_of_generator_conjugacy
    (h : ∀ f : MulAut He, ∃ σ : Equiv.Perm (Fin 2058),
      representation (f a) = σ * atlasA * σ⁻¹ ∧
      representation (f b) = σ * atlasB * σ⁻¹) :
    Function.Surjective permutationGroup.normalizerMonoidHom := by
  intro f
  obtain ⟨σ, ha, hb⟩ := h f
  have heq : representation.comp f.toMonoidHom =
      (MulAut.conj σ).toMonoidHom.comp representation := by
    apply MonoidHom.eq_of_eqOn_dense closure_pair
    intro x hx
    rcases hx with rfl | hx
    · exact ha
    · rw [Set.mem_singleton_iff] at hx
      subst x
      exact hb
  have hσ : σ ∈ Subgroup.normalizer
      (permutationGroup : Set (Equiv.Perm (Fin 2058))) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      have hyf := (f ⟨y, hy⟩).property
      change representation (f ⟨y, hy⟩) ∈ permutationGroup at hyf
      have hval := DFunLike.congr_fun heq ⟨y, hy⟩
      change representation (f ⟨y, hy⟩) = (MulAut.conj σ) y at hval
      exact hval ▸ hyf
    · intro hx
      refine ⟨(f.symm ⟨x, hx⟩).val, (f.symm ⟨x, hx⟩).property, ?_⟩
      have hfx := DFunLike.congr_fun heq (f.symm ⟨x, hx⟩)
      simpa [representation] using hfx.symm
  refine ⟨⟨σ, hσ⟩, ?_⟩
  apply MulEquiv.ext
  intro x
  apply representation_injective
  exact (DFunLike.congr_fun heq x).symm

end Held
