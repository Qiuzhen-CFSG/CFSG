module

public import Theory.SpecificGroups.Held.LocalPairs.Faithfulness

/-!
# Inner actors and full normalizer transport for Held

The copy of Held in its permutation normalizer induces exactly the inner
automorphisms. Faithfulness therefore detects outer automorphisms by literal
nonmembership in the original permutation subgroup. Full realization also
transports normalizer inclusions in Aut(He) to the concrete permutation action.

These statements construct the maps needed for the local calculations; they
do not assume a catalogue of automorphisms or certify pair coverage.
Sources: the ATLAS HeG1-p2058B0 model; GLS3 Table 5.3p; the retained Held
branch of Aschbacher–Smith, Proposition 1.3.4, printed p.511.
-/

@[expose] public section
open Subgroup
namespace Held.LocalPairs

/-- The original permutation group as a subgroup of its full normalizer. -/
def innerEmbedding : He →* PermutationNormalizer := inclusion le_normalizer

@[simp] theorem innerEmbedding_apply (g : He) :
    (innerEmbedding g).val = representation g := rfl

/-- The embedded original group acts by its actual inner automorphisms. -/
@[simp] theorem normalizerAction_innerEmbedding (g : He) :
    permutationGroup.normalizerMonoidHom (innerEmbedding g) = MulAut.conj g := by
  ext x
  rfl

/-- A normalizing permutation induces an inner automorphism exactly when it
belongs to the original group. This uses the proved trivial centralizer. -/
theorem normalizerAction_mem_inner_iff (a : PermutationNormalizer) :
    permutationGroup.normalizerMonoidHom a ∈ (MulAut.conj : He →* MulAut He).range ↔
      a.val ∈ permutationGroup := by
  constructor
  · rintro ⟨g, hg⟩
    have he : innerEmbedding g = a := normalizerAction_injective
      ((normalizerAction_innerEmbedding g).trans hg)
    rw [← he]
    exact g.property
  · intro ha
    exact ⟨⟨a.val, ha⟩, by ext x; rfl⟩

/-- Full realization transfers normalization, with no innerness restriction. -/
theorem automorphismNormalizer_le_iff
    (hrealize : Function.Surjective permutationGroup.normalizerMonoidHom)
    (U V : Subgroup He) :
    automorphismNormalizer U ≤ automorphismNormalizer V ↔
      ∀ a : PermutationNormalizer,
        a.val ∈ normalizer (U.map representation : Set (Equiv.Perm (Fin 2058))) →
        a.val ∈ normalizer (V.map representation : Set (Equiv.Perm (Fin 2058))) := by
  constructor
  · intro h a ha
    exact (normalizerAction_mem_stabilizer_iff permutationGroup V a).mp
      (h ((normalizerAction_mem_stabilizer_iff permutationGroup U a).mpr ha))
  · intro h b hb
    obtain ⟨a, rfl⟩ := hrealize b
    exact (normalizerAction_mem_stabilizer_iff permutationGroup V a).mpr
      (h a ((normalizerAction_mem_stabilizer_iff permutationGroup U a).mp hb))

end Held.LocalPairs
