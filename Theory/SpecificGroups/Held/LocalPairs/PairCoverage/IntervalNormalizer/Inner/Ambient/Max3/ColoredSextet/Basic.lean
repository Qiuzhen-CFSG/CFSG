module

public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.Ambient.Max3.OrbitData

/-!
# Neighbor counts preserved by colored Held graph symmetries

A permutation preserving a finite vertex set and the Held relation preserves
the number of neighbors in that set. An invariant membership predicate then
places the permutation in the actual setwise stabilizer of the max3 sextet.
These elementary transport lemmas support the finite certificates below.
Source context: ATLAS HeG1-p2058B0/max3 and GLS3 Table 5.3p.
-/

public section
open Held.NormalizerGraph
namespace Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.Ambient.Max3.ColoredSextet

@[expose] def neighborCount (s : Finset (Fin 2058)) (x : Fin 2058) : ℕ :=
  (s.filter (Adj x)).card

theorem neighborCount_invariant (s : Finset (Fin 2058)) (σ : Equiv.Perm (Fin 2058))
    (hg : σ ∈ preservingGroup) (hs : ∀ x, σ x ∈ s ↔ x ∈ s) (x : Fin 2058) :
    neighborCount s (σ x) = neighborCount s x := by
  have he : (s.filter (Adj x)).image σ = s.filter (Adj (σ x)) := by
    ext y
    simp only [Finset.mem_image, Finset.mem_filter]
    constructor
    · rintro ⟨z, ⟨hz, hxz⟩, rfl⟩
      exact ⟨(hs z).mpr hz, (hg x z).mpr hxz⟩
    · rintro ⟨hy, hxy⟩
      refine ⟨σ.symm y, ⟨?_, ?_⟩, σ.apply_symm_apply y⟩
      · exact (hs (σ.symm y)).mp (by simpa using hy)
      · exact (hg x (σ.symm y)).mp (by simpa using hxy)
  unfold neighborCount
  rw [← he, Finset.card_image_of_injective _ σ.injective]

theorem stabilizes_of_invariant (σ : Equiv.Perm (Fin 2058))
    (hs : ∀ x, σ x ∈ sextet ↔ x ∈ sextet) :
    σ ∈ sextetPermutationStabilizer := by
  apply mem_sextetPermutationStabilizer_of_image
  ext y
  simp only [Finset.mem_image]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (hs x).mpr hx
  · intro hy
    exact ⟨σ.symm y, (hs _).mp (by simpa using hy), σ.apply_symm_apply y⟩
end Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.Ambient.Max3.ColoredSextet

namespace Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.Ambient.Max3.ColoredSextet

theorem colorClass_invariant (t : Fin 7) (s : Finset (Fin 2058)) (c : ℕ)
    (hc : ∀ x, x ∈ s ↔ orbitSizeLabel t x = c)
    (σ : Equiv.Perm (Fin 2058)) (hσ : σ ∈ coloredGraphGroup t) :
    ∀ x, σ x ∈ s ↔ x ∈ s := by
  intro x
  rw [hc, hc, hσ.2 x]

theorem colored_le_of_neighbor_count (t : Fin 7) (s : Finset (Fin 2058)) (c k : ℕ)
    (hc : ∀ x, x ∈ s ↔ orbitSizeLabel t x = c)
    (hs : ∀ x, x ∈ sextet ↔ orbitSizeLabel t x = 2 ∨
      orbitSizeLabel t x = 4 ∧ neighborCount s x = k) :
    coloredGraphGroup t ≤ sextetPermutationStabilizer := by
  intro σ hσ
  apply stabilizes_of_invariant
  intro x
  rw [hs, hs, hσ.2 x,
    neighborCount_invariant s σ hσ.1 (colorClass_invariant t s c hc σ hσ) x]

end Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.Ambient.Max3.ColoredSextet
