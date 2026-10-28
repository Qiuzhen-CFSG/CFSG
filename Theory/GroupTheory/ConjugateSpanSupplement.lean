module
public import Theory.GroupTheory.ConjugateSpanSylow

/-!
# Removing a supplement that preserves the seed

If H normalizes both Z and K, then adjoining H to K does not enlarge
⟨Zᴷ⟩. Conjugation by H preserves the conjugate span by functoriality.
This gives the seed-span reduction in Aschbacher--Smith 15.3.7, where
K is the residual Y and H is the original Sylow subgroup T.
-/

public section
namespace Subgroup
variable {G : Type*} [Group G]

theorem conjugateSpanBy_sup_of_normalizes_seed (Z K H : Subgroup G)
    (hHZ : H ≤ normalizer (Z : Set G)) (hHK : H ≤ normalizer (K : Set G)) :
    conjugateSpanBy Z (K ⊔ H) = conjugateSpanBy Z K := by
  apply le_antisymm ?_ (conjugateSpanBy_mono le_rfl le_sup_left)
  apply conjugateSpanBy_le (le_conjugateSpanBy Z K)
  apply sup_le (le_normalizer_conjugateSpanBy Z K)
  intro h hh
  rw [mem_normalizer_iff_map_conj_eq, map_conjugateSpanBy,
    mem_normalizer_iff_map_conj_eq.mp (hHZ hh),
    mem_normalizer_iff_map_conj_eq.mp (hHK hh)]

end Subgroup
