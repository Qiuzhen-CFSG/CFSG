module

public import Theory.SpecificGroups.Held.LocalPairs.SylowGeometry.ThreePrimeOvergroups.OrbitCandidates
public import Theory.SpecificGroups.Held.LocalPairs.SylowGeometry.ThreePrimeOvergroups.OrbitTest.Arithmetic

/-!
# Exhaustive degree test for Held orbit unions

Saturation makes membership constant on each of the 24 published label fibers.
The certified fiber sizes and representative neighbor counts turn the hypotheses
into binary linear equations. Their checked case tree leaves precisely the pair
and the two 22-point candidates. This proves the finite degree classification
without group assumptions; `OrbitCandidates` already owns the subsequent profile
exclusion of the two larger candidates.

Sources: the literal ATLAS HeG1-p2058B0 action; GLS3 Table 5.3p; the Held-case
application on Aschbacher–Smith p.725. See `OrbitTest/Source/README.md` for the
reproducible tables and arithmetic certificate.
-/

open scoped BigOperators
namespace Held.LocalPairs.SylowGeometry.ThreePrimeOvergroups
open OrbitTest

/-- Classify all fiber-saturated three-prime subsets with constant induced degree. -/
public theorem regular_candidates (U : Finset (Fin 2058)) (hbase : basepoint ∈ U)
    (hsat : ∀ x ∈ U, ∀ y, orbitLabel x = orbitLabel y → y ∈ U)
    (hthree : ¬ 3 ∣ U.card)
    (hregular : ∀ x ∈ U, neighborCount U x = neighborCount U basepoint) :
    U = basePair ∨ U = candidate67 ∨ U = candidate69 := by
  have h0 : selection U 0 = 1 := by simp only [selection, representative_zero, if_pos hbase]
  have hc : ¬ 3 ∣ ∑ i : Fin 24, weights i * selection U i := by
    rwa [← selection_card U hsat]
  have hr (i : Fin 24) (hi : selection U i = 1) :
      ∑ j : Fin 24, matrix i j * selection U j =
      ∑ j : Fin 24, matrix 0 j * selection U j := by
    have hm : representative i ∈ U := by
      by_contra hn
      simp only [selection, if_neg hn] at hi
      contradiction
    rw [← selection_count U hsat i, ← selection_count U hsat 0, representative_zero]
    exact hregular _ hm
  have hm (x : Fin 2058) :
      x ∈ U ↔ selection U ⟨orbitLabel x, orbitLabel_lt x⟩ = 1 := by
    rw [mem_iff_representative U hsat ⟨orbitLabel x, orbitLabel_lt x⟩ x rfl]
    simp only [selection, ite_eq_left_iff, zero_ne_one, imp_false, not_not]
  rcases regular_vectors (selection U) (selection_le_one U) h0 hc hr with he | he | he
  · left
    ext x
    rw [hm, he, maskVector_one, orbitLabel_eq_zero_iff]
  · right; left
    ext x
    rw [hm, he, maskVector_67, mem_candidate67]
  · right; right
    ext x
    rw [hm, he, maskVector_69, mem_candidate69]

end Held.LocalPairs.SylowGeometry.ThreePrimeOvergroups
