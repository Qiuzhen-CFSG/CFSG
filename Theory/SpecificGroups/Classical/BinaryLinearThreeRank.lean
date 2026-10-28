module

public import Theory.SpecificGroups.Classical.BinaryDerivedCubicRank

/-!
# Three-rank in binary linear groups of dimension at least four

Embed Sp₄(2) by adjoining an identity block and reindexing coordinates.
Its actual derived subgroup has three-rank at least two, so the same bound
holds in SL₄(2), SL₅(2), and every larger binary special linear group.
The determinant and injectivity checks are structural, with no enumeration.

Source application: Aschbacher–Smith, combined 1 March 2004 manuscript,
B.4.2 and B.5.1, printed pp.86 and 99–103, and the rank-one reduction in
the proof of 15.3.67, printed p.1154.
-/

open Subgroup Theory.GroupTheory
namespace Theory.SpecificGroups.Classical.BinaryLinearThreeRank
open Matrix
private noncomputable def coordinates (r : ℕ) :
    ((Fin 2 ⊕ Fin 2) ⊕ Fin r) ≃ Fin (4 + r) :=
  (Equiv.sumCongr finSumFinEquiv (Equiv.refl _)).trans finSumFinEquiv

private noncomputable def symplecticIntoLinear (r : ℕ) :
    symplecticGroup (Fin 2) (ZMod 2) →* SpecialLinearGroup (Fin (4 + r)) (ZMod 2) where
  toFun g := ⟨reindex (coordinates r) (coordinates r)
    (fromBlocks g.val 0 0 (1 : Matrix (Fin r) (Fin r) (ZMod 2))), by
      rw [det_reindex_self, det_fromBlocks_zero₂₁, det_one, mul_one]
      exact SymplecticGroup.det_eq_one g.property⟩
  map_one' := by
    apply Subtype.ext
    change reindex (coordinates r) (coordinates r) (fromBlocks 1 0 0 1) = 1
    rw [fromBlocks_one]
    exact (reindexAlgEquiv (ZMod 2) (ZMod 2) (coordinates r)).map_one
  map_mul' g h := by
    apply Subtype.ext
    change reindex (coordinates r) (coordinates r) (fromBlocks (g.val * h.val) 0 0 1) =
      reindex (coordinates r) (coordinates r) (fromBlocks g.val 0 0 1) *
      reindex (coordinates r) (coordinates r) (fromBlocks h.val 0 0 1)
    simp only [reindex_apply]
    rw [submatrix_mul_equiv]
    congr 1
    simp [fromBlocks_multiply]

private theorem symplecticIntoLinear_injective (r : ℕ) :
    Function.Injective (symplecticIntoLinear r) := by
  intro g h he
  have hm := (reindex (coordinates r) (coordinates r)).injective (congrArg Subtype.val he)
  apply Subtype.ext
  exact congrArg (fun M => M.submatrix Sum.inl Sum.inl) hm

/-- The embedded derived symplectic group gives three-rank at least two
in every binary special linear group of dimension at least four. -/
public theorem two_le_primeRank {d : ℕ} (hd : 4 ≤ d) :
    2 ≤ primeRank 3 (SpecialLinearGroup (Fin d) (ZMod 2)) := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hd
  exact (Theory.SpecificGroups.Classical.BinaryDerivedCubicRank.symplectic (F := ZMod 2)).trans
    ((primeRank_le_of_injective 3 _ (commutator _).subtype_injective).trans
      (primeRank_le_of_injective 3 _ (symplecticIntoLinear_injective r)))
end Theory.SpecificGroups.Classical.BinaryLinearThreeRank
