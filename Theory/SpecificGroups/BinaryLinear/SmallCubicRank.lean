module

public import Theory.AtlasPort.ExceptionalIsomorphisms.Order20160A8
public import Theory.SpecificGroups.Alternating.TwoThreeCycles
public import Theory.GroupTheory.QuasithinBasic
public import Mathlib.LinearAlgebra.Matrix.Reindex

/-!
# Three-rank of the binary linear groups in degrees four and five

The actual exceptional isomorphism SL₄(2) ≃ A₈ transports two independent
three-cycles. Extending a matrix by an identity block embeds SL₄(2) into
SL₅(2), so the same lower bound holds there. Only these rank bounds, rather
than further order or simplicity results, are needed to exclude the binary
linear rows of B.5.1 for a component of three-rank one.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, B.5.9,
printed p.107. The exceptional isomorphism's ATLAS attribution and license
are retained in the imported module.
-/

public section
open Matrix
open scoped MatrixGroups
open Theory.GroupTheory

namespace BinaryLinear.SmallCubicRank

/-- The two disjoint three-cycles of A₈, transported through the actual
special-to-projective comparison over the binary field. -/
theorem four : 2 ≤ primeRank 3 SL(4, ZMod 2) := by
  rw [primeRank_equiv 3 (Atlas.Order20160A8.sl4TwoEquivPSL.trans
    Atlas.Comparisons.Exceptional.psl4TwoEquivAlt8)]
  exact alternatingGroup.TwoThreeCycles.two_le_primeRank (by decide)

private def extend : SL(4, ZMod 2) →*
    SpecialLinearGroup (Fin 4 ⊕ Fin 1) (ZMod 2) where
  toFun A := ⟨Matrix.fromBlocks A.val 0 0 1, by simp⟩
  map_one' := by apply Subtype.ext; simp
  map_mul' A B := by
    apply Subtype.ext
    change Matrix.fromBlocks (A.val * B.val) 0 0 (1 : Matrix (Fin 1) (Fin 1) (ZMod 2)) =
      Matrix.fromBlocks A.val 0 0 1 * Matrix.fromBlocks B.val 0 0 1
    simp [Matrix.fromBlocks_multiply]

private def reindex : SpecialLinearGroup (Fin 4 ⊕ Fin 1) (ZMod 2) →* SL(5, ZMod 2) where
  toFun A := ⟨Matrix.reindex finSumFinEquiv finSumFinEquiv A.val, by
    rw [Matrix.det_reindex_self]; exact A.property⟩
  map_one' := by
    apply Subtype.ext
    exact map_one (Matrix.reindexRingEquiv (ZMod 2) finSumFinEquiv)
  map_mul' A B := by
    apply Subtype.ext
    exact map_mul (Matrix.reindexRingEquiv (ZMod 2) finSumFinEquiv) A.val B.val

private theorem extension_injective : Function.Injective (reindex.comp extend) := by
  intro A B h
  apply Subtype.ext
  ext i j
  have he := congrArg (fun C : SL(5, ZMod 2) =>
    C.val (finSumFinEquiv (Sum.inl i : Fin 4 ⊕ Fin 1))
      (finSumFinEquiv (Sum.inl j : Fin 4 ⊕ Fin 1))) h
  change Matrix.fromBlocks A.val 0 0 (1 : Matrix (Fin 1) (Fin 1) (ZMod 2))
      (finSumFinEquiv.symm (finSumFinEquiv (Sum.inl i)))
      (finSumFinEquiv.symm (finSumFinEquiv (Sum.inl j))) =
    Matrix.fromBlocks B.val 0 0 (1 : Matrix (Fin 1) (Fin 1) (ZMod 2))
      (finSumFinEquiv.symm (finSumFinEquiv (Sum.inl i)))
      (finSumFinEquiv.symm (finSumFinEquiv (Sum.inl j))) at he
  simpa using he

/-- The same witness survives extension by the identity on a line. -/
theorem five : 2 ≤ primeRank 3 SL(5, ZMod 2) :=
  four.trans (primeRank_le_of_injective 3 (reindex.comp extend) extension_injective)

/-- Exactly the dimensions used by B.5.1's repeated and natural-dual rows. -/
theorem four_or_five {d : ℕ} (hd : d = 4 ∨ d = 5) :
    2 ≤ primeRank 3 SL(d, ZMod 2) := by
  rcases hd with rfl | rfl
  · exact four
  · exact five

end BinaryLinear.SmallCubicRank
