module

public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreNormalizer.LinearNormalizer.CoreRecognition.ProjectiveData

/-!
# Scalar rigidity of the core projective configuration

A binary matrix commuting with J and fixing each of the 231 specified scalar
lines is one of the three nonzero scalars. It suffices to use the six packed
rows `[5, 10, 33, 49, 83, 20]` and the five pairwise sums along a spanning tree.
Fixation of each sum forces the scalar choices at its endpoints to agree.
The six rows and their J-multiples form a binary basis, as certified by an
explicit left inverse, so this common scalar determines the entire matrix.

The witness data are recorded in `source/projective-certificate.json`; the
original ATLAS matrices and attribution are in `../../LinearModel/source/`.
Every finite identity used here is checked by Lean's kernel. Neither the
candidate-generation script nor an abstract group recognition is a proof input.
-/

namespace Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreLinearModel

private abbrev Row := Fin 12 → ZMod 2
-- Six published lines whose pairs of binary rows form a basis.
private def frame (i : Fin 6) : Row := packedVector (![5, 10, 33, 49, 83, 20] i)
private def frameIndex : Fin 6 → Fin 231 := ![0, 1, 5, 9, 16, 3]

-- A spanning tree whose five sums are also published representatives.
private def edges : Fin 5 → Fin 6 × Fin 6 := ![(0, 1), (0, 2), (0, 3), (0, 4), (1, 5)]
private def edgeIndex : Fin 5 → Fin 231 := ![2, 6, 11, 17, 4]

private def scalarImage (v : Row) : Fin 3 → Row := ![v, Matrix.vecMul v matrixJ, v + Matrix.vecMul v matrixJ]
private def scalarMatrix : Fin 3 → Matrix12 := ![1, matrixJ, 1 + matrixJ]

private def basisRows : Matrix12 := fromRows ![5, 2328, 10, 827, 33, 1226, 49, 2637, 83, 703, 20, 611]
private def basisRowsInv : Matrix12 := fromRows ![1105, 1438, 1104, 1434, 80, 1089, 159, 2821, 3421, 3345, 3006, 2197]

private theorem frame_published : ∀ i, frame i = projectiveVector (frameIndex i) := by
  decide +kernel

private theorem edge_published :
    ∀ e, frame (edges e).1 + frame (edges e).2 = projectiveVector (edgeIndex e) := by
  decide +kernel

-- Distinct scalar choices on an edge cannot map its sum into its own line.
private theorem edges_rigid : ∀ (e : Fin 5) (a b : Fin 3),
    scalarImage (frame (edges e).1) a + scalarImage (frame (edges e).2) b ∈
      scalarLine (frame (edges e).1 + frame (edges e).2) → a = b := by
  simp only [scalarLine, Set.mem_insert_iff, Set.mem_singleton_iff]
  decide +kernel

private theorem basisRows_left_inv : basisRowsInv * basisRows = 1 := by
  decide +kernel

private theorem basisRows_spec : ∀ i : Fin 6,
    basisRows (Fin.ofNat 12 (2 * i.val)) = frame i ∧
      basisRows (Fin.ofNat 12 (2 * i.val + 1)) = Matrix.vecMul (frame i) matrixJ := by
  decide +kernel

private theorem image_eq (v : Row) (a : Fin 3) : scalarImage v a = Matrix.vecMul v (scalarMatrix a) := by
  fin_cases a <;> simp [scalarImage, scalarMatrix, Matrix.vecMul_add]

private theorem image_exists {v w : Row} (h : w ∈ scalarLine v) : ∃ a, w = scalarImage v a := by
  rcases h with h | h | h
  · exact ⟨0, h⟩
  · exact ⟨1, h⟩
  · exact ⟨2, h⟩

private theorem scalar_commutes (a : Fin 3) : Commute (scalarMatrix a) matrixJ := by
  fin_cases a
  · exact Commute.one_left _
  · exact Commute.refl _
  · exact (Commute.one_left _).add_left (Commute.refl _)

private theorem equal_on_frame (u : Matrix12ˣ) (hfix : FixesCoreLines u) :
    ∃ a, ∀ i, Matrix.vecMul (frame i) (u : Matrix12) = Matrix.vecMul (frame i) (scalarMatrix a) := by
  have hv (i : Fin 6) : ∃ a, Matrix.vecMul (frame i) (u : Matrix12) = scalarImage (frame i) a := by
    apply image_exists
    rw [frame_published]
    exact hfix _
  choose s hs using hv
  have he (e : Fin 5) : s (edges e).1 = s (edges e).2 := by
    apply edges_rigid e
    rw [← hs _, ← hs _, ← Matrix.add_vecMul, edge_published]
    exact hfix _
  have hall (i : Fin 6) : s i = s 0 := by
    fin_cases i
    · rfl
    · exact (he 0).symm
    · exact (he 1).symm
    · exact (he 2).symm
    · exact (he 3).symm
    · exact (he 4).symm.trans (he 0).symm
  exact ⟨s 0, fun i => (hs i).trans (by rw [hall, image_eq])⟩

private theorem commuting_frame_ext {M N : Matrix12}
    (hM : Commute M matrixJ) (hN : Commute N matrixJ)
    (h : ∀ i, Matrix.vecMul (frame i) M = Matrix.vecMul (frame i) N) : M = N := by
  have hJ (i : Fin 6) : Matrix.vecMul (Matrix.vecMul (frame i) matrixJ) M =
      Matrix.vecMul (Matrix.vecMul (frame i) matrixJ) N := by
    rw [Matrix.vecMul_vecMul, ← hM.eq, ← Matrix.vecMul_vecMul, h,
      Matrix.vecMul_vecMul, hN.eq, ← Matrix.vecMul_vecMul]
  have hh : basisRows * M = basisRows * N := by
    funext i
    rw [Matrix.mul_apply_eq_vecMul, Matrix.mul_apply_eq_vecMul]
    fin_cases i
    · erw [(basisRows_spec 0).1]
      exact h 0
    · erw [(basisRows_spec 0).2]
      exact hJ 0
    · erw [(basisRows_spec 1).1]
      exact h 1
    · erw [(basisRows_spec 1).2]
      exact hJ 1
    · erw [(basisRows_spec 2).1]
      exact h 2
    · erw [(basisRows_spec 2).2]
      exact hJ 2
    · erw [(basisRows_spec 3).1]
      exact h 3
    · erw [(basisRows_spec 3).2]
      exact hJ 3
    · erw [(basisRows_spec 4).1]
      exact h 4
    · erw [(basisRows_spec 4).2]
      exact hJ 4
    · erw [(basisRows_spec 5).1]
      exact h 5
    · erw [(basisRows_spec 5).2]
      exact hJ 5
  calc
    M = (basisRowsInv * basisRows) * M := by rw [basisRows_left_inv, one_mul]
    _ = (basisRowsInv * basisRows) * N := by rw [mul_assoc, hh, ← mul_assoc]
    _ = N := by rw [basisRows_left_inv, one_mul]

/-- A unit commuting with J and fixing all the specified projective lines is scalar. -/
public theorem projective_fixed_units (u : Matrix12ˣ) (hJ : Commute (u : Matrix12) matrixJ)
    (hfix : FixesCoreLines u) : u = 1 ∨ u = scalarUnit ∨ u = scalarUnit ^ 2 := by
  obtain ⟨a, ha⟩ := equal_on_frame u hfix
  have hu : (u : Matrix12) = scalarMatrix a := commuting_frame_ext hJ (scalar_commutes a) ha
  fin_cases a
  · exact Or.inl (Units.ext hu)
  · exact Or.inr (Or.inr (Units.ext (hu.trans coe_scalarUnit_sq.symm)))
  · exact Or.inr (Or.inl (Units.ext (hu.trans coe_scalarUnit.symm)))

end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreLinearModel
