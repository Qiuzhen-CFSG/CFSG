module

public import Theory.SpecificGroups.PSL3.ExceptionalFourCover.KernelRealization.CentralEmbedding.Elements
public import Theory.SpecificGroups.PSL3.OuterSolvable.Actions

/-!
# Checked words for the diagonal twist of the permutation cover

The second permutation generators are short words in the first generators.
Their matrix coordinates are conjugates by diag(z,1,1), with a scalar z
factor for the second word. Thus they induce the literal diagonal action
on the projective quotient. Every permutation identity and matrix product
is checked by the Lean kernel. Source: Aschbacher--Smith 15.3.38, printed
p.1136; the original ATLAS data and attribution are retained in
`ExceptionalFourCover/KernelRealization/Source/README.md`.
-/

@[expose] public section
namespace Matrix.PSL3.ExceptionalFourCover.KernelModel.DiagonalWords
open scoped MatrixGroups

def diagonal : GL (Fin 3) F :=
  ⟨!![z, 0, 0; 0, 1, 0; 0, 0, 1],
   !![z + 1, 0, 0; 0, 1, 0; 0, 0, 1], by decide +kernel, by decide +kernel⟩

private def inverseX : SL := ⟨!![1, z + 1, 1; 0, 0, z; z, z, z + 1], by decide +kernel⟩
private theorem inverseX_eq : matrixX⁻¹ = inverseX := by
  apply Subtype.ext
  decide +kernel

private def inverseY : SL := ⟨!![z + 1, 1, z + 1; 1, 1, z; z, 1, z + 1], by decide +kernel⟩
private theorem inverseY_eq : matrixY⁻¹ = inverseY := by
  apply Subtype.ext
  decide +kernel

def wordX {H : Type*} [_root_.Group H] (a b : H) : H :=
  1 * b * b * a⁻¹ * b * a⁻¹ * b⁻¹ * a * a * b

theorem map_wordX {H K : Type*} [_root_.Group H] [_root_.Group K]
    (f : H →* K) (a b : H) : f (wordX a b) = wordX (f a) (f b) := by
  simp only [wordX, map_mul, map_inv, map_one]

theorem wordX_perm : wordX x1 y1 = x2 := by
  apply Equiv.ext
  decide +kernel

private def stepX0 : SL := ⟨!![1, 0, 1; 0, z + 1, z; z + 1, 1, z], by decide +kernel⟩
private theorem stepX0_eq : (1 : SL) * matrixY = stepX0 := by
  apply Subtype.ext
  decide +kernel

private def stepX1 : SL := ⟨!![z, 1, z + 1; 1, 0, z; z, 1, z], by decide +kernel⟩
private theorem stepX1_eq : stepX0 * matrixY = stepX1 := by
  apply Subtype.ext
  decide +kernel

private def stepX2 : SL := ⟨!![z + 1, 0, z; z, 0, 0; 1, z, 1], by decide +kernel⟩
private theorem stepX2_eq : stepX1 * inverseX = stepX2 := by
  apply Subtype.ext
  decide +kernel

private def stepX3 : SL := ⟨!![z, z, 0; z, 0, z; z, 0, 0], by decide +kernel⟩
private theorem stepX3_eq : stepX2 * matrixY = stepX3 := by
  apply Subtype.ext
  decide +kernel

private def stepX4 : SL := ⟨!![z, 1, 1; 1, z, z + 1; z, 1, z], by decide +kernel⟩
private theorem stepX4_eq : stepX3 * inverseX = stepX4 := by
  apply Subtype.ext
  decide +kernel

private def stepX5 : SL := ⟨!![z, z, 0; 0, 0, z; z + 1, 1, z], by decide +kernel⟩
private theorem stepX5_eq : stepX4 * inverseY = stepX5 := by
  apply Subtype.ext
  decide +kernel

private def stepX6 : SL := ⟨!![0, z, 1; 0, 1, 0; 1, 0, 1], by decide +kernel⟩
private theorem stepX6_eq : stepX5 * matrixX = stepX6 := by
  apply Subtype.ext
  decide +kernel

private def stepX7 : SL := ⟨!![1, 1, z + 1; z + 1, 1, z; z + 1, z + 1, 1], by decide +kernel⟩
private theorem stepX7_eq : stepX6 * matrixX = stepX7 := by
  apply Subtype.ext
  decide +kernel

private def stepX8 : SL := ⟨!![z + 1, 0, z; z, 1, z; 0, z + 1, 0], by decide +kernel⟩
private theorem stepX8_eq : stepX7 * matrixY = stepX8 := by
  apply Subtype.ext
  decide +kernel

theorem wordX_matrix : wordX matrixX matrixY =
    PSL3.OuterSolvable.linearConjSL F diagonal matrixX := by
  rw [wordX, inverseX_eq, inverseY_eq, stepX0_eq, stepX1_eq, stepX2_eq, stepX3_eq, stepX4_eq, stepX5_eq, stepX6_eq, stepX7_eq, stepX8_eq]
  apply Subtype.ext
  decide +kernel

def wordY {H : Type*} [_root_.Group H] (a b : H) : H :=
  1 * a⁻¹ * b * a * a * b * b * b * b * a * b⁻¹ * a

theorem map_wordY {H K : Type*} [_root_.Group H] [_root_.Group K]
    (f : H →* K) (a b : H) : f (wordY a b) = wordY (f a) (f b) := by
  simp only [wordY, map_mul, map_inv, map_one]

theorem wordY_perm : wordY x1 y1 = y2 := by
  apply Equiv.ext
  decide +kernel

private def stepY0 : SL := ⟨!![1, z + 1, 1; 0, 0, z; z, z, z + 1], by decide +kernel⟩
private theorem stepY0_eq : (1 : SL) * inverseX = stepY0 := by
  apply Subtype.ext
  decide +kernel

private def stepY1 : SL := ⟨!![z, z + 1, z; 1, z, z + 1; 0, z, 0], by decide +kernel⟩
private theorem stepY1_eq : stepY0 * matrixY = stepY1 := by
  apply Subtype.ext
  decide +kernel

private def stepY2 : SL := ⟨!![z + 1, z, z + 1; z, 0, z; 1, z, z + 1], by decide +kernel⟩
private theorem stepY2_eq : stepY1 * matrixX = stepY2 := by
  apply Subtype.ext
  decide +kernel

private def stepY3 : SL := ⟨!![z + 1, 0, 0; 1, 1, z; z, 0, z], by decide +kernel⟩
private theorem stepY3_eq : stepY2 * matrixX = stepY3 := by
  apply Subtype.ext
  decide +kernel

private def stepY4 : SL := ⟨!![z + 1, 0, z + 1; 0, 1, 0; z + 1, z, 1], by decide +kernel⟩
private theorem stepY4_eq : stepY3 * matrixY = stepY4 := by
  apply Subtype.ext
  decide +kernel

private def stepY5 : SL := ⟨!![1, z + 1, z; 0, z + 1, z; 0, 0, z], by decide +kernel⟩
private theorem stepY5_eq : stepY4 * matrixY = stepY5 := by
  apply Subtype.ext
  decide +kernel

private def stepY6 : SL := ⟨!![0, 0, z + 1; 1, 0, z; 1, z, z + 1], by decide +kernel⟩
private theorem stepY6_eq : stepY5 * matrixY = stepY6 := by
  apply Subtype.ext
  decide +kernel

private def stepY7 : SL := ⟨!![z, z + 1, 1; 0, z, z; z + 1, z, z + 1], by decide +kernel⟩
private theorem stepY7_eq : stepY6 * matrixY = stepY7 := by
  apply Subtype.ext
  decide +kernel

private def stepY8 : SL := ⟨!![z + 1, 0, z + 1; 1, z + 1, z + 1; z + 1, 0, 0], by decide +kernel⟩
private theorem stepY8_eq : stepY7 * matrixX = stepY8 := by
  apply Subtype.ext
  decide +kernel

private def stepY9 : SL := ⟨!![z + 1, 0, 0; 1, 1, 0; z, z + 1, z], by decide +kernel⟩
private theorem stepY9_eq : stepY8 * inverseY = stepY9 := by
  apply Subtype.ext
  decide +kernel

private def stepY10 : SL := ⟨!![z, 0, z + 1; 0, 1, z + 1; z + 1, z, z + 1], by decide +kernel⟩
private theorem stepY10_eq : stepY9 * matrixX = stepY10 := by
  apply Subtype.ext
  decide +kernel

theorem wordY_matrix : wordY matrixX matrixY =
    CentralWords.scalarZ * PSL3.OuterSolvable.linearConjSL F diagonal matrixY := by
  rw [wordY, inverseX_eq, inverseY_eq, stepY0_eq, stepY1_eq, stepY2_eq, stepY3_eq, stepY4_eq, stepY5_eq, stepY6_eq, stepY7_eq, stepY8_eq, stepY9_eq, stepY10_eq]
  apply Subtype.ext
  decide +kernel

end Matrix.PSL3.ExceptionalFourCover.KernelModel.DiagonalWords
