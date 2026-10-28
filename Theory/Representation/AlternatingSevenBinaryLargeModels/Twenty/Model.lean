module

public import Theory.Representation.AlternatingSevenBinaryLargeModels.Subspace
public import Theory.SpecificGroups.Thompson.Model.GeneratorCertificates.BinaryMatrix
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.GroupTheory.SpecificGroups.Alternating
import Mathlib.Tactic.FinCases

/-!
# A binary twenty-space in a permutation module

Seven-letter permutations act simultaneously on four ordered letters.
The embedding is symmetric within each pair and under interchange of the pairs.
The unordered configurations with four distinct letters correspond to the
105 partitions of shape 3+2+2. The explicit twenty-dimensional subspace below has zero coordinates on
all other points. Its embedding was located by a finite-field calculation, but
all claims about it are verified by Lean: the reader is a left inverse, the six
adjacent transpositions preserve it, and the two specified even permutations act
by the displayed matrices. A separate density certificate proves absolute
irreducibility. No external computation is used as a proof.

This is the twenty-dimensional candidate needed to exhaust the binary spectrum
in the argument for Aschbacher–Smith K.1.2, printed p.452/PDF p.463.
-/

public section
-- Keep the independent finite checks sequential to bound peak kernel memory.
set_option Elab.async false

open Matrix Thompson.BinaryMatrix
namespace Representation.AlternatingSevenBinaryLargeModels
namespace Twenty

abbrev Vector := Fin 20 → ZMod 2
abbrev Point := (Fin 7 × Fin 7) × (Fin 7 × Fin 7)
abbrev Ambient := Point → ZMod 2

private def pairIndex (a b : ℕ) : ℕ := max a b * (max a b + 1) / 2 + min a b

private theorem pairIndex_comm (a b : ℕ) : pairIndex a b = pairIndex b a := by
  simp only [pairIndex, max_comm, min_comm]

private def pointIndex (p : Point) : ℕ :=
  pairIndex (pairIndex p.1.1.val p.1.2.val) (pairIndex p.2.1.val p.2.2.val)

private def coordinateChunk0 : Array ℕ := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2432, 0, 0]
private def coordinateChunk1 : Array ℕ := #[0, 0, 0, 2440, 0, 0, 0, 0, 0, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
private def coordinateChunk2 : Array ℕ := #[0, 0, 0, 128, 0, 0, 263372, 263276, 0, 0, 0, 0, 0, 65664, 0, 0, 328836, 0, 147464, 0, 0, 0, 0, 65536, 0, 0, 0, 0]
private def coordinateChunk3 : Array ℕ := #[336948, 155656, 0, 0, 0, 0, 0, 0, 65608, 0, 73816, 8192, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
private def coordinateChunk4 : Array ℕ := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2048, 0, 0, 264768, 262754, 0, 0, 262144, 518275, 256161, 0, 0, 0, 0, 0, 71688]
private def coordinateChunk5 : Array ℕ := #[0, 0, 334404, 0, 131072, 0, 262220, 0, 241928, 111368, 0, 0, 0, 0, 69640, 0, 0, 0, 0, 856679, 655360, 0, 0, 1034718, 757768, 0, 154553, 0]
private def coordinateChunk6 : Array ℕ := #[0, 0, 0, 0, 69636, 0, 593925, 524288, 0, 0, 0, 0, 0, 772530, 644100, 138679, 0, 0, 0, 0, 0, 0, 0, 76, 0, 532829, 532736, 0]
private def coordinateChunk7 : Array ℕ := #[532755, 550668, 17934, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
private def coordinateChunk8 : Array ℕ := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 256, 0, 0, 1796, 1542, 0, 0, 1028, 249015, 247985, 0, 0, 512, 248753, 248243, 2, 0]
private def coordinateChunk9 : Array ℕ := #[0, 0, 0, 0, 4352, 0, 0, 5952, 0, 16384, 0, 1024, 0, 53504, 37696, 0, 576, 0, 32768, 50176, 17984, 0, 0, 0, 0, 4096, 0, 0]
private def coordinateChunk10 : Array ℕ := #[0, 0, 540627, 551296, 0, 0, 773426, 577664, 0, 220129, 0, 254689, 43264, 0, 200114, 18003, 0, 0, 0, 0, 0, 4164, 0, 539093, 534912, 0, 0, 0]
private def coordinateChunk11 : Array ℕ := #[0, 0, 772370, 954504, 350603, 0, 0, 254083, 436556, 346590, 0, 17, 0, 0, 0, 0, 0, 0, 4, 0, 524677, 524672, 0, 524707, 918472, 393834, 0, 0]
private def coordinateChunk12 : Array ℕ := #[0, 0, 0, 0, 34, 393804, 393839, 1, 0, 0, 0, 0, 0, 0, 0, 0, 64, 0, 10576, 10496, 0, 10544, 421196, 410732, 0, 32, 410636, 410684]
private def coordinateChunk13 : Array ℕ := #[16, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
private def coordinateChunk14 : Array ℕ := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

private def coordinateChunks : Array (Array ℕ) := #[coordinateChunk0, coordinateChunk1, coordinateChunk2, coordinateChunk3, coordinateChunk4, coordinateChunk5, coordinateChunk6, coordinateChunk7, coordinateChunk8, coordinateChunk9, coordinateChunk10, coordinateChunk11, coordinateChunk12, coordinateChunk13, coordinateChunk14]

private def edgeRow (k : ℕ) : ℕ := (coordinateChunks[k / 28]!)[k % 28]!

private def freeEdges : Fin 20 → Point :=
  ![((3, 5), (4, 6)), ((0, 6), (4, 5)), ((0, 1), (4, 6)), ((0, 1), (2, 3)), ((3, 4), (5, 6)), ((0, 4), (5, 6)), ((0, 1), (5, 6)), ((0, 4), (1, 2)), ((0, 6), (1, 2)), ((0, 6), (1, 5)), ((0, 4), (1, 6)), ((0, 5), (1, 2)), ((0, 1), (2, 6)), ((1, 2), (3, 4)), ((1, 6), (2, 3)), ((1, 6), (2, 5)), ((0, 1), (2, 4)), ((1, 5), (2, 3)), ((0, 5), (1, 4)), ((1, 2), (3, 5))]

private def permute (g : Equiv.Perm (Fin 7)) : Point → Point :=
  fun p => ((g.symm p.1.1, g.symm p.1.2), (g.symm p.2.1, g.symm p.2.2))

private def embeddingMatrix : Matrix Point (Fin 20) (ZMod 2) :=
  fun p j => bit (edgeRow (pointIndex p)) j.val

/-- The symmetric embedding in the permutation module on ordered quadruples. -/
def embed : Vector →ₗ[ZMod 2] Ambient := embeddingMatrix.toLin'

/-- Read the twenty selected configuration coordinates. -/
def read : Ambient →ₗ[ZMod 2] Vector :=
  LinearMap.pi fun i => LinearMap.proj (freeEdges i)

/-- The permutation action on pairs of pairs. -/
def ambient : Representation (ZMod 2) (Equiv.Perm (Fin 7)) Ambient where
  toFun g := {
    toFun := fun v p => v (permute g p)
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }
  map_one' := rfl
  map_mul' _ _ := rfl

private theorem embed_single (j : Fin 20) (p : Point) :
    embed (Pi.single j 1) p = bit (edgeRow (pointIndex p)) j.val := by
  exact congrFun (Matrix.mulVec_single_one embeddingMatrix j) p

private theorem read_embed_rows : ∀ i : Fin 20,
    (edgeRow (pointIndex (freeEdges i))) = 2 ^ i.val := by
  decide +kernel

theorem read_embed : read.comp embed = LinearMap.id := by
  apply LinearMap.toMatrix'.injective
  ext i j
  change embed (Pi.single j 1) (freeEdges i) = (Pi.single j 1 : Vector) i
  rw [embed_single, read_embed_rows]
  simp [bit, Nat.testBit_two_pow, Pi.single_apply, Fin.ext_iff, eq_comm]

private def adjacentRows0 : Array ℕ := #[1, 17984, 4, 8, 16, 410636, 64, 65664, 4352, 576, 1028, 71688, 4096, 73816, 1542, 248753, 65536, 262754, 262220, 593925]
private def adjacentRows1 : Array ℕ := #[1, 2, 524677, 2440, 16, 32, 10576, 128, 256, 248753, 773426, 2048, 4352, 8192, 551296, 43264, 65664, 655360, 518275, 524288]
private def adjacentRows2 : Array ℕ := #[393839, 2, 4, 8, 410684, 32, 64, 263372, 1796, 512, 1024, 264768, 4164, 155656, 16384, 50176, 65608, 131072, 262144, 655360]
private def adjacentRows3 : Array ℕ := #[17, 248243, 4164, 65536, 16, 10544, 64, 2432, 256, 512, 5952, 2048, 4096, 8192, 53504, 32768, 8, 241928, 264768, 532736]
private def adjacentRows4 : Array ℕ := #[16, 2, 64, 8, 1, 34, 4, 2048, 256, 1028, 576, 128, 4096, 524288, 16384, 53504, 69640, 147464, 262220, 8192]
private def adjacentRows5 : Array ℕ := #[17, 34, 76, 8, 16, 32, 64, 128, 2048, 576, 262220, 256, 69640, 8192, 131072, 43264, 65536, 16384, 1028, 534912]

private def adjacentMatrices : Fin 6 → Array ℕ :=
  ![adjacentRows0, adjacentRows1, adjacentRows2, adjacentRows3, adjacentRows4, adjacentRows5]

private theorem adjacentMatrices_spec : ∀ i : Fin 6, ∀ k : Fin 20,
    (adjacentMatrices i)[k.val]! =
      (edgeRow (pointIndex (permute (Equiv.swap i.castSucc i.succ) (freeEdges k)))) := by
  decide +kernel

private def permutedChunk0_0 : Array ℕ := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2440, 0, 0]
private def permutedChunk0_1 : Array ℕ := #[0, 0, 0, 2432, 0, 0, 0, 0, 0, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
private def permutedChunk0_2 : Array ℕ := #[0, 0, 0, 65664, 0, 0, 328836, 147464, 0, 0, 0, 0, 0, 128, 0, 0, 263372, 0, 263276, 0, 0, 0, 0, 65536, 0, 0, 0, 0]
private def permutedChunk0_3 : Array ℕ := #[155656, 336948, 0, 0, 0, 0, 0, 0, 65608, 0, 8192, 73816, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
private def permutedChunk0_4 : Array ℕ := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 71688, 0, 0, 334404, 131072, 0, 0, 262220, 241928, 111368, 0, 0, 0, 0, 0, 2048]
private def permutedChunk0_5 : Array ℕ := #[0, 0, 264768, 0, 262754, 0, 262144, 0, 518275, 256161, 0, 0, 0, 0, 69640, 0, 0, 0, 0, 655360, 856679, 0, 0, 757768, 1034718, 0, 154553, 0]
private def permutedChunk0_6 : Array ℕ := #[0, 0, 0, 0, 69636, 0, 524288, 593925, 0, 0, 0, 0, 0, 644100, 772530, 138679, 0, 0, 0, 0, 0, 0, 0, 76, 0, 532736, 532829, 0]
private def permutedChunk0_7 : Array ℕ := #[550668, 532755, 17934, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
private def permutedChunk0_8 : Array ℕ := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4352, 0, 0, 5952, 16384, 0, 0, 1024, 53504, 37696, 0, 0, 576, 32768, 50176, 17984, 0]
private def permutedChunk0_9 : Array ℕ := #[0, 0, 0, 0, 256, 0, 0, 1796, 0, 1542, 0, 1028, 0, 249015, 247985, 0, 512, 0, 248753, 248243, 2, 0, 0, 0, 0, 4096, 0, 0]
private def permutedChunk0_10 : Array ℕ := #[0, 0, 551296, 540627, 0, 0, 577664, 773426, 0, 220129, 0, 43264, 254689, 0, 200114, 18003, 0, 0, 0, 0, 0, 4164, 0, 534912, 539093, 0, 0, 0]
private def permutedChunk0_11 : Array ℕ := #[0, 0, 954504, 772370, 350603, 0, 0, 436556, 254083, 346590, 0, 17, 0, 0, 0, 0, 0, 0, 4, 0, 524672, 524677, 0, 918472, 524707, 393834, 0, 0]
private def permutedChunk0_12 : Array ℕ := #[0, 0, 0, 0, 393804, 34, 393839, 1, 0, 0, 0, 0, 0, 0, 0, 0, 64, 0, 10496, 10576, 0, 421196, 10544, 410732, 0, 410636, 32, 410684]
private def permutedChunk0_13 : Array ℕ := #[16, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
private def permutedChunk0_14 : Array ℕ := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
private def permutedChunks0 : Array (Array ℕ) := #[permutedChunk0_0, permutedChunk0_1, permutedChunk0_2, permutedChunk0_3, permutedChunk0_4, permutedChunk0_5, permutedChunk0_6, permutedChunk0_7, permutedChunk0_8, permutedChunk0_9, permutedChunk0_10, permutedChunk0_11, permutedChunk0_12, permutedChunk0_13, permutedChunk0_14]

private def permutedChunk1_0 : Array ℕ := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2432, 0, 0]
private def permutedChunk1_1 : Array ℕ := #[0, 0, 0, 8, 0, 0, 0, 0, 0, 2440, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
private def permutedChunk1_2 : Array ℕ := #[0, 0, 0, 128, 0, 0, 263276, 263372, 0, 0, 0, 0, 0, 65536, 0, 0, 336948, 0, 155656, 0, 0, 0, 0, 65664, 0, 0, 0, 0]
private def permutedChunk1_3 : Array ℕ := #[328836, 147464, 0, 0, 0, 0, 0, 0, 73816, 0, 65608, 8192, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
private def permutedChunk1_4 : Array ℕ := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2048, 0, 0, 262754, 264768, 0, 0, 518275, 262144, 256161, 0, 0, 0, 0, 0, 69640]
private def permutedChunk1_5 : Array ℕ := #[0, 0, 856679, 0, 655360, 0, 1034718, 0, 757768, 154553, 0, 0, 0, 0, 71688, 0, 0, 0, 0, 334404, 131072, 0, 0, 262220, 241928, 0, 111368, 0]
private def permutedChunk1_6 : Array ℕ := #[0, 0, 0, 0, 593925, 0, 69636, 524288, 0, 0, 0, 0, 0, 772530, 138679, 644100, 0, 0, 0, 0, 0, 0, 0, 532829, 0, 76, 532736, 0]
private def permutedChunk1_7 : Array ℕ := #[532755, 17934, 550668, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
private def permutedChunk1_8 : Array ℕ := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 256, 0, 0, 1542, 1796, 0, 0, 249015, 1028, 247985, 0, 0, 248753, 512, 248243, 2, 0]
private def permutedChunk1_9 : Array ℕ := #[0, 0, 0, 0, 4096, 0, 0, 540627, 0, 551296, 0, 773426, 0, 577664, 220129, 0, 254689, 0, 43264, 200114, 18003, 0, 0, 0, 0, 4352, 0, 0]
private def permutedChunk1_10 : Array ℕ := #[0, 0, 5952, 16384, 0, 0, 1024, 53504, 0, 37696, 0, 576, 32768, 0, 50176, 17984, 0, 0, 0, 0, 0, 539093, 0, 4164, 534912, 0, 0, 0]
private def permutedChunk1_11 : Array ℕ := #[0, 0, 772370, 350603, 954504, 0, 0, 254083, 346590, 436556, 0, 17, 0, 0, 0, 0, 0, 0, 524677, 0, 4, 524672, 0, 524707, 393834, 918472, 0, 0]
private def permutedChunk1_12 : Array ℕ := #[0, 0, 0, 0, 34, 393839, 393804, 1, 0, 0, 0, 0, 0, 0, 0, 0, 10576, 0, 64, 10496, 0, 10544, 410732, 421196, 0, 32, 410684, 410636]
private def permutedChunk1_13 : Array ℕ := #[16, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
private def permutedChunk1_14 : Array ℕ := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
private def permutedChunks1 : Array (Array ℕ) := #[permutedChunk1_0, permutedChunk1_1, permutedChunk1_2, permutedChunk1_3, permutedChunk1_4, permutedChunk1_5, permutedChunk1_6, permutedChunk1_7, permutedChunk1_8, permutedChunk1_9, permutedChunk1_10, permutedChunk1_11, permutedChunk1_12, permutedChunk1_13, permutedChunk1_14]

private def permutedChunk2_0 : Array ℕ := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2440, 0, 0]
private def permutedChunk2_1 : Array ℕ := #[0, 0, 0, 2432, 0, 0, 0, 0, 0, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
private def permutedChunk2_2 : Array ℕ := #[0, 0, 0, 263372, 0, 0, 128, 263276, 0, 0, 0, 0, 0, 328836, 0, 0, 65664, 0, 147464, 0, 0, 0, 0, 65608, 0, 0, 0, 0]
private def permutedChunk2_3 : Array ℕ := #[73816, 8192, 0, 0, 0, 0, 0, 0, 65536, 0, 336948, 155656, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
private def permutedChunk2_4 : Array ℕ := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 264768, 0, 0, 2048, 262754, 0, 0, 262144, 256161, 518275, 0, 0, 0, 0, 0, 334404]
private def permutedChunk2_5 : Array ℕ := #[0, 0, 71688, 0, 131072, 0, 262220, 0, 111368, 241928, 0, 0, 0, 0, 69636, 0, 0, 0, 0, 593925, 524288, 0, 0, 772530, 644100, 0, 138679, 0]
private def permutedChunk2_6 : Array ℕ := #[0, 0, 0, 0, 69640, 0, 856679, 655360, 0, 0, 0, 0, 0, 1034718, 757768, 154553, 0, 0, 0, 0, 0, 0, 0, 76, 0, 532755, 550668, 0]
private def permutedChunk2_7 : Array ℕ := #[532829, 532736, 17934, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
private def permutedChunk2_8 : Array ℕ := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1796, 0, 0, 256, 1542, 0, 0, 1028, 247985, 249015, 0, 0, 512, 248243, 248753, 2, 0]
private def permutedChunk2_9 : Array ℕ := #[0, 0, 0, 0, 5952, 0, 0, 4352, 0, 16384, 0, 1024, 0, 37696, 53504, 0, 576, 0, 50176, 32768, 17984, 0, 0, 0, 0, 4164, 0, 0]
private def permutedChunk2_10 : Array ℕ := #[0, 0, 539093, 534912, 0, 0, 772370, 954504, 0, 350603, 0, 254083, 436556, 0, 346590, 17, 0, 0, 0, 0, 0, 4096, 0, 540627, 551296, 0, 0, 0]
private def permutedChunk2_11 : Array ℕ := #[0, 0, 773426, 577664, 220129, 0, 0, 254689, 43264, 200114, 0, 18003, 0, 0, 0, 0, 0, 0, 4, 0, 524707, 918472, 0, 524677, 524672, 393834, 0, 0]
private def permutedChunk2_12 : Array ℕ := #[0, 0, 0, 0, 34, 393804, 1, 393839, 0, 0, 0, 0, 0, 0, 0, 0, 64, 0, 10544, 421196, 0, 10576, 10496, 410732, 0, 32, 410636, 16]
private def permutedChunk2_13 : Array ℕ := #[410684, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
private def permutedChunk2_14 : Array ℕ := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
private def permutedChunks2 : Array (Array ℕ) := #[permutedChunk2_0, permutedChunk2_1, permutedChunk2_2, permutedChunk2_3, permutedChunk2_4, permutedChunk2_5, permutedChunk2_6, permutedChunk2_7, permutedChunk2_8, permutedChunk2_9, permutedChunk2_10, permutedChunk2_11, permutedChunk2_12, permutedChunk2_13, permutedChunk2_14]

private def permutedChunk3_0 : Array ℕ := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 128, 0, 0]
private def permutedChunk3_1 : Array ℕ := #[0, 0, 0, 65664, 0, 0, 0, 0, 0, 65536, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
private def permutedChunk3_2 : Array ℕ := #[0, 0, 0, 2432, 0, 0, 328836, 336948, 0, 0, 0, 0, 0, 2440, 0, 0, 263372, 0, 155656, 0, 0, 0, 0, 8, 0, 0, 0, 0]
private def permutedChunk3_3 : Array ℕ := #[263276, 147464, 0, 0, 0, 0, 0, 0, 65608, 0, 73816, 8192, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
private def permutedChunk3_4 : Array ℕ := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2048, 0, 0, 262144, 518275, 0, 0, 264768, 262754, 256161, 0, 0, 0, 0, 0, 71688]
private def permutedChunk3_5 : Array ℕ := #[0, 0, 262220, 0, 241928, 0, 334404, 0, 131072, 111368, 0, 0, 0, 0, 69640, 0, 0, 0, 0, 1034718, 757768, 0, 0, 856679, 655360, 0, 154553, 0]
private def permutedChunk3_6 : Array ℕ := #[0, 0, 0, 0, 76, 0, 532829, 532736, 0, 0, 0, 0, 0, 532755, 550668, 17934, 0, 0, 0, 0, 0, 0, 0, 69636, 0, 593925, 524288, 0]
private def permutedChunk3_7 : Array ℕ := #[772530, 644100, 138679, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
private def permutedChunk3_8 : Array ℕ := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 256, 0, 0, 1028, 249015, 0, 0, 1796, 1542, 247985, 0, 0, 512, 248753, 2, 248243, 0]
private def permutedChunk3_9 : Array ℕ := #[0, 0, 0, 0, 4352, 0, 0, 1024, 0, 53504, 0, 5952, 0, 16384, 37696, 0, 576, 0, 32768, 17984, 50176, 0, 0, 0, 0, 4096, 0, 0]
private def permutedChunk3_10 : Array ℕ := #[0, 0, 773426, 577664, 0, 0, 540627, 551296, 0, 220129, 0, 254689, 43264, 0, 18003, 200114, 0, 0, 0, 0, 0, 4, 0, 524677, 524672, 0, 0, 0]
private def permutedChunk3_11 : Array ℕ := #[0, 0, 524707, 918472, 393834, 0, 0, 34, 393804, 393839, 0, 1, 0, 0, 0, 0, 0, 0, 4164, 0, 539093, 534912, 0, 772370, 954504, 350603, 0, 0]
private def permutedChunk3_12 : Array ℕ := #[0, 0, 0, 0, 254083, 436556, 346590, 17, 0, 0, 0, 0, 0, 0, 0, 0, 64, 0, 10576, 10496, 0, 32, 410636, 410684, 0, 10544, 421196, 410732]
private def permutedChunk3_13 : Array ℕ := #[16, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
private def permutedChunk3_14 : Array ℕ := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
private def permutedChunks3 : Array (Array ℕ) := #[permutedChunk3_0, permutedChunk3_1, permutedChunk3_2, permutedChunk3_3, permutedChunk3_4, permutedChunk3_5, permutedChunk3_6, permutedChunk3_7, permutedChunk3_8, permutedChunk3_9, permutedChunk3_10, permutedChunk3_11, permutedChunk3_12, permutedChunk3_13, permutedChunk3_14]

private def permutedChunk4_0 : Array ℕ := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2432, 0, 0]
private def permutedChunk4_1 : Array ℕ := #[0, 0, 0, 2440, 0, 0, 0, 0, 0, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
private def permutedChunk4_2 : Array ℕ := #[0, 0, 0, 2048, 0, 0, 264768, 262754, 0, 0, 0, 0, 0, 71688, 0, 0, 334404, 0, 131072, 0, 0, 0, 0, 69640, 0, 0, 0, 0]
private def permutedChunk4_3 : Array ℕ := #[856679, 655360, 0, 0, 0, 0, 0, 0, 69636, 0, 593925, 524288, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
private def permutedChunk4_4 : Array ℕ := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 128, 0, 0, 263372, 263276, 0, 0, 262220, 1034718, 772530, 0, 0, 0, 0, 0, 65664]
private def permutedChunk4_5 : Array ℕ := #[0, 0, 328836, 0, 147464, 0, 262144, 0, 757768, 644100, 0, 0, 0, 0, 65536, 0, 0, 0, 0, 336948, 155656, 0, 0, 518275, 241928, 0, 138679, 0]
private def permutedChunk4_6 : Array ℕ := #[0, 0, 0, 0, 65608, 0, 73816, 8192, 0, 0, 0, 0, 0, 256161, 111368, 154553, 0, 0, 0, 0, 0, 0, 0, 76, 0, 532829, 532736, 0]
private def permutedChunk4_7 : Array ℕ := #[532755, 550668, 17934, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
private def permutedChunk4_8 : Array ℕ := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 256, 0, 0, 1796, 1542, 0, 0, 512, 248753, 248243, 0, 0, 1028, 249015, 247985, 2, 0]
private def permutedChunk4_9 : Array ℕ := #[0, 0, 0, 0, 4352, 0, 0, 5952, 0, 16384, 0, 576, 0, 32768, 50176, 0, 1024, 0, 53504, 37696, 17984, 0, 0, 0, 0, 4096, 0, 0]
private def permutedChunk4_10 : Array ℕ := #[0, 0, 540627, 551296, 0, 0, 254689, 43264, 0, 200114, 0, 773426, 577664, 0, 220129, 18003, 0, 0, 0, 0, 0, 4164, 0, 539093, 534912, 0, 0, 0]
private def permutedChunk4_11 : Array ℕ := #[0, 0, 254083, 436556, 346590, 0, 0, 772370, 954504, 350603, 0, 17, 0, 0, 0, 0, 0, 0, 64, 0, 10576, 10496, 0, 10544, 421196, 410732, 0, 0]
private def permutedChunk4_12 : Array ℕ := #[0, 0, 0, 0, 32, 410636, 410684, 16, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 524677, 524672, 0, 524707, 918472, 393834, 0, 34, 393804, 393839]
private def permutedChunk4_13 : Array ℕ := #[1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
private def permutedChunk4_14 : Array ℕ := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
private def permutedChunks4 : Array (Array ℕ) := #[permutedChunk4_0, permutedChunk4_1, permutedChunk4_2, permutedChunk4_3, permutedChunk4_4, permutedChunk4_5, permutedChunk4_6, permutedChunk4_7, permutedChunk4_8, permutedChunk4_9, permutedChunk4_10, permutedChunk4_11, permutedChunk4_12, permutedChunk4_13, permutedChunk4_14]

private def permutedChunk5_0 : Array ℕ := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2432, 0, 0]
private def permutedChunk5_1 : Array ℕ := #[0, 0, 0, 2440, 0, 0, 0, 0, 0, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
private def permutedChunk5_2 : Array ℕ := #[0, 0, 0, 128, 0, 0, 263372, 263276, 0, 0, 0, 0, 0, 65664, 0, 0, 328836, 0, 147464, 0, 0, 0, 0, 65536, 0, 0, 0, 0]
private def permutedChunk5_3 : Array ℕ := #[336948, 155656, 0, 0, 0, 0, 0, 0, 65608, 0, 73816, 8192, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
private def permutedChunk5_4 : Array ℕ := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 256, 0, 0, 1796, 1542, 0, 0, 1028, 249015, 247985, 0, 0, 0, 0, 0, 4352]
private def permutedChunk5_5 : Array ℕ := #[0, 0, 5952, 0, 16384, 0, 1024, 0, 53504, 37696, 0, 0, 0, 0, 4096, 0, 0, 0, 0, 540627, 551296, 0, 0, 773426, 577664, 0, 220129, 0]
private def permutedChunk5_6 : Array ℕ := #[0, 0, 0, 0, 4164, 0, 539093, 534912, 0, 0, 0, 0, 0, 772370, 954504, 350603, 0, 0, 0, 0, 0, 0, 0, 4, 0, 524677, 524672, 0]
private def permutedChunk5_7 : Array ℕ := #[524707, 918472, 393834, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
private def permutedChunk5_8 : Array ℕ := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2048, 0, 0, 264768, 262754, 0, 0, 262144, 518275, 256161, 0, 0, 576, 254689, 254083, 34, 0]
private def permutedChunk5_9 : Array ℕ := #[0, 0, 0, 0, 71688, 0, 0, 334404, 0, 131072, 0, 262220, 0, 241928, 111368, 0, 512, 0, 43264, 436556, 393804, 0, 0, 0, 0, 69640, 0, 0]
private def permutedChunk5_10 : Array ℕ := #[0, 0, 856679, 655360, 0, 0, 1034718, 757768, 0, 154553, 0, 248753, 32768, 0, 346590, 393839, 0, 0, 0, 0, 0, 69636, 0, 593925, 524288, 0, 0, 0]
private def permutedChunk5_11 : Array ℕ := #[0, 0, 772530, 644100, 138679, 0, 0, 248243, 50176, 200114, 0, 1, 0, 0, 0, 0, 0, 0, 76, 0, 532829, 532736, 0, 532755, 550668, 17934, 0, 0]
private def permutedChunk5_12 : Array ℕ := #[0, 0, 0, 0, 2, 17984, 18003, 17, 0, 0, 0, 0, 0, 0, 0, 0, 64, 0, 10576, 10496, 0, 10544, 421196, 410732, 0, 32, 410636, 410684]
private def permutedChunk5_13 : Array ℕ := #[16, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
private def permutedChunk5_14 : Array ℕ := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
private def permutedChunks5 : Array (Array ℕ) := #[permutedChunk5_0, permutedChunk5_1, permutedChunk5_2, permutedChunk5_3, permutedChunk5_4, permutedChunk5_5, permutedChunk5_6, permutedChunk5_7, permutedChunk5_8, permutedChunk5_9, permutedChunk5_10, permutedChunk5_11, permutedChunk5_12, permutedChunk5_13, permutedChunk5_14]

private def permutedChunks : Fin 6 → Array (Array ℕ) :=
  ![permutedChunks0, permutedChunks1, permutedChunks2, permutedChunks3, permutedChunks4, permutedChunks5]

private def permutedRow (i : Fin 6) (k : ℕ) : ℕ :=
  ((permutedChunks i)[k / 28]!)[k % 28]!

private def edgePermutation : Fin 6 → Array ℕ :=
  ![#[2, 1, 0, 4, 3, 5, 7, 6, 8, 9, 11, 10, 12, 13, 14, 16, 15, 17, 18, 19, 20, 22, 21, 23, 24, 25, 26, 27],
    #[0, 3, 5, 1, 4, 2, 6, 8, 7, 9, 10, 12, 11, 13, 14, 15, 17, 16, 18, 19, 20, 21, 23, 22, 24, 25, 26, 27],
    #[0, 1, 2, 6, 7, 9, 3, 4, 8, 5, 10, 11, 13, 12, 14, 15, 16, 18, 17, 19, 20, 21, 22, 24, 23, 25, 26, 27],
    #[0, 1, 2, 3, 4, 5, 10, 11, 12, 14, 6, 7, 8, 13, 9, 15, 16, 17, 19, 18, 20, 21, 22, 23, 25, 24, 26, 27],
    #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 15, 16, 17, 18, 20, 10, 11, 12, 13, 19, 14, 21, 22, 23, 24, 26, 25, 27],
    #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 21, 22, 23, 24, 25, 27, 15, 16, 17, 18, 19, 26, 20]]

private theorem edgeIndex_lt : ∀ a b : Fin 7, pairIndex a.val b.val < 28 := by
  decide +kernel

private theorem pairIndex_lt : ∀ a b : Fin 28, pairIndex a.val b.val < 406 := by
  decide +kernel

private theorem pointIndex_lt (p : Point) : pointIndex p < 406 :=
  pairIndex_lt ⟨pairIndex p.1.1.val p.1.2.val, edgeIndex_lt _ _⟩
    ⟨pairIndex p.2.1.val p.2.2.val, edgeIndex_lt _ _⟩

private theorem edgePermutation_spec : ∀ i : Fin 6, ∀ a b : Fin 7,
    pairIndex ((Equiv.swap i.castSucc i.succ).symm a).val
      ((Equiv.swap i.castSucc i.succ).symm b).val =
        (edgePermutation i)[pairIndex a.val b.val]! := by
  decide +kernel

private theorem rowProduct_zero (b : Array ℕ) (n : ℕ) : rowProduct 0 b n = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [rowProduct, ih]

set_option maxRecDepth 4000 in
private theorem row_products_0 : ∀ k : Fin 406,
    if edgeRow k.val = 0 then permutedRow 0 k.val = 0 else
      rowProduct (edgeRow k.val) (adjacentMatrices 0) 20 = permutedRow 0 k.val := by
  decide +kernel

set_option maxRecDepth 4000 in
private theorem row_products_1 : ∀ k : Fin 406,
    if edgeRow k.val = 0 then permutedRow 1 k.val = 0 else
      rowProduct (edgeRow k.val) (adjacentMatrices 1) 20 = permutedRow 1 k.val := by
  decide +kernel

set_option maxRecDepth 4000 in
private theorem row_products_2 : ∀ k : Fin 406,
    if edgeRow k.val = 0 then permutedRow 2 k.val = 0 else
      rowProduct (edgeRow k.val) (adjacentMatrices 2) 20 = permutedRow 2 k.val := by
  decide +kernel

set_option maxRecDepth 4000 in
private theorem row_products_3 : ∀ k : Fin 406,
    if edgeRow k.val = 0 then permutedRow 3 k.val = 0 else
      rowProduct (edgeRow k.val) (adjacentMatrices 3) 20 = permutedRow 3 k.val := by
  decide +kernel

set_option maxRecDepth 4000 in
private theorem row_products_4 : ∀ k : Fin 406,
    if edgeRow k.val = 0 then permutedRow 4 k.val = 0 else
      rowProduct (edgeRow k.val) (adjacentMatrices 4) 20 = permutedRow 4 k.val := by
  decide +kernel

set_option maxRecDepth 4000 in
private theorem row_products_5 : ∀ k : Fin 406,
    if edgeRow k.val = 0 then permutedRow 5 k.val = 0 else
      rowProduct (edgeRow k.val) (adjacentMatrices 5) 20 = permutedRow 5 k.val := by
  decide +kernel

private theorem row_products (i : Fin 6) (k : Fin 406) :
    rowProduct (edgeRow k.val) (adjacentMatrices i) 20 = permutedRow i k.val := by
  have h : if edgeRow k.val = 0 then permutedRow i k.val = 0 else
      rowProduct (edgeRow k.val) (adjacentMatrices i) 20 = permutedRow i k.val := by
    fin_cases i
    · exact row_products_0 k
    · exact row_products_1 k
    · exact row_products_2 k
    · exact row_products_3 k
    · exact row_products_4 k
    · exact row_products_5 k
  by_cases hk : edgeRow k.val = 0
  · simp only [hk, if_true] at h
    rw [hk, rowProduct_zero, h]
  · simpa only [if_neg hk] using h

set_option maxRecDepth 4000 in
private theorem permutedRows_checked_0 : ∀ a b : Fin 28, a ≤ b →
    permutedRow 0 (pairIndex a.val b.val) =
      (edgeRow (pairIndex (edgePermutation 0)[a.val]! (edgePermutation 0)[b.val]!)) := by
  decide +kernel

set_option maxRecDepth 4000 in
private theorem permutedRows_checked_1 : ∀ a b : Fin 28, a ≤ b →
    permutedRow 1 (pairIndex a.val b.val) =
      (edgeRow (pairIndex (edgePermutation 1)[a.val]! (edgePermutation 1)[b.val]!)) := by
  decide +kernel

set_option maxRecDepth 4000 in
private theorem permutedRows_checked_2 : ∀ a b : Fin 28, a ≤ b →
    permutedRow 2 (pairIndex a.val b.val) =
      (edgeRow (pairIndex (edgePermutation 2)[a.val]! (edgePermutation 2)[b.val]!)) := by
  decide +kernel

set_option maxRecDepth 4000 in
private theorem permutedRows_checked_3 : ∀ a b : Fin 28, a ≤ b →
    permutedRow 3 (pairIndex a.val b.val) =
      (edgeRow (pairIndex (edgePermutation 3)[a.val]! (edgePermutation 3)[b.val]!)) := by
  decide +kernel

set_option maxRecDepth 4000 in
private theorem permutedRows_checked_4 : ∀ a b : Fin 28, a ≤ b →
    permutedRow 4 (pairIndex a.val b.val) =
      (edgeRow (pairIndex (edgePermutation 4)[a.val]! (edgePermutation 4)[b.val]!)) := by
  decide +kernel

set_option maxRecDepth 4000 in
private theorem permutedRows_checked_5 : ∀ a b : Fin 28, a ≤ b →
    permutedRow 5 (pairIndex a.val b.val) =
      (edgeRow (pairIndex (edgePermutation 5)[a.val]! (edgePermutation 5)[b.val]!)) := by
  decide +kernel

private theorem permutedRows_checked (i : Fin 6) (a b : Fin 28) :
    permutedRow i (pairIndex a.val b.val) =
      (edgeRow (pairIndex (edgePermutation i)[a.val]! (edgePermutation i)[b.val]!)) := by
  have ordered (x y : Fin 28) (hxy : x ≤ y) :
      permutedRow i (pairIndex x.val y.val) =
        (edgeRow (pairIndex (edgePermutation i)[x.val]! (edgePermutation i)[y.val]!)) := by
    fin_cases i
    · exact permutedRows_checked_0 x y hxy
    · exact permutedRows_checked_1 x y hxy
    · exact permutedRows_checked_2 x y hxy
    · exact permutedRows_checked_3 x y hxy
    · exact permutedRows_checked_4 x y hxy
    · exact permutedRows_checked_5 x y hxy
  by_cases hab : a ≤ b
  · exact ordered a b hab
  · rw [pairIndex_comm a.val b.val,
      pairIndex_comm (edgePermutation i)[a.val]! (edgePermutation i)[b.val]!]
    exact ordered b a (le_of_not_ge hab)

private theorem permutedRows_spec (i : Fin 6) (p : Point) :
    permutedRow i (pointIndex p) =
      (edgeRow (pointIndex (permute (Equiv.swap i.castSucc i.succ) p))) := by
  change permutedRow i (pointIndex p) =
    (edgeRow (pairIndex
      (pairIndex ((Equiv.swap i.castSucc i.succ).symm p.1.1).val
        ((Equiv.swap i.castSucc i.succ).symm p.1.2).val)
      (pairIndex ((Equiv.swap i.castSucc i.succ).symm p.2.1).val
        ((Equiv.swap i.castSucc i.succ).symm p.2.2).val)))
  rw [edgePermutation_spec, edgePermutation_spec]
  exact permutedRows_checked i
    ⟨pairIndex p.1.1.val p.1.2.val, edgeIndex_lt _ _⟩
    ⟨pairIndex p.2.1.val p.2.2.val, edgeIndex_lt _ _⟩

private theorem adjacent_rows (i : Fin 6) (p : Point) :
    rowProduct (edgeRow (pointIndex p)) (adjacentMatrices i) 20 =
      (edgeRow (pointIndex (permute (Equiv.swap i.castSucc i.succ) p))) := by
  rw [row_products i ⟨pointIndex p, pointIndex_lt p⟩, permutedRows_spec]

private theorem adjacent_basis (i : Fin 6) (j : Fin 20) :
    embed (read (ambient (Equiv.swap i.castSucc i.succ) (embed (Pi.single j 1)))) =
      ambient (Equiv.swap i.castSucc i.succ) (embed (Pi.single j 1)) := by
  ext p
  have h := congrArg (fun x => bit x j.val) (adjacent_rows i p)
  rw [bit_rowProduct, ← Fin.sum_univ_eq_sum_range] at h
  change (∑ k : Fin 20, bit (edgeRow (pointIndex p)) k.val *
    embed (Pi.single j 1) (permute (Equiv.swap i.castSucc i.succ) (freeEdges k))) =
    embed (Pi.single j 1) (permute (Equiv.swap i.castSucc i.succ) p)
  simp only [embed_single]
  simpa only [adjacentMatrices_spec] using h

theorem invariant (g : Equiv.Perm (Fin 7)) :
    embed.comp (read.comp ((ambient g).comp embed)) = (ambient g).comp embed := by
  apply invariant_of_adjacent ambient embed read read_embed
  intro i
  apply LinearMap.toMatrix'.injective
  ext p j
  exact congrFun (adjacent_basis i j) p

/-- The coordinate representation of the twenty-dimensional configuration space. -/
def representation : Representation (ZMod 2) (alternatingGroup (Fin 7)) Vector :=
  (onSubspace ambient embed read read_embed invariant).comp (alternatingGroup (Fin 7)).subtype

def threeCycle : alternatingGroup (Fin 7) :=
  ⟨Equiv.swap 0 1 * Equiv.swap 1 2, by rw [_root_.Equiv.Perm.mem_alternatingGroup]; decide⟩

def sevenCycle : alternatingGroup (Fin 7) :=
  ⟨Equiv.swap 0 1 * Equiv.swap 1 2 * Equiv.swap 2 3 *
    Equiv.swap 3 4 * Equiv.swap 4 5 * Equiv.swap 5 6, by rw [_root_.Equiv.Perm.mem_alternatingGroup]; decide⟩

@[expose] def firstMatrix : Matrix (Fin 20) (Fin 20) (ZMod 2) := fun i j => bit 171489811548135047602965734258331613418654358039126851960111791276051928573830141681579435586066231651880859681109835777 (20 * i.val + j.val)

@[expose] def secondMatrix : Matrix (Fin 20) (Fin 20) (ZMod 2) := fun i j => bit 161391849677165053054370219928099606362290306349849640992003837363345042642160817421121261320952325559788351296943300023 (20 * i.val + j.val)

private theorem first_rows : ∀ i : Fin 20,
    (edgeRow (pointIndex (permute threeCycle.val (freeEdges i)))) =
      #[1, 18003, 524677, 2440, 16, 410684, 10576, 65536, 4096, 254689, 249015, 69640, 4352, 65608, 1796, 512, 65664, 264768, 1034718, 69636][i.val]! := by
  decide +kernel

private theorem second_rows : ∀ i : Fin 20,
    (edgeRow (pointIndex (permute sevenCycle.val (freeEdges i)))) =
      #[138679, 16, 248243, 256, 17934, 17, 2, 4164, 64, 32, 254083, 4, 512, 8, 2048, 262144, 1796, 128, 524707, 65536][i.val]! := by
  decide +kernel

private theorem first_flatten : ∀ i : Fin 20,
    #[1, 18003, 524677, 2440, 16, 410684, 10576, 65536, 4096, 254689, 249015, 69640, 4352, 65608, 1796, 512, 65664, 264768, 1034718, 69636][i.val]! =
      (171489811548135047602965734258331613418654358039126851960111791276051928573830141681579435586066231651880859681109835777 >>> (20 * i.val)) % 2 ^ 20 := by
  decide +kernel

private theorem second_flatten : ∀ i : Fin 20,
    #[138679, 16, 248243, 256, 17934, 17, 2, 4164, 64, 32, 254083, 4, 512, 8, 2048, 262144, 1796, 128, 524707, 65536][i.val]! =
      (161391849677165053054370219928099606362290306349849640992003837363345042642160817421121261320952325559788351296943300023 >>> (20 * i.val)) % 2 ^ 20 := by
  decide +kernel

theorem matrix_threeCycle : LinearMap.toMatrix' (representation threeCycle) = firstMatrix := by
  ext i j
  change embed (Pi.single j 1) (permute threeCycle.val (freeEdges i)) = _
  rw [embed_single, first_rows, first_flatten]
  unfold firstMatrix bit
  rw [Nat.testBit_mod_two_pow _ 20 j.val, Nat.testBit_shiftRight]
  simp only [j.isLt, decide_true, Bool.true_and]

theorem matrix_sevenCycle : LinearMap.toMatrix' (representation sevenCycle) = secondMatrix := by
  ext i j
  change embed (Pi.single j 1) (permute sevenCycle.val (freeEdges i)) = _
  rw [embed_single, second_rows, second_flatten]
  unfold secondMatrix bit
  rw [Nat.testBit_mod_two_pow _ 20 j.val, Nat.testBit_shiftRight]
  simp only [j.isLt, decide_true, Bool.true_and]

end Twenty
end Representation.AlternatingSevenBinaryLargeModels
