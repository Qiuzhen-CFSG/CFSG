module

public import Theory.Representation.G2DerivedPermutationFiltration.VertexFiltrations.CoordinateFiltrations.Density.Arithmetic

/-!
# Density of the 6-dimensional binary diagonal factor

The stored matrices are obtained by multiplying earlier stored matrices by
one of the two literal generators. The inverse coefficient table writes each
matrix unit as their binary sum. Packed arithmetic is checked by kernel
reduction and interpreted by the soundness lemmas in `Density.Arithmetic`.
The witness integers use bit `n * row + column`; the saved exploration used
the transposed packing. See LICENSES/ATLAS.txt for the original action data.
This supplies a matrix certificate used in Aschbacher–Smith G.7.2(3), p.348.
Witness provenance: the adapted ATLAS data in `CoordinateFiltrations.Data`.
-/

@[expose] public section
namespace G2DerivedPermutationFiltration.VertexCoordinates.CoordinateFiltrations.Density.Six
open Thompson.BinaryMatrix

local instance : NeZero (length 0) := ⟨by decide⟩

private def generators : Fin 2 → Array ℕ := ![#[10, 33, 50, 54, 62, 15], #[3, 29, 47, 19, 23, 36]]
private def packed : Array ℕ := #[34630287489, 17160677450, 39045756739, 50810388823, 66158201899, 36809664974, 12451080734, 34573381159, 68016471122, 49915012517, 31624085083, 7397014310, 13252840681, 61371864417, 14332145142, 32972406495, 45388499831, 52526666595, 20522103516, 4407416499, 14356021637, 15803681314, 39662725141, 18887617546, 6261745992, 43675064538, 54233294358, 65430666100, 68272709761, 26652475496, 53253268388, 15691445496, 39750725230, 66402251718, 56761707607, 61517842729]
private def storedRows : Array (Array ℕ) :=
  #[#[1, 2, 4, 8, 16, 32], #[10, 33, 50, 54, 62, 15], #[3, 29, 47, 19, 23, 36], #[23, 5, 16, 34, 20, 47], #[43, 48, 32, 21, 39, 61], #[14, 39, 46, 1, 18, 34], #[30, 40, 6, 9, 38, 11], #[39, 56, 62, 46, 12, 32], #[18, 49, 15, 6, 22, 63], #[37, 22, 42, 10, 31, 46], #[27, 57, 19, 60, 28, 29], #[38, 44, 23, 57, 56, 6], #[41, 51, 36, 59, 21, 12], #[33, 21, 5, 3, 10, 57], #[54, 55, 50, 16, 22, 13], #[31, 59, 47, 19, 45, 30], #[55, 45, 24, 23, 17, 42], #[35, 13, 21, 53, 58, 48], #[28, 11, 39, 13, 7, 19], #[51, 26, 61, 44, 6, 4], #[5, 6, 56, 43, 23, 13], #[34, 40, 16, 62, 45, 14], #[21, 32, 18, 5, 60, 36], #[10, 48, 34, 50, 37, 17], #[8, 37, 42, 14, 53, 5], #[26, 35, 9, 15, 43, 40], #[22, 24, 38, 35, 32, 50], #[52, 45, 11, 62, 59, 60], #[1, 2, 46, 23, 37, 63], #[40, 1, 8, 39, 52, 24], #[36, 14, 6, 9, 38, 49], #[56, 19, 7, 18, 39, 14], #[46, 57, 62, 20, 1, 37], #[6, 15, 31, 56, 53, 61], #[23, 49, 46, 16, 55, 52], #[41, 36, 60, 47, 18, 57]]
private def parent : Fin 36 → Fin 36 :=
  ![0, 0, 0, 1, 1, 2, 2, 3, 3, 4, 4, 5, 5, 6, 6, 7, 8, 8, 9, 9, 10, 10, 11, 11, 12, 12, 13, 13, 14, 15, 15, 17, 17, 18, 18, 19]
private def letter : Fin 36 → Fin 2 :=
  ![0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1]
private def inverseColumns : Array ℕ := #[43216921690, 65691357651, 38903284398, 65771880159, 3460840008, 6108060040, 31731921977, 59236751444, 39572134262, 30411022159, 22767281795, 14670790231, 4086918942, 47654604284, 2687813347, 63860958210, 38258908746, 28410737959, 56011879797, 24902495842, 31678923760, 48921709771, 4719716471, 49373521657, 51962969585, 66384662078, 30078757324, 22503016294, 63113654448, 56964447140, 6175260448, 27694314472, 64268883368, 63533937732, 52702501383, 11664082583]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem generators_checked : ∀ j,
    decode 6 (generators j) = factorMatrix 0 1 j := by
  intro j
  apply Matrix.ext
  intro x y
  change Thompson.BinaryMatrix.bit (generators j)[x.val]! y.val =
    bit (actionColumns 0 j (blockIndex 0 1 y)) (blockIndex 0 1 x).val
  revert j x y
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem rows_checked : ∀ (k : Fin 36) (i : Fin 6),
    (storedRows[k.val]!)[i.val]! = (packed[k.val]! >>> (6 * i.val)) % 2 ^ 6 := by
  decide +kernel

private theorem stored_checked (k : Fin 36) :
    decode 6 (storedRows[k.val]!) = packedMatrix 6 packed[k.val]! :=
  decode_rows 6 _ _ (rows_checked k)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem zero_checked : packedMatrix 6 packed[0]! = 1 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem parent_checked : ∀ k : Fin 36, k.val ≠ 0 → (parent k).val < k.val := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem products_checked : ∀ k : Fin 36, k.val ≠ 0 → ∀ i : Fin 6,
    rowProduct (generators (letter k))[i.val]! (storedRows[(parent k).val]!) 6 =
      (storedRows[k.val]!)[i.val]! := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem inverse_checked : ∀ i j : Fin 6,
    rowProduct inverseColumns[6 * j.val + i.val]! packed 36 =
      2 ^ (6 * i.val + j.val) := by decide +kernel

theorem algebra_eq_top
    (Q : Subalgebra (ZMod 2) (Matrix (Fin 6) (Fin 6) (ZMod 2)))
    (h : ∀ j, factorMatrix 0 1 j ∈ Q) : Q = ⊤ := by
  apply density_of_certificate (n := 6) (factorMatrix 0 1) packed parent letter
      (fun k hk => by simpa only [hk] using zero_checked) parent_checked ?_
      (fun i j => inverseColumns[6 * j.val + i.val]!) inverse_checked Q h
  intro k hk
  rw [← stored_checked k, ← stored_checked (parent k), ← generators_checked]
  exact (decode_mul 6 _ _ _ (products_checked k hk)).symm

end G2DerivedPermutationFiltration.VertexCoordinates.CoordinateFiltrations.Density.Six
