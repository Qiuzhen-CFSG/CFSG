module

public import Theory.GroupTheory.Recognition.ReeTwo.SmallParityThreeLongCountArithmetic

/-!
# Centralizer sizes for the long rank-three parity rows

The table records the centralizer size at each finite parameter. Every entry
is verified against a population count of the ambient collected commuting mask.
The checks are split into blocks to limit temporary kernel memory. These counts
are independent of the identification of the parameters with a subgroup.

Source: Shinoda (1975), (2.3), pp. 81–82, through
`SmallParityThreeLongCoordinates` and the verified bit-vector arithmetic.
The table entries are proposed witnesses, justified by the certificates below.
-/

@[expose] public section
namespace ReeTwo.SylowModel.SmallParityLong.Counts
set_option maxRecDepth 32768
set_option exponentiation.threshold 1024
/-- Proposed centralizer sizes, subsequently certified using collected multiplication. -/
def centralTable (c : Fin 3) (n : Fin (size c)) : ℕ :=
  (![([512, 16, 32, 16, 128, 16, 32, 16, 64, 16, 32, 16, 64, 16, 64, 16, 128, 16, 32, 16, 128, 16, 32, 16, 64, 16, 32, 16, 64, 16, 64, 16, 256, 16, 32, 16, 128, 16, 32, 16, 64, 16, 32, 16, 64, 16, 64, 16, 128, 16, 32, 16, 128, 16, 32, 16, 64, 16, 32, 16, 64, 16, 64, 16, 512, 16, 32, 16, 128, 16, 32, 16, 64, 16, 32, 16, 64, 16, 64, 16, 128, 16, 32, 16, 128, 16, 32, 16, 64, 16, 32, 16, 64, 16, 64, 16, 256, 16, 32, 16, 128, 16, 32, 16, 64, 16, 32, 16, 64, 16, 64, 16, 128, 16, 32, 16, 128, 16, 32, 16, 64, 16, 32, 16, 64, 16, 64, 16, 64, 16, 32, 16, 64, 16, 64, 16, 128, 16, 32, 16, 128, 16, 32, 16, 64, 16, 32, 16, 64, 16, 64, 16, 256, 16, 32, 16, 128, 16, 32, 16, 64, 16, 32, 16, 64, 16, 64, 16, 128, 16, 32, 16, 128, 16, 32, 16, 64, 16, 32, 16, 64, 16, 64, 16, 256, 16, 32, 16, 128, 16, 32, 16, 64, 16, 32, 16, 64, 16, 64, 16, 128, 16, 32, 16, 128, 16, 32, 16, 64, 16, 32, 16, 64, 16, 64, 16, 256, 16, 32, 16, 128, 16, 32, 16, 64, 16, 32, 16, 64, 16, 64, 16, 128, 16, 32, 16, 128, 16, 32, 16, 64, 16, 32, 16, 64, 16, 64, 16, 256, 16, 32, 16, 128, 16, 32, 16, 64, 16, 32, 16, 64, 16, 32, 16, 64, 16, 32, 16, 64, 16, 64, 16, 64, 16, 32, 16, 64, 16, 32, 16, 64, 16, 32, 16, 64, 16, 64, 16, 64, 16, 32, 16, 64, 16, 32, 16, 64, 16, 32, 16, 64, 16, 64, 16, 64, 16, 32, 16, 64, 16, 32, 16, 64, 16, 32, 16, 64, 16, 64, 16, 64, 16, 32, 16, 64, 16, 32, 16, 64, 16, 32, 16, 64, 16, 64, 16, 64, 16, 32, 16, 64, 16, 32, 16, 64, 16, 32, 16, 64, 16, 64, 16, 64, 16, 32, 16, 64, 16, 32, 16, 64, 16, 32, 16, 64, 16, 64, 16, 64, 16, 32, 16, 64, 16, 32, 16, 64, 16, 32, 16, 64, 16, 64, 16, 64, 16, 32, 16, 64, 16, 64, 16, 64, 16, 32, 16, 64, 16, 32, 16, 64, 16, 32, 16, 64, 16, 64, 16, 64, 16, 32, 16, 64, 16, 32, 16, 64, 16, 32, 16, 64, 16, 64, 16, 64, 16, 32, 16, 64, 16, 32, 16, 64, 16, 32, 16, 64, 16, 64, 16, 64, 16, 32, 16, 64, 16, 32, 16, 64, 16, 32, 16, 64, 16, 64, 16, 64, 16, 32, 16, 64, 16, 32, 16, 64, 16, 32, 16, 64, 16, 64, 16, 64, 16, 32, 16, 64, 16, 32, 16, 64, 16, 32, 16, 64, 16, 64, 16, 64, 16, 32, 16, 64, 16, 32, 16, 64, 16, 32, 16, 64, 16, 64, 16, 64, 16, 32, 16, 64, 16, 32, 16] : List ℕ),
    ([256, 16, 32, 16, 64, 16, 32, 16, 64, 16, 32, 16, 64, 16, 32, 16, 64, 16, 32, 16, 64, 16, 32, 16, 256, 16, 32, 16, 64, 16, 32, 16, 128, 16, 32, 16, 64, 16, 32, 16, 64, 16, 32, 16, 64, 16, 32, 16, 64, 16, 32, 16, 64, 16, 32, 16, 128, 16, 32, 16, 64, 16, 32, 16, 256, 16, 32, 16, 64, 16, 32, 16, 64, 16, 32, 16, 64, 16, 32, 16, 64, 16, 32, 16, 64, 16, 32, 16, 256, 16, 32, 16, 64, 16, 32, 16, 128, 16, 32, 16, 64, 16, 32, 16, 64, 16, 32, 16, 64, 16, 32, 16, 64, 16, 32, 16, 64, 16, 32, 16, 128, 16, 32, 16, 64, 16, 32, 16, 32, 16, 32, 16, 32, 16, 64, 16, 32, 16, 32, 16, 32, 16, 64, 16, 32, 16, 32, 16, 32, 16, 64, 16, 32, 16, 32, 16, 32, 16, 64, 16, 32, 16, 32, 16, 32, 16, 64, 16, 32, 16, 32, 16, 32, 16, 64, 16, 32, 16, 32, 16, 32, 16, 64, 16, 32, 16, 32, 16, 32, 16, 64, 16, 32, 16, 32, 16, 32, 16, 64, 16, 32, 16, 32, 16, 32, 16, 64, 16, 32, 16, 32, 16, 32, 16, 64, 16, 32, 16, 32, 16, 32, 16, 64, 16, 32, 16, 32, 16, 32, 16, 64, 16, 32, 16, 32, 16, 32, 16, 64, 16, 32, 16, 32, 16, 32, 16, 64, 16, 32, 16, 32, 16, 32, 16, 64, 16] : List ℕ),
    ([128, 16, 32, 16, 32, 16, 32, 16, 32, 16, 32, 16, 64, 16, 32, 16, 32, 16, 32, 16, 64, 16, 64, 16, 128, 16, 32, 16, 32, 16, 64, 16, 64, 16, 32, 16, 32, 16, 32, 16, 32, 16, 32, 16, 64, 16, 32, 16, 32, 16, 32, 16, 64, 16, 64, 16, 64, 16, 32, 16, 32, 16, 64, 16, 128, 16, 32, 16, 32, 16, 32, 16, 32, 16, 32, 16, 64, 16, 32, 16, 32, 16, 32, 16, 64, 16, 64, 16, 128, 16, 32, 16, 32, 16, 64, 16, 64, 16, 32, 16, 32, 16, 32, 16, 32, 16, 32, 16, 64, 16, 32, 16, 32, 16, 32, 16, 64, 16, 64, 16, 64, 16, 32, 16, 32, 16, 64, 16] : List ℕ)] : Fin 3 → List ℕ) c |>.getD n.val 0



set_option Elab.async false in
set_option maxHeartbeats 1000000 in
private theorem central_block_0_0 : ∀ m : Fin 64,
    centralCount 0 (element 0 (enumerate 0 (@finProdFinEquiv 8 64 ((0 : Fin 8), m)))) =
      centralTable 0 (@finProdFinEquiv 8 64 ((0 : Fin 8), m)) := by decide +kernel

set_option Elab.async false in
set_option maxHeartbeats 1000000 in
private theorem central_block_0_1 : ∀ m : Fin 64,
    centralCount 0 (element 0 (enumerate 0 (@finProdFinEquiv 8 64 ((1 : Fin 8), m)))) =
      centralTable 0 (@finProdFinEquiv 8 64 ((1 : Fin 8), m)) := by decide +kernel

set_option Elab.async false in
set_option maxHeartbeats 1000000 in
private theorem central_block_0_2 : ∀ m : Fin 64,
    centralCount 0 (element 0 (enumerate 0 (@finProdFinEquiv 8 64 ((2 : Fin 8), m)))) =
      centralTable 0 (@finProdFinEquiv 8 64 ((2 : Fin 8), m)) := by decide +kernel

set_option Elab.async false in
set_option maxHeartbeats 1000000 in
private theorem central_block_0_3 : ∀ m : Fin 64,
    centralCount 0 (element 0 (enumerate 0 (@finProdFinEquiv 8 64 ((3 : Fin 8), m)))) =
      centralTable 0 (@finProdFinEquiv 8 64 ((3 : Fin 8), m)) := by decide +kernel

set_option Elab.async false in
set_option maxHeartbeats 1000000 in
private theorem central_block_0_4 : ∀ m : Fin 64,
    centralCount 0 (element 0 (enumerate 0 (@finProdFinEquiv 8 64 ((4 : Fin 8), m)))) =
      centralTable 0 (@finProdFinEquiv 8 64 ((4 : Fin 8), m)) := by decide +kernel

set_option Elab.async false in
set_option maxHeartbeats 1000000 in
private theorem central_block_0_5 : ∀ m : Fin 64,
    centralCount 0 (element 0 (enumerate 0 (@finProdFinEquiv 8 64 ((5 : Fin 8), m)))) =
      centralTable 0 (@finProdFinEquiv 8 64 ((5 : Fin 8), m)) := by decide +kernel

set_option Elab.async false in
set_option maxHeartbeats 1000000 in
private theorem central_block_0_6 : ∀ m : Fin 64,
    centralCount 0 (element 0 (enumerate 0 (@finProdFinEquiv 8 64 ((6 : Fin 8), m)))) =
      centralTable 0 (@finProdFinEquiv 8 64 ((6 : Fin 8), m)) := by decide +kernel

set_option Elab.async false in
set_option maxHeartbeats 1000000 in
private theorem central_block_0_7 : ∀ m : Fin 64,
    centralCount 0 (element 0 (enumerate 0 (@finProdFinEquiv 8 64 ((7 : Fin 8), m)))) =
      centralTable 0 (@finProdFinEquiv 8 64 ((7 : Fin 8), m)) := by decide +kernel

private theorem central_certificate_0 (n : Fin (size 0)) :
    centralCount 0 (element 0 (enumerate 0 n)) = centralTable 0 n := by
  obtain ⟨⟨b,m⟩, rfl⟩ := (@finProdFinEquiv 8 64).surjective (show Fin (8*64) from n)
  fin_cases b
  · exact central_block_0_0 m
  · exact central_block_0_1 m
  · exact central_block_0_2 m
  · exact central_block_0_3 m
  · exact central_block_0_4 m
  · exact central_block_0_5 m
  · exact central_block_0_6 m
  · exact central_block_0_7 m

set_option Elab.async false in
set_option maxHeartbeats 1000000 in
private theorem central_block_1_0 : ∀ m : Fin 64,
    centralCount 1 (element 1 (enumerate 1 (@finProdFinEquiv 4 64 ((0 : Fin 4), m)))) =
      centralTable 1 (@finProdFinEquiv 4 64 ((0 : Fin 4), m)) := by decide +kernel

set_option Elab.async false in
set_option maxHeartbeats 1000000 in
private theorem central_block_1_1 : ∀ m : Fin 64,
    centralCount 1 (element 1 (enumerate 1 (@finProdFinEquiv 4 64 ((1 : Fin 4), m)))) =
      centralTable 1 (@finProdFinEquiv 4 64 ((1 : Fin 4), m)) := by decide +kernel

set_option Elab.async false in
set_option maxHeartbeats 1000000 in
private theorem central_block_1_2 : ∀ m : Fin 64,
    centralCount 1 (element 1 (enumerate 1 (@finProdFinEquiv 4 64 ((2 : Fin 4), m)))) =
      centralTable 1 (@finProdFinEquiv 4 64 ((2 : Fin 4), m)) := by decide +kernel

set_option Elab.async false in
set_option maxHeartbeats 1000000 in
private theorem central_block_1_3 : ∀ m : Fin 64,
    centralCount 1 (element 1 (enumerate 1 (@finProdFinEquiv 4 64 ((3 : Fin 4), m)))) =
      centralTable 1 (@finProdFinEquiv 4 64 ((3 : Fin 4), m)) := by decide +kernel

private theorem central_certificate_1 (n : Fin (size 1)) :
    centralCount 1 (element 1 (enumerate 1 n)) = centralTable 1 n := by
  obtain ⟨⟨b,m⟩, rfl⟩ := (@finProdFinEquiv 4 64).surjective (show Fin (4*64) from n)
  fin_cases b
  · exact central_block_1_0 m
  · exact central_block_1_1 m
  · exact central_block_1_2 m
  · exact central_block_1_3 m

set_option Elab.async false in
set_option maxHeartbeats 1000000 in
private theorem central_block_2_0 : ∀ m : Fin 64,
    centralCount 2 (element 2 (enumerate 2 (@finProdFinEquiv 2 64 ((0 : Fin 2), m)))) =
      centralTable 2 (@finProdFinEquiv 2 64 ((0 : Fin 2), m)) := by decide +kernel

set_option Elab.async false in
set_option maxHeartbeats 1000000 in
private theorem central_block_2_1 : ∀ m : Fin 64,
    centralCount 2 (element 2 (enumerate 2 (@finProdFinEquiv 2 64 ((1 : Fin 2), m)))) =
      centralTable 2 (@finProdFinEquiv 2 64 ((1 : Fin 2), m)) := by decide +kernel

private theorem central_certificate_2 (n : Fin (size 2)) :
    centralCount 2 (element 2 (enumerate 2 n)) = centralTable 2 n := by
  obtain ⟨⟨b,m⟩, rfl⟩ := (@finProdFinEquiv 2 64).surjective (show Fin (2*64) from n)
  fin_cases b
  · exact central_block_2_0 m
  · exact central_block_2_1 m

/-- The table is the exact number of commuting original parameters. -/
theorem commutingCount_table (c : Fin 3) (n : Fin (size c)) :
    commutingCount c (element c (enumerate c n)) = centralTable c n := by
  rw [centralCount_eq]
  fin_cases c
  · exact central_certificate_0 n
  · exact central_certificate_1 n
  · exact central_certificate_2 n
end ReeTwo.SylowModel.SmallParityLong.Counts
