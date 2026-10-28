module

public import Theory.SpecificGroups.HaradaNorton.Simplicity.Reduction
public import Theory.SpecificGroups.HaradaNorton.Simplicity.WordCertificates.ABProducts
public import Theory.SpecificGroups.HaradaNorton.Simplicity.WordCertificates.PerfectProducts

/-!
# Certified HN word identities

The fixed ATLAS matrices satisfy `(AB)²² = I` and `((AB)⁵B)²⁵ = I`.
Explicit intermediate matrices certify an addition chain for each exponent.
Packed arithmetic is proved to decode to ordinary matrix multiplication, and
all numerical products are checked by Lean's kernel. Faithfulness of
`matrixHom` transfers the identities to the fixed group `HN`.

These two relations discharge the hypotheses of the perfectness and normal
generation lemmas in `Simplicity.Reduction`. They assert individual identities,
without treating the ATLAS semi-presentation as a defining presentation.
Source: https://brauer.maths.qmul.ac.uk/Atlas/v3/spor/HN/, standard-generator
product of order 22 and class-25A word `abababababb`. Matrix attribution is in
`../MatrixSources.md`; the reproducible certificate generator is
`WordCertificates/GenerateCertificates.py`.
-/

namespace HaradaNorton

open WordCertificates

private instance entriesDecidable (A B : Matrix133) :
    Decidable (∀ i j : Fin 133, A i j = B i j) :=
  @Nat.decidableForallFin 133 _ (fun i =>
    @Nat.decidableForallFin 133 _ (fun j => ZMod.decidableEq 5 (A i j) (B i j)))

set_option maxRecDepth 10000 in
private theorem decode_aPacked : decode aPacked = aMatrix := by
  apply Matrix.ext
  decide +kernel

set_option maxRecDepth 10000 in
private theorem decode_bPacked : decode bPacked = bMatrix := by
  apply Matrix.ext
  decide +kernel

private theorem matrix_ab_eq : aMatrix * bMatrix = decode abRows := by
  rw [← decode_aPacked, ← decode_bPacked]
  exact product_ab

private theorem matrix_ab_pow_five : (aMatrix * bMatrix) ^ 5 = decode ab5Rows := by
  rw [matrix_ab_eq]
  have h2 : decode abRows ^ 2 = decode ab2Rows := (pow_two _).trans product_ab2
  have h4 : decode abRows ^ 4 = decode ab4Rows := by
    calc
      _ = decode abRows ^ 2 * decode abRows ^ 2 := pow_add _ 2 2
      _ = _ := by rw [h2, product_ab4]
  rw [pow_succ, h4, product_ab5]

private theorem matrix_ab_pow_twenty_two : (aMatrix * bMatrix) ^ 22 = 1 := by
  have h10 : (aMatrix * bMatrix) ^ 10 = decode ab10Rows := by
    calc
      _ = (aMatrix * bMatrix) ^ 5 * (aMatrix * bMatrix) ^ 5 := pow_add _ 5 5
      _ = _ := by rw [matrix_ab_pow_five, product_ab10]
  have h11 : (aMatrix * bMatrix) ^ 11 = decode ab11Rows := by
    rw [pow_succ, h10, matrix_ab_eq, product_ab11]
  calc
    _ = (aMatrix * bMatrix) ^ 11 * (aMatrix * bMatrix) ^ 11 := pow_add _ 11 11
    _ = 1 := by rw [h11, product_ab22, decode_oneRows]

private theorem matrix_word_eq : (aMatrix * bMatrix) ^ 5 * bMatrix = decode wordRows := by
  rw [matrix_ab_pow_five, ← decode_bPacked, product_word]

private theorem matrix_word_pow_twenty_five :
    ((aMatrix * bMatrix) ^ 5 * bMatrix) ^ 25 = 1 := by
  rw [matrix_word_eq]
  have h2 : decode wordRows ^ 2 = decode word2Rows := (pow_two _).trans product_word2
  have h4 : decode wordRows ^ 4 = decode word4Rows := by
    calc
      _ = decode wordRows ^ 2 * decode wordRows ^ 2 := pow_add _ 2 2
      _ = _ := by rw [h2, product_word4]
  have h8 : decode wordRows ^ 8 = decode word8Rows := by
    calc
      _ = decode wordRows ^ 4 * decode wordRows ^ 4 := pow_add _ 4 4
      _ = _ := by rw [h4, product_word8]
  have h12 : decode wordRows ^ 12 = decode word12Rows := by
    calc
      _ = decode wordRows ^ 8 * decode wordRows ^ 4 := pow_add _ 8 4
      _ = _ := by rw [h8, h4, product_word12]
  have h24 : decode wordRows ^ 24 = decode word24Rows := by
    calc
      _ = decode wordRows ^ 12 * decode wordRows ^ 12 := pow_add _ 12 12
      _ = _ := by rw [h12, product_word24]
  rw [pow_succ, h24, product_word25, decode_oneRows]

/-- The product of the two fixed HN generators has twenty-second power one. -/
public theorem ab_pow_twenty_two : (a * b) ^ 22 = 1 := by
  apply matrixHom_injective
  simpa only [map_pow, map_mul, matrixHom_a, matrixHom_b, map_one] using
    matrix_ab_pow_twenty_two

/-- The ATLAS class-25A word has twenty-fifth power one in the fixed HN group. -/
public theorem perfectWord_pow_twenty_five : perfectWord ^ 25 = 1 := by
  apply matrixHom_injective
  simpa only [perfectWord, map_pow, map_mul, matrixHom_a, matrixHom_b, map_one] using
    matrix_word_pow_twenty_five

end HaradaNorton
