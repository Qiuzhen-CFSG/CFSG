module

public import Theory.SpecificGroups.Janko4.Model.LocalStructure.SymmetricLinear.CharacteristicTwo.NormalClosure.WordProducts

/-!
# The eleven literal normal-closure words in certified coordinates

The seed evaluation uses its sixth-power certificate. Each next conjugate is
obtained from a checked identity `q*g = g*q'`, with `g` alternating between the
literal max4 generators. Faithful coordinates use the existing certified basis.
No inverse table or external evaluator is assumed. See `source/README.md`.

This supplies the word-evaluation premise of the characteristic-two assembly,
for Aschbacher–Smith condition E, printed pp.3–4 and 481–482.
-/

public section

namespace Janko4.LocalStructure.SymmetricLinear.CharacteristicTwo
open GeneratorCertificates NormalClosure NormalClosure.WordData NormalClosure.WordData.Products
local notation "ρ" => coordinateHom basis_mul_basisInverse basisInverse_mul_basis

private lemma decoded_product {a b c : Vector ℕ 112} (h : packedMul a b = c) :
    decodeRows a * decodeRows b = decodeRows c := by rw [← decode_packedMul, h]

private theorem seed_coordinates : coordinates seed = decodeRows (Coordinates.conjugateRows.get 0) := by
  have hy2 : decodeRows secondSquareRows = decodeRows Coordinates.secondRows ^ 2 := by
    rw [← decoded_product secondSquare, pow_two]
  have hw : decodeRows seedBaseRows =
      decodeRows Coordinates.firstRows * decodeRows Coordinates.secondRows ^ 2 := by
    rw [← decoded_product seedBase, hy2]
  have hw2 : decodeRows seedBaseSquareRows = decodeRows seedBaseRows ^ 2 := by
    rw [← decoded_product seedBaseSquare, pow_two]
  have hw3 : decodeRows seedBaseCubeRows = decodeRows seedBaseRows ^ 3 := by
    rw [← decoded_product seedBaseCube, hw2, ← pow_succ]
  have hw6 : decodeRows (Coordinates.conjugateRows.get 0) = decodeRows seedBaseRows ^ 6 := by
    rw [← decoded_product seedPower, hw3, ← pow_add]
  rw [← coordinateHom_apply basis_mul_basisInverse basisInverse_mul_basis,
    seed, map_pow, map_mul, map_pow, coordinateHom_apply, coordinateHom_apply,
    first_coordinates, second_coordinates, hw6, hw]

private theorem eval_conjugate {q g : max4Subgroup} {A B C : BinaryMatrix}
    (hq : coordinates q = A) (hg : coordinates g = B) (h : A * B = B * C) :
    coordinates (g⁻¹ * q * g) = C := by
  have hq' : ρ q = A := (coordinateHom_apply _ _ q).trans hq
  have hg' : ρ g = B := (coordinateHom_apply _ _ g).trans hg
  rw [← coordinateHom_apply basis_mul_basisInverse basisInverse_mul_basis]
  calc
    ρ (g⁻¹ * q * g) = ρ g⁻¹ * (A * B) := by rw [map_mul, map_mul, hq', hg', mul_assoc]
    _ = ρ g⁻¹ * (B * C) := by rw [h]
    _ = C := by rw [← hg', ← mul_assoc, ← map_mul, inv_mul_cancel, map_one, one_mul]

private theorem eval_0 : coordinates (seedConjugate 0) =
    decodeRows (Coordinates.conjugateRows.get 0) := seed_coordinates

private theorem eval_1 : coordinates (seedConjugate 1) =
    decodeRows (Coordinates.conjugateRows.get 1) := by
  change coordinates (first⁻¹ * seedConjugate 0 * first) = _
  exact eval_conjugate eval_0 first_coordinates
    ((decoded_product conjugateLeft0).trans (decoded_product conjugateRight0).symm)

private theorem eval_2 : coordinates (seedConjugate 2) =
    decodeRows (Coordinates.conjugateRows.get 2) := by
  change coordinates (second⁻¹ * seedConjugate 1 * second) = _
  exact eval_conjugate eval_1 second_coordinates
    ((decoded_product conjugateLeft1).trans (decoded_product conjugateRight1).symm)

private theorem eval_3 : coordinates (seedConjugate 3) =
    decodeRows (Coordinates.conjugateRows.get 3) := by
  change coordinates (first⁻¹ * seedConjugate 2 * first) = _
  exact eval_conjugate eval_2 first_coordinates
    ((decoded_product conjugateLeft2).trans (decoded_product conjugateRight2).symm)

private theorem eval_4 : coordinates (seedConjugate 4) =
    decodeRows (Coordinates.conjugateRows.get 4) := by
  change coordinates (second⁻¹ * seedConjugate 3 * second) = _
  exact eval_conjugate eval_3 second_coordinates
    ((decoded_product conjugateLeft3).trans (decoded_product conjugateRight3).symm)

private theorem eval_5 : coordinates (seedConjugate 5) =
    decodeRows (Coordinates.conjugateRows.get 5) := by
  change coordinates (first⁻¹ * seedConjugate 4 * first) = _
  exact eval_conjugate eval_4 first_coordinates
    ((decoded_product conjugateLeft4).trans (decoded_product conjugateRight4).symm)

private theorem eval_6 : coordinates (seedConjugate 6) =
    decodeRows (Coordinates.conjugateRows.get 6) := by
  change coordinates (second⁻¹ * seedConjugate 5 * second) = _
  exact eval_conjugate eval_5 second_coordinates
    ((decoded_product conjugateLeft5).trans (decoded_product conjugateRight5).symm)

private theorem eval_7 : coordinates (seedConjugate 7) =
    decodeRows (Coordinates.conjugateRows.get 7) := by
  change coordinates (first⁻¹ * seedConjugate 6 * first) = _
  exact eval_conjugate eval_6 first_coordinates
    ((decoded_product conjugateLeft6).trans (decoded_product conjugateRight6).symm)

private theorem eval_8 : coordinates (seedConjugate 8) =
    decodeRows (Coordinates.conjugateRows.get 8) := by
  change coordinates (second⁻¹ * seedConjugate 7 * second) = _
  exact eval_conjugate eval_7 second_coordinates
    ((decoded_product conjugateLeft7).trans (decoded_product conjugateRight7).symm)

private theorem eval_9 : coordinates (seedConjugate 9) =
    decodeRows (Coordinates.conjugateRows.get 9) := by
  change coordinates (first⁻¹ * seedConjugate 8 * first) = _
  exact eval_conjugate eval_8 first_coordinates
    ((decoded_product conjugateLeft8).trans (decoded_product conjugateRight8).symm)

private theorem eval_10 : coordinates (seedConjugate 10) =
    decodeRows (Coordinates.conjugateRows.get 10) := by
  change coordinates (second⁻¹ * seedConjugate 9 * second) = _
  exact eval_conjugate eval_9 second_coordinates
    ((decoded_product conjugateLeft9).trans (decoded_product conjugateRight9).symm)

/-- The eleven tables evaluate the literal alternating right conjugates. -/
theorem seedConjugate_coordinates (k : Fin 11) :
    coordinates (seedConjugate k.val) = decodeRows (Coordinates.conjugateRows.get k) := by
  fin_cases k
  · exact eval_0
  · exact eval_1
  · exact eval_2
  · exact eval_3
  · exact eval_4
  · exact eval_5
  · exact eval_6
  · exact eval_7
  · exact eval_8
  · exact eval_9
  · exact eval_10

end Janko4.LocalStructure.SymmetricLinear.CharacteristicTwo
