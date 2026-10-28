module

public import Theory.Representation.HexacodeAction.SixDimensionalRecognition.EvenImage.Operators
public import Theory.Representation.HexacodeAction.SixDimensionalRecognition.EvenImage.PairCertificate.Coverage
public import Theory.Representation.HexacodeAction.SixDimensionalRecognition.EvenImage.PairCertificate.Interpretation
/-!
# Certifying normalized even hexacode pairs

Every field-linear operator `v` satisfying the three displayed pair relations
can be conjugated into the literal even hexacode image while fixing the first
generator. Exhaustive kernel checks cover all three by three F₄ matrices,
without assuming a determinant, scalar exclusion or conjugacy classification.
For each surviving matrix they supply a two-sided inverse for a centralizing
conjugator and an equality with one of four words in the actual generators.
The coordinate interpretation transports those identities to the original
hexacode carrier and proves the exact second input of
`exists_twist_of_pair_inputs`.

The independent order-four normalization and the final representation
recognition remain with the importing assembly module. No representation
uniqueness or image membership is assumed here.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, K.1.3,
printed p.453 (PDF p.464). The generator source and ATLAS attribution are
recorded in `EvenImage/Generators.lean`; certificate reconstruction and
measurements are recorded in `PairCertificate/source/README.md`.
-/

@[expose] public section
open Atlas.Codes
namespace Representation.Hexacode.SixDimensional.EvenImage
open PairData

private theorem decode_cube (m : M) : decode (cube m) = decode m ^ 3 := by
  simp [cube, decode_mm, pow_succ]
private theorem decode_fifth (m : M) : decode (fifth m) = decode m ^ 5 := by
  simp [fifth, decode_mm, pow_succ, mul_assoc]

private theorem encoded_relations (v : FieldGL)
    (h3 : v ^ 3 = 1) (h5 : (fieldGenerator * v) ^ 5 = 1)
    (h23 : (fieldGenerator * v ^ 2) ^ 3 = 1) : Relations (encode (matrix v)) := by
  have h3' := congrArg matrix h3
  have h5' := congrArg matrix h5
  have h23' := congrArg matrix h23
  simp only [map_pow, map_mul, map_one] at h3' h5' h23'
  refine ⟨decode_injective ?_, decode_injective ?_, decode_injective ?_⟩
  · simpa only [decode_cube, decode_encode, decode_ident] using h3'
  · simpa only [decode_fifth, decode_mm, decode_encode, ← matrix_first, decode_ident]
      using h5'
  · simpa only [decode_cube, decode_mm, decode_encode, ← matrix_first, decode_ident,
      pow_two] using h23'

private def modelLetter : Fin 4 → HexEvenAutomorphisms :=
  ![generatorA, generatorB, generatorA ^ 3, generatorB ^ 2]
private def modelWord (w : List (Fin 4)) : HexEvenAutomorphisms :=
  (w.map modelLetter).prod

private theorem matrix_modelLetter (k : Fin 4) :
    matrix (evenFieldAction (modelLetter k)) = decode (letter k) := by
  have ha : matrix (evenFieldAction generatorA) = decode first := matrix_first
  fin_cases k <;>
    simp [modelLetter, letter, map_pow, ha, matrix_second, decode_cube,
      decode_mm, pow_two]

private theorem matrix_modelWord (w : List (Fin 4)) :
    matrix (evenFieldAction (modelWord w)) = decode (word w) := by
  induction w with
  | nil => simp [modelWord, word, decode_ident]
  | cons k w ih =>
    change matrix (evenFieldAction (modelLetter k * modelWord w)) =
      decode (mm (letter k) (word w))
    rw [map_mul, map_mul, matrix_modelLetter, ih, decode_mm]

private noncomputable def centralizingEquiv (j : Fin 16) : FieldGL :=
  ofMatrices (decode (conjugator j)) (decode (conjugatorInv j))
    (by rw [← decode_mm, (conjugator_checks j).1, decode_ident])
    (by rw [← decode_mm, (conjugator_checks j).2.1, decode_ident])

private theorem matrix_centralizingEquiv (j : Fin 16) :
    matrix (centralizingEquiv j) = decode (conjugator j) := matrix_ofMatrices _ _ _ _

private theorem matrix_centralizingEquiv_inv (j : Fin 16) :
    matrix (centralizingEquiv j)⁻¹ = decode (conjugatorInv j) := by
  change matrixRing (matrixRing.symm (decode (conjugatorInv j))) = _
  exact matrixRing.apply_symm_apply _

private theorem centralizingEquiv_commutes (j : Fin 16) :
    centralizingEquiv j * fieldGenerator = fieldGenerator * centralizingEquiv j := by
  apply matrix_injective
  rw [map_mul, map_mul, matrix_centralizingEquiv, matrix_first,
    ← decode_mm, ← decode_mm, (conjugator_checks j).2.2]

/-- A normalized pair can be placed in the actual even image by a conjugator
that fixes the first generator. No class or determinant premise is required. -/
theorem exists_pair_conjugates_centralizing (v : FieldGL)
    (h3 : v ^ 3 = 1) (h5 : (fieldGenerator * v) ^ 5 = 1)
    (h23 : (fieldGenerator * v ^ 2) ^ 3 = 1) :
    ∃ c : FieldGL, MulAut.conj c fieldGenerator = fieldGenerator ∧
      MulAut.conj c v ∈ evenFieldAction.range := by
  obtain ⟨k, hk⟩ := coverage (encode (matrix v)) (encoded_relations v h3 h5 h23)
  have hv : matrix v = decode (candidates k) := by
    rw [← decode_encode (matrix v), hk]
  refine ⟨centralizingEquiv (witness k), ?_, ?_⟩
  · change centralizingEquiv (witness k) * fieldGenerator *
      (centralizingEquiv (witness k))⁻¹ = fieldGenerator
    rw [centralizingEquiv_commutes, mul_assoc, mul_inv_cancel, mul_one]
  · refine ⟨modelWord (words (representative k)), ?_⟩
    apply matrix_injective
    change matrix (evenFieldAction (modelWord (words (representative k)))) =
      matrix (centralizingEquiv (witness k) * v * (centralizingEquiv (witness k))⁻¹)
    rw [map_mul, map_mul, matrix_centralizingEquiv, matrix_centralizingEquiv_inv,
      hv, matrix_modelWord, ← decode_mm, ← decode_mm, candidate_checks]

/-- The precise normalized-pair input required by `exists_twist_of_pair_inputs`. -/
theorem exists_pair_conjugates (v : FieldGL)
    (h3 : v ^ 3 = 1) (h5 : (fieldGenerator * v) ^ 5 = 1)
    (h23 : (fieldGenerator * v ^ 2) ^ 3 = 1) :
    ∃ c : FieldGL, MulAut.conj c fieldGenerator ∈ evenFieldAction.range ∧
      MulAut.conj c v ∈ evenFieldAction.range := by
  obtain ⟨c, hc, hv⟩ := exists_pair_conjugates_centralizing v h3 h5 h23
  refine ⟨c, ?_, hv⟩
  rw [hc]
  exact ⟨generatorA, rfl⟩
end Representation.Hexacode.SixDimensional.EvenImage
