module
public import Theory.Representation.HexacodeAction.TwelveDimensionalExclusion.CosetFiltration.CosetIdentification.Words
public import Theory.Representation.HexacodeAction.SixDimensionalRecognition.EvenImage.PairCertificate.Interpretation

/-!
# Faithful arithmetic for the fixed coset words

Integer exponents are reduced using the proved orders of the marked generators.
The existing four-symbol matrix arithmetic is interpreted through the faithful
field action on the actual hexacode. In particular the scalar is the literal
`hexEvenZ`, with eigenvalue omega, and the words keep their written order.

Source application: Aschbacher–Smith K.1.3, printed p.453 / PDF p.464.
The hexacode and marked pair are from the licensed ATLAS ports; see
`LICENSES/ATLAS.txt` and `LICENSES/ATLAS-CITATION.cff`.
-/

@[expose] public section

open Atlas.Codes
open Representation.Hexacode
open Representation.Hexacode.SixDimensional.EvenImage
open Representation.Hexacode.SixDimensional.EvenImage.PairData
open Representation.Hexacode.SixDimensional.EvenImage.PairData.Q
open Representation.Hexacode.TwelveDimensional
open Representation.Hexacode.TwelveDimensional.CosetCertificate
open Representation.Hexacode.TwelveDimensional.CosetCertificate.CosetIdentification

namespace Representation.Hexacode.TwelveDimensional.CosetCertificate.CosetIdentification.WordGeometry

def mpow (m : M) : ℕ → M
  | 0 => ident
  | n + 1 => mm (mpow m n) m

theorem decode_mpow (m : M) (n : ℕ) : decode (mpow m n) = decode m ^ n := by
  induction n with
  | zero => exact decode_ident
  | succ n ih => rw [mpow, decode_mm, ih, pow_succ]

def genOrder (j : Fin 2) : ℕ := if j = 0 then 4 else 3

def genMatrix : Fin 2 → M := ![first, second]

def letterMatrix (a : Fin 2 × ℤ) : M :=
  mpow (genMatrix a.1) (a.2 % genOrder a.1).toNat

def wordMatrix (w : List (Fin 2 × ℤ)) : M := (w.map letterMatrix).foldr mm ident

noncomputable def coverMatrix : Cover →* Mat := matrix.comp evenFieldAction

theorem coverMatrix_injective : Function.Injective coverMatrix :=
  matrix_injective.comp evenFieldAction_injective

theorem coverMatrix_generator (j : Fin 2) : coverMatrix (coverGenerator j) = decode (genMatrix j) := by
  fin_cases j
  · exact matrix_first
  · exact matrix_second

theorem generator_power (j : Fin 2) : coverGenerator j ^ genOrder j = 1 := by
  fin_cases j
  · exact generatorA_four
  · exact generatorB_three

theorem coverMatrix_letter (a : Fin 2 × ℤ) :
    coverMatrix (coverGenerator a.1 ^ a.2) = decode (letterMatrix a) := by
  rw [zpow_eq_zpow_emod' _ (generator_power a.1)]
  have hp : 0 ≤ a.2 % (genOrder a.1 : ℤ) := Int.emod_nonneg _ (by
    have h : ∀ j, (genOrder j : ℤ) ≠ 0 := by decide +kernel
    exact h a.1)
  rw [← Int.toNat_of_nonneg hp, zpow_natCast, map_pow, coverMatrix_generator]
  exact (decode_mpow _ _).symm

theorem coverMatrix_word (w : List (Fin 2 × ℤ)) :
    coverMatrix (evalWord w) = decode (wordMatrix w) := by
  induction w with
  | nil => simp [evalWord, wordMatrix, decode_ident]
  | cons a w ih =>
    change coverMatrix (coverGenerator a.1 ^ a.2 * evalWord w) =
      decode (mm (letterMatrix a) (wordMatrix w))
    rw [map_mul, coverMatrix_letter, ih, decode_mm]

def scalarMatrix : M := ⟨w,z,z,z,w,z,z,z,w⟩

theorem coverMatrix_scalar : coverMatrix hexEvenZ = decode scalarMatrix := by
  apply Matrix.toLin'.injective
  apply LinearMap.ext
  intro x
  change (matrix (evenFieldAction hexEvenZ)).mulVec x = (decode scalarMatrix).mulVec x
  rw [matrix_apply]
  change binaryCoordinates (action hexZ (fieldCoordinates.symm x)) = _
  rw [scalar_coordinates]
  change omega • fieldCoordinates (fieldCoordinates.symm x) = _
  rw [fieldCoordinates.apply_symm_apply]
  funext i
  fin_cases i <;> simp [decode, scalarMatrix, value, Matrix.mulVec, dotProduct,
    Fin.sum_univ_succ]

end Representation.Hexacode.TwelveDimensional.CosetCertificate.CosetIdentification.WordGeometry
