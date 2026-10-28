module
public import Theory.Representation.HexacodeAction.SixDimensionalRecognition.EvenImage.PairCertificate.Data

/-!
# Exhaustive normalized pair certificate over F₄

The single variable is a nine-entry matrix; the first matrix is fixed.
Splitting its first row leaves 64 checks of 4096 matrices each. Every check
uses kernel reduction, including the existential index into the candidate
table. Thus coverage includes singular and scalar matrices as well: no
conjugacy-class, determinant or diagonalization premise is required.

The remaining small checks certify two-sided inverses for the sixteen
conjugators, their commutation with the first matrix, and the actual model
word reached from each candidate. The source use is K.1.3, printed p.453
(PDF p.464). See `PairCertificate/source/README.md` for measurements.
-/

@[expose] public section
namespace Representation.Hexacode.SixDimensional.EvenImage.PairData

set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
/-- Every matrix satisfying the three pair relations occurs in the table. -/
theorem coverage (v : M) (hv : Relations v) : ∃ k : Fin 64, v = candidates k := by
  rcases v with ⟨a,b,c,d,e,f,g,h,i⟩
  revert d e f g h i
  cases a <;> cases b <;> cases c <;> decide +kernel

/-- The listed inverses and the centralizing equations are exact. -/
theorem conjugator_checks : ∀ j : Fin 16,
    mm (conjugator j) (conjugatorInv j) = ident ∧
    mm (conjugatorInv j) (conjugator j) = ident ∧
    mm (conjugator j) first = mm first (conjugator j) := by decide +kernel

/-- Every candidate is carried to its stated word in the actual pair. -/
theorem candidate_checks : ∀ k : Fin 64,
    mm (mm (conjugator (witness k)) (candidates k)) (conjugatorInv (witness k)) =
      word (words (representative k)) := by decide +kernel

end Representation.Hexacode.SixDimensional.EvenImage.PairData
