module

public import Theory.SpecificGroups.ONan.E9A4.WordMatrices.Values
public import Theory.SpecificGroups.ONan.E9A4.WordMatrices.Words
import Mathlib.Tactic.FinCases

/-!
# Exact linear matrices of the O'Nan E₉ × A₄ candidate words

The four fixed words in the published 45-dimensional GF(7) generators have
exactly the matrices in `E9A4.Data`. Balanced product certificates, including
right-inverse witnesses, establish each matrix value by kernel checking.
Group associativity then identifies the balanced expressions with the literal
ATLAS max5 program and signed local words of `E9A4.Words`.

This supplies the linear-realization premise of the separate projective-table
argument. No order, simplicity, or subgroup identification is assumed.
Sources and attribution: `E9A4/source/README.md`, `refs/original/onan/`, and
`WordMatrices/source/README.md`; the local application is Aschbacher--Smith,
*The Classification of Quasithin Groups*, A.2.19, printed p. 41.
-/

namespace ONan.E9A4

/-- The fixed signed words realize the four candidate matrices exactly in GL(45,7). -/
public theorem linearGenerators_matrix (i : Fin 4) :
    (linearGenerators i : Mat) = Data.generatorMatrix i := by
  fin_cases i
  · change (linearGenerators 0 : Mat) = Data.gen0
    rw [WordCertificate.generator0_eq]
    exact WordCertificate.value_part8
  · change (linearGenerators 1 : Mat) = Data.gen1
    rw [WordCertificate.generator1_eq]
    exact WordCertificate.value_part16
  · change (linearGenerators 2 : Mat) = Data.gen2
    rw [WordCertificate.generator2_eq]
    exact WordCertificate.value_part30
  · change (linearGenerators 3 : Mat) = Data.gen3
    rw [WordCertificate.generator3_eq]
    exact WordCertificate.value_part37

end ONan.E9A4
