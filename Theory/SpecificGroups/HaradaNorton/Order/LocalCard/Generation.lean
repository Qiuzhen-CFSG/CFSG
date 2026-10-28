module

public import Theory.SpecificGroups.HaradaNorton.Order.LocalCard.MatrixValues
public import Theory.SpecificGroups.HaradaNorton.Order.LocalCard.Generation.Products00
public import Theory.SpecificGroups.HaradaNorton.Order.LocalCard.Generation.Products01
public import Theory.SpecificGroups.HaradaNorton.Order.LocalCard.Generation.Products02
import Mathlib.Tactic.FinCases

/-!
# Generation of the concrete HN local subgroup

The fixed words of lengths five and nineteen recover the original generators
`a` and `localB` from the ten Suzuki words. We certify these equalities in the
original 133-dimensional representation over GF(5), then use its injectivity.
The closure argument in `Words.lean` consequently proves generation without
using any Suzuki presentation relations or an assumed group order.

The words are recorded in `source/candidate-words.json`; the intermediate
matrix certificates are reproduced by `Generation/Generate.py`.
Matrix provenance and attribution: `../../MatrixSources.md`.
-/

public section
namespace HaradaNorton.OrderCertificate

open WordCertificates LocalMatrixValues LocalRecovery

/-- The fixed positive recovery words give the original local generating pair. -/
theorem localSuzukiGen_recovery (i : Fin 2) :
    evalLocalSuzukiWord (localSuzukiRecoveryWords i) = localPair i := by
  fin_cases i
  · apply Subtype.ext
    apply matrixHom_injective
    change matrixHom ((localSuzukiGen 1 : HN) ^ 1 * ((localSuzukiGen 3 : HN) ^ 1 * ((localSuzukiGen 5 : HN) ^ 1 * ((localSuzukiGen 7 : HN) ^ 1 * ((localSuzukiGen 9 : HN) ^ 1 * 1))))) = matrixHom a
    simp only [pow_one, mul_one, map_mul, matrixHom_localSuzukiGen, image_a]
    change decode p057 * (decode p079 * (decode p087 * (decode p103 * (decode p128)))) = decode aPacked
    rw [mul_r0_03, mul_r0_02, mul_r0_01, mul_r0_00]
  · apply Subtype.ext
    apply matrixHom_injective
    change matrixHom ((localSuzukiGen 0 : HN) ^ 1 * ((localSuzukiGen 1 : HN) ^ 1 * ((localSuzukiGen 3 : HN) ^ 1 * ((localSuzukiGen 2 : HN) ^ 1 * ((localSuzukiGen 1 : HN) ^ 1 * ((localSuzukiGen 4 : HN) ^ 1 * ((localSuzukiGen 3 : HN) ^ 1 * ((localSuzukiGen 2 : HN) ^ 1 * ((localSuzukiGen 1 : HN) ^ 1 * ((localSuzukiGen 5 : HN) ^ 1 * ((localSuzukiGen 6 : HN) ^ 1 * ((localSuzukiGen 8 : HN) ^ 1 * ((localSuzukiGen 7 : HN) ^ 1 * ((localSuzukiGen 6 : HN) ^ 1 * ((localSuzukiGen 5 : HN) ^ 1 * ((localSuzukiGen 4 : HN) ^ 1 * ((localSuzukiGen 3 : HN) ^ 1 * ((localSuzukiGen 9 : HN) ^ 1 * ((localSuzukiGen 8 : HN) ^ 1 * 1))))))))))))))))))) = matrixHom localB
    simp only [pow_one, mul_one, map_mul, matrixHom_localSuzukiGen, matrixHom_localB]
    change decode p054 * (decode p057 * (decode p079 * (decode p062 * (decode p057 * (decode p083 * (decode p079 * (decode p062 * (decode p057 * (decode p087 * (decode p097 * (decode p117 * (decode p103 * (decode p097 * (decode p087 * (decode p083 * (decode p079 * (decode p128 * (decode p117)))))))))))))))))) = decode p009
    rw [mul_r1_17, mul_r1_16, mul_r1_15, mul_r1_14, mul_r1_13, mul_r1_12, mul_r1_11, mul_r1_10, mul_r1_09, mul_r1_08, mul_r1_07, mul_r1_06, mul_r1_05, mul_r1_04, mul_r1_03, mul_r1_02, mul_r1_01, mul_r1_00]

/-- The ten fixed Suzuki words generate the actual HN local subgroup. -/
theorem localSuzukiGen_generates :
    Subgroup.closure (Set.range localSuzukiGen) = ⊤ :=
  localSuzukiGen_generates_of_recovery localSuzukiGen_recovery

end HaradaNorton.OrderCertificate
