module

public import CFSG.Quasithin.ChapterK.Section01To04.SporadicCatalogue.RudvalisExclusion.ModelComparison.Binary
/-!
# Kernel certificates for the marked 4060-point orbit

The column tables are checked against both preserved ATLAS matrices. The
orbit check certifies both generator actions and a left inverse for the point
labels. Finally the basis certificate expresses all 28 coordinate vectors
as sums of selected orbit vectors. No external computation is trusted.

Source: the witness and conventions documented in `Data` and
`../source/README.md`.
-/

@[expose] public section
namespace CFSG.Quasithin.ChapterK.SporadicCatalogue.RudvalisExclusion.ModelComparison
lemma columnsA_size : columnsA.size = 28 := by decide +kernel
lemma columnsB_size : columnsB.size = 28 := by decide +kernel
lemma columnsA_matrix : ∀ i j : Fin 28, matrixA i j = bit columnsA[j.val]! i.val := by
  unfold matrixA bit
  decide +kernel
lemma columnsB_matrix : ∀ i j : Fin 28, matrixB i j = bit columnsB[j.val]! i.val := by
  unfold matrixB bit
  decide +kernel
lemma basisCodes_size : basisCodes.size = 28 := by decide +kernel
lemma basisCodes_eq : ∀ j : Fin 28, basisCodes[j.val]! = orbitCode (basisPoints j) := by
  decide +kernel
lemma basisCoefficients_check : ∀ i : Fin 28,
    packedAction basisCodes (basisCoefficients i) = 2^i.val := by decide +kernel

lemma orbit_check : ∀ i : Fin 4060,
    packedAction columnsA (orbitCode i) = orbitCode (Rudvalis.Data.aMap i) ∧
    packedAction columnsB (orbitCode i) = orbitCode (Rudvalis.Data.bMap i) ∧
    labelOf (orbitCode i) = i.val := by
  apply allOrbit
  rw [checkTree, Bool.and_eq_true]
  constructor <;> rw [checkTree, Bool.and_eq_true]
  all_goals constructor <;> decide +kernel

end CFSG.Quasithin.ChapterK.SporadicCatalogue.RudvalisExclusion.ModelComparison
