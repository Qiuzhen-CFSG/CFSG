module

public import CFSG.Quasithin.ChapterK.Section01To04.SporadicCatalogue.RudvalisExclusion.ModelComparison.Checks

/-!
# A spanning, injectively labelled orbit for the Rudvalis matrices

The checked binary words decode to 4060 distinct vectors. The column-action
bridge proves equivariance for the actual ATLAS generators. The checked basis
coefficients put every coordinate vector in their span, so they span `Space`.
These three properties are the inputs to the marked group comparison.

Source: the preserved ATLAS matrices and permutation tables, with the
inverse-action convention documented in `../source/README.md`.
-/

@[expose] public section
namespace CFSG.Quasithin.ChapterK.SporadicCatalogue.RudvalisExclusion.ModelComparison

def orbitVector (i : Fin 4060) : Space := bits (orbitCode i)
lemma orbitVector_injective : Function.Injective orbitVector := by
  intro i j hij
  have hcode := bits_injective_bounded
    (Nat.mod_lt _ (by decide) : orbitCode i < 2^28)
    (Nat.mod_lt _ (by decide) : orbitCode j < 2^28) hij
  change orbitCode i = orbitCode j at hcode
  apply Fin.ext
  exact (orbit_check i).2.2.symm.trans ((congrArg labelOf hcode).trans (orbit_check j).2.2)
lemma generatorA_equivariant (i : Fin 4060) :
    generatorA.val (orbitVector i) = orbitVector (Rudvalis.aPerm i) := by
  change Matrix.toLin' matrixA (bits (orbitCode i)) = bits (orbitCode (Rudvalis.Data.aMap i))
  rw [← packedAction_matrix columnsA matrixA columnsA_size columnsA_matrix,
    (orbit_check i).1]
lemma generatorB_equivariant (i : Fin 4060) :
    generatorB.val (orbitVector i) = orbitVector (Rudvalis.bPerm i) := by
  change Matrix.toLin' matrixB (bits (orbitCode i)) = bits (orbitCode (Rudvalis.Data.bMap i))
  rw [← packedAction_matrix columnsB matrixB columnsB_size columnsB_matrix,
    (orbit_check i).2.1]
private lemma coordinate_mem_span (i : Fin 28) :
    Pi.single i (1 : ZMod 2) ∈ Submodule.span (ZMod 2) (Set.range orbitVector) := by
  rw [← bits_two_pow, ← basisCoefficients_check i, bits_packedAction _ basisCodes_size]
  apply Submodule.sum_mem
  intro j _
  apply Submodule.smul_mem
  rw [basisCodes_eq]
  exact Submodule.subset_span ⟨basisPoints j, rfl⟩
lemma orbitVector_span : Submodule.span (ZMod 2) (Set.range orbitVector) = ⊤ := by
  apply top_unique
  rw [← (Pi.basisFun (ZMod 2) (Fin 28)).span_eq]
  apply Submodule.span_le.mpr
  rintro _ ⟨i, rfl⟩
  change (Pi.basisFun (ZMod 2) (Fin 28)) i ∈
    Submodule.span (ZMod 2) (Set.range orbitVector)
  rw [Pi.basisFun_apply]
  exact coordinate_mem_span i
end CFSG.Quasithin.ChapterK.SporadicCatalogue.RudvalisExclusion.ModelComparison

