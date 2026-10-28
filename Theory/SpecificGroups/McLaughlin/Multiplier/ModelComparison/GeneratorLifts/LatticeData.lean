/-
The Golay and Leech congruence certificates below are checked in Lean's kernel.
The displayed data are adapted from the ATLAS McLaughlin matrix calculation;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module
public import Theory.SpecificGroups.McLaughlin.Multiplier.ModelComparison.GeneratorLifts.RationalMaps
public import Theory.SpecificGroups.McLaughlin.Multiplier.ModelComparison.Action
public import Theory.AtlasPort.OtherSporadic.Lattices.LeechGeneratorCriterion
@[expose] public section
noncomputable section
namespace Theory.SpecificGroups.McLaughlin.Multiplier.ModelComparison
open Atlas.Codes Atlas.Lattices Atlas.Conway
open scoped Matrix BigOperators
set_option maxRecDepth 100000
def wordOfMask (k : ℕ) : BinaryWord :=
  ∑ i : Fin 12, if (k >>> i.val) % 2 = 1 then golayGenerators i else 0

theorem wordOfMask_mem (k : ℕ) : wordOfMask k ∈ golay := by
  apply golay.sum_mem
  intro i hi
  split
  · rw [← golayBasis_coe]
    exact (golayBasis i).property
  · exact golay.zero_mem

theorem leech_of_certificate (v : Fin 24 → ℤ) (m : ℤ) (k : ℕ)
    (hm : m = 0 ∨ m = 1)
    (hp : ∀ i : Omega, vectorOfData v i % 2 = m)
    (hr : halfResidue (vectorOfData v) m = wordOfMask k)
    (hs : (∑ i : Omega, vectorOfData v i) % 8 = 4 * m) :
    vectorOfData v ∈ leech := by
  rw [mem_leech]
  exact ⟨m,hm,hp,hr ▸ wordOfMask_mem k,hs⟩

def sourceParity : Fin 37 → ℤ := ![1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def sourceCoeffs : Fin 37 → ℕ := ![0,1,2,4,8,16,32,64,128,256,512,1024,2048,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def imageAParity : Fin 37 → ℤ := ![1,1,0,1,0,1,0,0,0,0,1,1,0,0,1,1,1,1,1,1,1,1,1,1,1,1,0,0,1,0,0,1,0,1,1,0,0]
def imageACoeffs : Fin 37 → ℕ := ![1052,43,3403,3707,200,58,568,64,128,136,2718,3786,3065,1052,3278,3738,1958,1210,4087,3427,3491,3895,1582,1330,3462,4050,1052,0,1495,1052,1052,1119,1052,1303,1183,1052,1052]
def imageAInvParity : Fin 37 → ℤ := ![1,1,0,1,0,1,0,0,0,0,1,1,0,0,1,1,1,1,1,1,1,1,1,1,1,1,0,0,1,0,0,1,0,1,1,0,0]
def imageAInvCoeffs : Fin 37 → ℕ := ![1052,43,3403,3707,200,58,568,64,128,136,2718,3786,3065,1052,3278,3738,1958,1210,4087,3427,3491,3895,1582,1330,3462,4050,1052,0,1495,1052,1052,1119,1052,1303,1183,1052,1052]
def imageBParity : Fin 37 → ℤ := ![0,0,1,1,1,0,1,1,1,0,1,0,0,1,0,1,1,0,1,0,0,0,0,0,1,1,0,0,0,0,0,0,0,0,1,1,1]
def imageBCoeffs : Fin 37 → ℕ := ![48,267,3005,2564,2551,379,3000,3538,81,132,3020,315,3014,2032,1028,618,2032,1061,2120,3523,3039,2724,128,101,1898,1524,258,514,264,3023,3048,177,3027,753,1976,3844,48]
def imageBInvParity : Fin 37 → ℤ := ![0,0,1,1,1,0,0,0,1,1,0,1,1,1,1,0,0,0,1,1,0,1,0,1,0,0,0,0,0,1,0,1,0,0,0,0,1]
def imageBInvCoeffs : Fin 37 → ℕ := ![345,3065,3451,3400,1212,780,2663,528,1696,3328,3037,1268,101,1689,1768,1253,101,80,1128,201,2720,1745,2492,1689,2470,891,1399,2878,119,2339,123,3515,64,4024,2724,456,345]

theorem mapA_source (j : Fin 37) :
    mapA (rationalEmbedding (vectorOfData (sourceVectors j))) =
      rationalEmbedding (vectorOfData (imageAVectors j)) := by
  have h : ∀ j : Fin 37,
      mapA (rationalEmbedding (vectorOfData (sourceVectors j))) =
        rationalEmbedding (vectorOfData (imageAVectors j)) := by
    decide +kernel
  exact h j

theorem mapA_inverse_source (j : Fin 37) :
    mapA.symm (rationalEmbedding (vectorOfData (sourceVectors j))) =
      rationalEmbedding (vectorOfData (imageAInvVectors j)) := by
  have h : ∀ j : Fin 37,
      mapA.symm (rationalEmbedding (vectorOfData (sourceVectors j))) =
        rationalEmbedding (vectorOfData (imageAInvVectors j)) := by
    decide +kernel
  exact h j

theorem mapB_source (j : Fin 37) :
    mapB (rationalEmbedding (vectorOfData (sourceVectors j))) =
      rationalEmbedding (vectorOfData (imageBVectors j)) := by
  have h : ∀ j : Fin 37,
      mapB (rationalEmbedding (vectorOfData (sourceVectors j))) =
        rationalEmbedding (vectorOfData (imageBVectors j)) := by
    decide +kernel
  exact h j

theorem mapB_inverse_source (j : Fin 37) :
    mapB.symm (rationalEmbedding (vectorOfData (sourceVectors j))) =
      rationalEmbedding (vectorOfData (imageBInvVectors j)) := by
  have h : ∀ j : Fin 37,
      mapB.symm (rationalEmbedding (vectorOfData (sourceVectors j))) =
        rationalEmbedding (vectorOfData (imageBInvVectors j)) := by
    decide +kernel
  exact h j



theorem certificate_mem (v : Fin 24 → ℤ) (m : ℤ) (k : ℕ)
    (hp : ∀ i : Omega, vectorOfData v i % 2 = m)
    (hr : halfResidue (vectorOfData v) m = wordOfMask k)
    (hs : (∑ i : Omega, vectorOfData v i) % 8 = 4 * m) :
    vectorOfData v ∈ leech :=
  leech_of_certificate v m k (by omega) hp hr hs


end Theory.SpecificGroups.McLaughlin.Multiplier.ModelComparison
