module

public import Theory.SpecificGroups.Janko4.Model.LocalStructure.MathieuSeedCentralizer.KernelBound.RestrictionRigidity.Separation.Finite.WeightTransposeRows
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.MathieuSeedCentralizer.KernelBound.RestrictionRigidity.Separation.Finite.SymWeightRows
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.MathieuSeedCentralizer.KernelBound.RestrictionRigidity.Separation.Finite.Values

/-!
# Finite evaluations and pair coverage

The weights plus their transposes evaluate polarized products. The triangular
index covers every pair with the second index at most the first, including
each diagonal. A checked XOR identity reconstructs the last square-basis
operator from the first 44 operators and the exact top operator.

Source: KernelBound/source/README.md and kernel-restriction.json. Numerical
witnesses are checked by Lean; the generator is not trusted.
-/

@[expose] public section
open Matrix
open scoped Matrix
namespace Janko4.LocalStructure.MathieuSeedCentralizer.KernelBound.RestrictionRigidity.SeparationCertificate
open Coordinates GeneratorCertificates
open OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound.OrbitCoverCoordinates
open PolynomialCertificate.ExteriorAnnihilators PolynomialCertificate.PullbackCoefficients ExteriorInvariance

set_option maxRecDepth 10000
set_option Elab.async false
attribute [local irreducible] symWeights weights linearWords productWords productPairs survivor
  alternativeBasisWords squareBasis topOperator testForm weightTransposes

theorem symWeights_spec (k : Fin 44) : decodeHalf (symWeights.get k) =
    decodeHalf (weights.get k.castSucc) + (decodeHalf (weights.get k.castSucc))ᵀ := by
  have ht := transposeRows_of_check (halfRows (weights.get k.castSucc)) (weightTransposes.get k) (weightTransposeRows_check k)
  have ha := addRows_of_check (n := 56) (halfRows (weights.get k.castSucc)) (weightTransposes.get k)
    (halfRows (symWeights.get k)) (symWeightRows_check k)
  rw [ht, halfRows_spec, halfRows_spec] at ha
  exact ha

private theorem triangular_list : productPairs.toList =
    (List.ofFn (fun i : Fin 45 => List.ofFn (fun j : Fin (i.val+1) =>
      (i, (⟨j.val, by omega⟩ : Fin 45))))).flatten := by
  decide +kernel

theorem pair_coverage (i j : Fin 45) (h : j ≤ i) :
    ∃ p : Fin 1035, productPairs.get p = (i,j) := by
  have hm : (i,j) ∈ productPairs.toList := by
    rw [triangular_list]
    apply List.mem_flatten.mpr
    refine ⟨_, List.mem_ofFn.mpr ⟨i, rfl⟩, ?_⟩
    exact List.mem_ofFn.mpr ⟨⟨j.val, by omega⟩, rfl⟩
  obtain ⟨p, hp, he⟩ := Vector.mem_iff_getElem.mp (Vector.mem_toList_iff.mp hm)
  exact ⟨⟨p,hp⟩, he⟩

theorem survivor_relation :
    (∑ k : Fin 44, bit survivor k.val • squareBasis k.castSucc) + topOperator = squareBasis 44 := by
  have h : xorList (List.ofFn (fun k : Fin 44 => if survivor.testBit k.val then
      alternativeBasisWords.get ⟨k.val+11, by omega⟩ else 0)) ^^^ topOperatorWord =
        alternativeBasisWords.get 55 := by decide +kernel
  have he := congrArg decodeHalf h
  rw [decodeHalf_xor, decodeHalf_xorList, List.map_ofFn, List.sum_ofFn] at he
  have hz : decodeHalf 0 = 0 := by
    funext i j
    simp only [decodeHalf, bit, Nat.zero_testBit, Bool.false_eq_true, if_false,
      Matrix.zero_apply]
  have hs : (∑ k : Fin 44, bit survivor k.val • squareBasis k.castSucc) =
      ∑ k : Fin 44, decodeHalf (if survivor.testBit k.val then
        alternativeBasisWords.get ⟨k.val+11, by omega⟩ else 0) := by
    apply Finset.sum_congr rfl
    intro k _
    cases ht : survivor.testBit k.val <;>
      simp only [bit, ht, Bool.false_eq_true, if_false, if_true,
        zero_smul, one_smul, hz, squareBasis, alternativeBasis, Fin.val_castSucc]
  rw [hs]
  simp only [topOperator, squareBasis, alternativeBasis]
  change (∑ k : Fin 44, decodeHalf (if survivor.testBit k.val then
    alternativeBasisWords.get ⟨k.val+11, by omega⟩ else 0)) + decodeHalf topOperatorWord =
      decodeHalf (alternativeBasisWords.get 55)
  exact he

end Janko4.LocalStructure.MathieuSeedCentralizer.KernelBound.RestrictionRigidity.SeparationCertificate
