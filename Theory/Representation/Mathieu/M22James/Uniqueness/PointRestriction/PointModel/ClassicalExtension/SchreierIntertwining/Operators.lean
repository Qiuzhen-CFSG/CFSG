module
public import Theory.Representation.Mathieu.M22James.Uniqueness.PointRestriction.PointModel.Coordinates
public import Theory.Representation.Mathieu.M22James.Uniqueness.PointRestriction.PointModel.ClassicalExtension.SchreierIntertwining.Words
public import Theory.Representation.Mathieu.M22James.Uniqueness.PointRestriction.PointModel.ClassicalExtension.Multiplication

/-!
# The nineteen classical operators and the whole-space coordinate change

The natural matrices in the three specified field columns have determinant one.
For each such matrix, twelve binary basis-vector identities certify exactly
`Reference.operator`, including its coupling and Frobenius inverse-transpose
blocks. Binary linearity extends these certificates to all vectors. A second
family of small identities checks conjugacy of the actual binary matrices by
`comparisonMatrix`.

The field and binary data are reproduced by `source/generate.py` from the
preserved PointModel diagnostics. ATLAS attribution is retained there and in
`Words.lean`. Source context: James (1973), Lemma 8.3, as used in
Aschbacher–Smith H.12.1, printed pp.393–394. The computations enumerate neither
SL₃(4) nor the module vectors; every identity is checked by the Lean kernel.
-/

@[expose] public noncomputable section
namespace Sporadic.Mathieu.M22TripleCover.Uniqueness.PointRestriction.PointModel
open Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreLinearModel
open scoped Matrix
namespace SchreierCertificate
/-- Natural field matrices read in the specified geometric columns. -/
def naturalMatrix : Fin 19 → Matrix (Fin 3) (Fin 3) Reference.F :=
  ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]],
    ![![0, 1, 1], ![0, 1, 0], ![1, 1, 0]],
    ![![1, (1 + QuadraticAlgebra.omega), (1 + QuadraticAlgebra.omega)], ![0, 0, 1], ![0, 1, 0]],
    ![![QuadraticAlgebra.omega, QuadraticAlgebra.omega, 1], ![0, 0, QuadraticAlgebra.omega], ![(1 + QuadraticAlgebra.omega), 1, 0]],
    ![![0, (1 + QuadraticAlgebra.omega), QuadraticAlgebra.omega], ![(1 + QuadraticAlgebra.omega), (1 + QuadraticAlgebra.omega), 1], ![QuadraticAlgebra.omega, (1 + QuadraticAlgebra.omega), (1 + QuadraticAlgebra.omega)]],
    ![![QuadraticAlgebra.omega, 0, 1], ![(1 + QuadraticAlgebra.omega), 1, 1], ![QuadraticAlgebra.omega, 0, QuadraticAlgebra.omega]],
    ![![1, 0, 0], ![0, 0, QuadraticAlgebra.omega], ![0, (1 + QuadraticAlgebra.omega), 0]],
    ![![0, 0, 1], ![1, QuadraticAlgebra.omega, (1 + QuadraticAlgebra.omega)], ![QuadraticAlgebra.omega, QuadraticAlgebra.omega, QuadraticAlgebra.omega]],
    ![![(1 + QuadraticAlgebra.omega), 1, QuadraticAlgebra.omega], ![0, 1, 0], ![0, 0, QuadraticAlgebra.omega]],
    ![![QuadraticAlgebra.omega, QuadraticAlgebra.omega, (1 + QuadraticAlgebra.omega)], ![(1 + QuadraticAlgebra.omega), 1, 0], ![0, 1, 1]],
    ![![QuadraticAlgebra.omega, 1, (1 + QuadraticAlgebra.omega)], ![1, (1 + QuadraticAlgebra.omega), (1 + QuadraticAlgebra.omega)], ![0, (1 + QuadraticAlgebra.omega), 0]],
    ![![1, 0, 0], ![0, 1, 0], ![1, 1, 1]],
    ![![1, (1 + QuadraticAlgebra.omega), QuadraticAlgebra.omega], ![0, 0, (1 + QuadraticAlgebra.omega)], ![0, QuadraticAlgebra.omega, 0]],
    ![![QuadraticAlgebra.omega, 0, QuadraticAlgebra.omega], ![(1 + QuadraticAlgebra.omega), 1, (1 + QuadraticAlgebra.omega)], ![QuadraticAlgebra.omega, QuadraticAlgebra.omega, 1]],
    ![![QuadraticAlgebra.omega, QuadraticAlgebra.omega, 1], ![1, (1 + QuadraticAlgebra.omega), (1 + QuadraticAlgebra.omega)], ![QuadraticAlgebra.omega, QuadraticAlgebra.omega, (1 + QuadraticAlgebra.omega)]],
    ![![QuadraticAlgebra.omega, QuadraticAlgebra.omega, QuadraticAlgebra.omega], ![0, 1, 0], ![0, 0, (1 + QuadraticAlgebra.omega)]],
    ![![1, 1, (1 + QuadraticAlgebra.omega)], ![(1 + QuadraticAlgebra.omega), QuadraticAlgebra.omega, QuadraticAlgebra.omega], ![(1 + QuadraticAlgebra.omega), QuadraticAlgebra.omega, (1 + QuadraticAlgebra.omega)]],
    ![![1, (1 + QuadraticAlgebra.omega), 0], ![(1 + QuadraticAlgebra.omega), 1, 0], ![0, QuadraticAlgebra.omega, QuadraticAlgebra.omega]],
    ![![QuadraticAlgebra.omega, 1, 0], ![1, QuadraticAlgebra.omega, 0], ![1, QuadraticAlgebra.omega, (1 + QuadraticAlgebra.omega)]]]
private lemma natural_det (k : Fin 19) : (naturalMatrix k).det = 1 := by
  revert k
  decide +kernel
/-- Special linear candidates for the nineteen distinct words. -/
def referenceElement (k : Fin 19) : Reference.SL := ⟨naturalMatrix k, by exact natural_det k⟩
/-- Whole-space reference matrices in interleaved binary coordinates. -/
def operatorMatrix : Fin 19 → Matrix12 :=
  ![fromRows ![1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048],
    fromRows ![20, 40, 4, 8, 5, 10, 1024, 2048, 1344, 2688, 64, 128],
    fromRows ![2685, 3990, 208, 96, 196, 72, 64, 128, 1152, 2240, 384, 704],
    fromRows ![2330, 3631, 864, 432, 2951, 3529, 448, 576, 2624, 3968, 640, 960],
    fromRows ![2860, 3380, 2591, 3877, 2366, 3607, 2112, 3200, 1664, 3008, 3520, 1600],
    fromRows ![530, 803, 1495, 2665, 290, 563, 3776, 1856, 256, 512, 3392, 1664],
    fromRows ![1, 2, 32, 48, 12, 4, 64, 128, 2048, 3072, 768, 256],
    fromRows ![720, 864, 3513, 1758, 2922, 3519, 1728, 2880, 960, 320, 448, 576],
    fromRows ![2343, 3641, 196, 72, 224, 112, 192, 64, 448, 576, 2240, 3136],
    fromRows ![3770, 2015, 455, 585, 1300, 2600, 2624, 3968, 3904, 1408, 2944, 3520],
    fromRows ![3382, 1563, 2685, 3990, 3276, 1092, 2240, 3136, 1216, 2112, 832, 384],
    fromRows ![1025, 2050, 1028, 2056, 341, 682, 1088, 2176, 1280, 2560, 1024, 2048],
    fromRows ![2861, 3382, 176, 208, 200, 76, 64, 128, 3200, 1216, 704, 832],
    fromRows ![1634, 2995, 4023, 1497, 474, 623, 2816, 3328, 2432, 3776, 3264, 1088],
    fromRows ![2970, 3567, 701, 982, 2298, 3167, 2944, 3520, 640, 960, 2240, 3136],
    fromRows ![2602, 3903, 68, 136, 240, 80, 128, 192, 320, 640, 3264, 1088],
    fromRows ![757, 858, 1515, 2685, 1211, 2269, 704, 832, 1472, 2624, 1152, 2240],
    fromRows ![3085, 1030, 1031, 2057, 2600, 3900, 1472, 2624, 3904, 1408, 2048, 3072],
    fromRows ![6, 11, 3081, 1038, 3513, 1758, 576, 896, 3456, 1728, 3072, 1024]]
set_option Elab.async false in
set_option maxRecDepth 4000 in
private lemma operator_basis0 : ∀ l : Fin 12,
    flattenPair (Reference.operator (referenceElement 0) (flattenPair.symm (Pi.single l 1))) =
      operatorMatrix 0 *ᵥ Pi.single l 1 := by decide +kernel

set_option Elab.async false in
set_option maxRecDepth 4000 in
private lemma operator_basis1 : ∀ l : Fin 12,
    flattenPair (Reference.operator (referenceElement 1) (flattenPair.symm (Pi.single l 1))) =
      operatorMatrix 1 *ᵥ Pi.single l 1 := by decide +kernel

set_option Elab.async false in
set_option maxRecDepth 4000 in
private lemma operator_basis2 : ∀ l : Fin 12,
    flattenPair (Reference.operator (referenceElement 2) (flattenPair.symm (Pi.single l 1))) =
      operatorMatrix 2 *ᵥ Pi.single l 1 := by decide +kernel

set_option Elab.async false in
set_option maxRecDepth 4000 in
private lemma operator_basis3 : ∀ l : Fin 12,
    flattenPair (Reference.operator (referenceElement 3) (flattenPair.symm (Pi.single l 1))) =
      operatorMatrix 3 *ᵥ Pi.single l 1 := by decide +kernel

set_option Elab.async false in
set_option maxRecDepth 4000 in
private lemma operator_basis4 : ∀ l : Fin 12,
    flattenPair (Reference.operator (referenceElement 4) (flattenPair.symm (Pi.single l 1))) =
      operatorMatrix 4 *ᵥ Pi.single l 1 := by decide +kernel

set_option Elab.async false in
set_option maxRecDepth 4000 in
private lemma operator_basis5 : ∀ l : Fin 12,
    flattenPair (Reference.operator (referenceElement 5) (flattenPair.symm (Pi.single l 1))) =
      operatorMatrix 5 *ᵥ Pi.single l 1 := by decide +kernel

set_option Elab.async false in
set_option maxRecDepth 4000 in
private lemma operator_basis6 : ∀ l : Fin 12,
    flattenPair (Reference.operator (referenceElement 6) (flattenPair.symm (Pi.single l 1))) =
      operatorMatrix 6 *ᵥ Pi.single l 1 := by decide +kernel

set_option Elab.async false in
set_option maxRecDepth 4000 in
private lemma operator_basis7 : ∀ l : Fin 12,
    flattenPair (Reference.operator (referenceElement 7) (flattenPair.symm (Pi.single l 1))) =
      operatorMatrix 7 *ᵥ Pi.single l 1 := by decide +kernel

set_option Elab.async false in
set_option maxRecDepth 4000 in
private lemma operator_basis8 : ∀ l : Fin 12,
    flattenPair (Reference.operator (referenceElement 8) (flattenPair.symm (Pi.single l 1))) =
      operatorMatrix 8 *ᵥ Pi.single l 1 := by decide +kernel

set_option Elab.async false in
set_option maxRecDepth 4000 in
private lemma operator_basis9 : ∀ l : Fin 12,
    flattenPair (Reference.operator (referenceElement 9) (flattenPair.symm (Pi.single l 1))) =
      operatorMatrix 9 *ᵥ Pi.single l 1 := by decide +kernel

set_option Elab.async false in
set_option maxRecDepth 4000 in
private lemma operator_basis10 : ∀ l : Fin 12,
    flattenPair (Reference.operator (referenceElement 10) (flattenPair.symm (Pi.single l 1))) =
      operatorMatrix 10 *ᵥ Pi.single l 1 := by decide +kernel

set_option Elab.async false in
set_option maxRecDepth 4000 in
private lemma operator_basis11 : ∀ l : Fin 12,
    flattenPair (Reference.operator (referenceElement 11) (flattenPair.symm (Pi.single l 1))) =
      operatorMatrix 11 *ᵥ Pi.single l 1 := by decide +kernel

set_option Elab.async false in
set_option maxRecDepth 4000 in
private lemma operator_basis12 : ∀ l : Fin 12,
    flattenPair (Reference.operator (referenceElement 12) (flattenPair.symm (Pi.single l 1))) =
      operatorMatrix 12 *ᵥ Pi.single l 1 := by decide +kernel

set_option Elab.async false in
set_option maxRecDepth 4000 in
private lemma operator_basis13 : ∀ l : Fin 12,
    flattenPair (Reference.operator (referenceElement 13) (flattenPair.symm (Pi.single l 1))) =
      operatorMatrix 13 *ᵥ Pi.single l 1 := by decide +kernel

set_option Elab.async false in
set_option maxRecDepth 4000 in
private lemma operator_basis14 : ∀ l : Fin 12,
    flattenPair (Reference.operator (referenceElement 14) (flattenPair.symm (Pi.single l 1))) =
      operatorMatrix 14 *ᵥ Pi.single l 1 := by decide +kernel

set_option Elab.async false in
set_option maxRecDepth 4000 in
private lemma operator_basis15 : ∀ l : Fin 12,
    flattenPair (Reference.operator (referenceElement 15) (flattenPair.symm (Pi.single l 1))) =
      operatorMatrix 15 *ᵥ Pi.single l 1 := by decide +kernel

set_option Elab.async false in
set_option maxRecDepth 4000 in
private lemma operator_basis16 : ∀ l : Fin 12,
    flattenPair (Reference.operator (referenceElement 16) (flattenPair.symm (Pi.single l 1))) =
      operatorMatrix 16 *ᵥ Pi.single l 1 := by decide +kernel

set_option Elab.async false in
set_option maxRecDepth 4000 in
private lemma operator_basis17 : ∀ l : Fin 12,
    flattenPair (Reference.operator (referenceElement 17) (flattenPair.symm (Pi.single l 1))) =
      operatorMatrix 17 *ᵥ Pi.single l 1 := by decide +kernel

set_option Elab.async false in
set_option maxRecDepth 4000 in
private lemma operator_basis18 : ∀ l : Fin 12,
    flattenPair (Reference.operator (referenceElement 18) (flattenPair.symm (Pi.single l 1))) =
      operatorMatrix 18 *ᵥ Pi.single l 1 := by decide +kernel

private lemma operator_basis (k : Fin 19) (l : Fin 12) :
    flattenPair (Reference.operator (referenceElement k) (flattenPair.symm (Pi.single l 1))) =
      operatorMatrix k *ᵥ Pi.single l 1 := by
  fin_cases k
  · exact operator_basis0 l
  · exact operator_basis1 l
  · exact operator_basis2 l
  · exact operator_basis3 l
  · exact operator_basis4 l
  · exact operator_basis5 l
  · exact operator_basis6 l
  · exact operator_basis7 l
  · exact operator_basis8 l
  · exact operator_basis9 l
  · exact operator_basis10 l
  · exact operator_basis11 l
  · exact operator_basis12 l
  · exact operator_basis13 l
  · exact operator_basis14 l
  · exact operator_basis15 l
  · exact operator_basis16 l
  · exact operator_basis17 l
  · exact operator_basis18 l

private lemma operator_matrix_of_basis (g : Reference.SL) (a : Matrix12)
    (hb : ∀ l : Fin 12,
      flattenPair (Reference.operator g (flattenPair.symm (Pi.single l 1))) =
        a *ᵥ Pi.single l 1) (v : Reference.V) :
    flattenPair (Reference.operator g v) =
      a *ᵥ flattenPair v := by
  let f : Module.End (ZMod 2) BinarySpace :=
    flattenPair.toLinearMap.comp
      (((Reference.operator g).restrictScalars (ZMod 2)).comp
        flattenPair.symm.toLinearMap)
  have hf : f = a.mulVecLin := by
    apply (Pi.basisFun (ZMod 2) (Fin 12)).ext
    intro l
    simpa only [f, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearMap.restrictScalars_apply, Pi.basisFun_apply, Matrix.mulVecLin_apply]
      using hb l
  have h := LinearMap.congr_fun hf (flattenPair v)
  change flattenPair (Reference.operator g
    (flattenPair.symm (flattenPair v))) = _ at h
  simpa only [flattenPair.symm_apply_apply, Matrix.mulVecLin_apply] using h

/-- Equality on the twelve binary basis vectors gives the complete operator. -/
lemma operator_matrix (k : Fin 19) (v : Reference.V) :
    flattenPair (Reference.operator (referenceElement k) v) =
      operatorMatrix k *ᵥ flattenPair v :=
  operator_matrix_of_basis (referenceElement k) (operatorMatrix k) (operator_basis k) v

set_option Elab.async false in
set_option maxRecDepth 4000 in
private lemma conjugacy0 : comparisonMatrix * schreierMatrix 0 =
    operatorMatrix 0 * comparisonMatrix := by decide +kernel

set_option Elab.async false in
set_option maxRecDepth 4000 in
private lemma conjugacy1 : comparisonMatrix * schreierMatrix 1 =
    operatorMatrix 1 * comparisonMatrix := by decide +kernel

set_option Elab.async false in
set_option maxRecDepth 4000 in
private lemma conjugacy2 : comparisonMatrix * schreierMatrix 2 =
    operatorMatrix 2 * comparisonMatrix := by decide +kernel

set_option Elab.async false in
set_option maxRecDepth 4000 in
private lemma conjugacy3 : comparisonMatrix * schreierMatrix 3 =
    operatorMatrix 3 * comparisonMatrix := by decide +kernel

set_option Elab.async false in
set_option maxRecDepth 4000 in
private lemma conjugacy4 : comparisonMatrix * schreierMatrix 4 =
    operatorMatrix 4 * comparisonMatrix := by decide +kernel

set_option Elab.async false in
set_option maxRecDepth 4000 in
private lemma conjugacy5 : comparisonMatrix * schreierMatrix 5 =
    operatorMatrix 5 * comparisonMatrix := by decide +kernel

set_option Elab.async false in
set_option maxRecDepth 4000 in
private lemma conjugacy6 : comparisonMatrix * schreierMatrix 6 =
    operatorMatrix 6 * comparisonMatrix := by decide +kernel

set_option Elab.async false in
set_option maxRecDepth 4000 in
private lemma conjugacy7 : comparisonMatrix * schreierMatrix 7 =
    operatorMatrix 7 * comparisonMatrix := by decide +kernel

set_option Elab.async false in
set_option maxRecDepth 4000 in
private lemma conjugacy8 : comparisonMatrix * schreierMatrix 8 =
    operatorMatrix 8 * comparisonMatrix := by decide +kernel

set_option Elab.async false in
set_option maxRecDepth 4000 in
private lemma conjugacy9 : comparisonMatrix * schreierMatrix 9 =
    operatorMatrix 9 * comparisonMatrix := by decide +kernel

set_option Elab.async false in
set_option maxRecDepth 4000 in
private lemma conjugacy10 : comparisonMatrix * schreierMatrix 10 =
    operatorMatrix 10 * comparisonMatrix := by decide +kernel

set_option Elab.async false in
set_option maxRecDepth 4000 in
private lemma conjugacy11 : comparisonMatrix * schreierMatrix 11 =
    operatorMatrix 11 * comparisonMatrix := by decide +kernel

set_option Elab.async false in
set_option maxRecDepth 4000 in
private lemma conjugacy12 : comparisonMatrix * schreierMatrix 12 =
    operatorMatrix 12 * comparisonMatrix := by decide +kernel

set_option Elab.async false in
set_option maxRecDepth 4000 in
private lemma conjugacy13 : comparisonMatrix * schreierMatrix 13 =
    operatorMatrix 13 * comparisonMatrix := by decide +kernel

set_option Elab.async false in
set_option maxRecDepth 4000 in
private lemma conjugacy14 : comparisonMatrix * schreierMatrix 14 =
    operatorMatrix 14 * comparisonMatrix := by decide +kernel

set_option Elab.async false in
set_option maxRecDepth 4000 in
private lemma conjugacy15 : comparisonMatrix * schreierMatrix 15 =
    operatorMatrix 15 * comparisonMatrix := by decide +kernel

set_option Elab.async false in
set_option maxRecDepth 4000 in
private lemma conjugacy16 : comparisonMatrix * schreierMatrix 16 =
    operatorMatrix 16 * comparisonMatrix := by decide +kernel

set_option Elab.async false in
set_option maxRecDepth 4000 in
private lemma conjugacy17 : comparisonMatrix * schreierMatrix 17 =
    operatorMatrix 17 * comparisonMatrix := by decide +kernel

set_option Elab.async false in
set_option maxRecDepth 4000 in
private lemma conjugacy18 : comparisonMatrix * schreierMatrix 18 =
    operatorMatrix 18 * comparisonMatrix := by decide +kernel

/-- The fixed coordinate change intertwines each of the nineteen matrices. -/
lemma conjugacy (k : Fin 19) : comparisonMatrix * schreierMatrix k =
    operatorMatrix k * comparisonMatrix := by
  fin_cases k
  · exact conjugacy0
  · exact conjugacy1
  · exact conjugacy2
  · exact conjugacy3
  · exact conjugacy4
  · exact conjugacy5
  · exact conjugacy6
  · exact conjugacy7
  · exact conjugacy8
  · exact conjugacy9
  · exact conjugacy10
  · exact conjugacy11
  · exact conjugacy12
  · exact conjugacy13
  · exact conjugacy14
  · exact conjugacy15
  · exact conjugacy16
  · exact conjugacy17
  · exact conjugacy18

end SchreierCertificate
end Sporadic.Mathieu.M22TripleCover.Uniqueness.PointRestriction.PointModel
