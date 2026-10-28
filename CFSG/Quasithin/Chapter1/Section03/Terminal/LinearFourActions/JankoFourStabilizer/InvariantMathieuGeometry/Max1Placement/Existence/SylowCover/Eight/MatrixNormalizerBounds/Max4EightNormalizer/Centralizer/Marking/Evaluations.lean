module

public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Eight.MatrixNormalizerBounds.Max4EightNormalizer.Centralizer.Definitions
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Eight.MatrixNormalizerBounds.Max4EightNormalizer.Centralizer.Marking.IntertwiningProducts
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.J4.PairActions.Parity.Conjugacy.SylowCover.MaximalEmbeddings.Max4.NormalEight.Evaluation
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.LowerBound.KernelSeparation.WordEvaluations

/-!
# Evaluating the literal bridge and marked max2 words

The packed certificates are transferred through the faithful matrix map.
The two kernel products retain the increasing-bit order of LowerBound.Source.
The bridge uses exactly the fifth power in Centralizer.Definitions.

Source: retained ATLAS J4G1-f2r112B0, J4G1-max4W1 and J4G1-max2W1 data;
Kleidman–Wilson (1988), pp.484–510; Aschbacher–Smith A.3.12, pp.47–48.
-/

public section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency true
namespace CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover.MatrixNormalizerBounds.Max4EightCentralizer.MarkingCertificates
open Janko4 Janko4.GeneratorCertificates Janko4.LocalStructure.SymmetricLinear
open Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData
open LowerBound LowerBound.KernelSeparation

private theorem eval_mul {g z : Model} {rs ss ts : Vector ℕ 112}
    (hg : toMatrix g = decodeRows rs) (hz : toMatrix z = decodeRows ss)
    (hc : packedMul rs ss = ts) : toMatrix (g * z) = decodeRows ts := by
  rw [map_mul, hg, hz, ← decode_packedMul, hc]

private theorem eval_pow_add {g : Model} {m n : ℕ} {rs ss ts : Vector ℕ 112}
    (hg : toMatrix (g ^ m) = decodeRows rs) (hz : toMatrix (g ^ n) = decodeRows ss)
    (hc : packedMul rs ss = ts) : toMatrix (g ^ (m + n)) = decodeRows ts := by
  rw [pow_add]
  exact eval_mul hg hz hc

private def r : Model := (NormalEight.element 2 : Model) * a

private theorem eval_r : toMatrix r = decodeRows rRows :=
  eval_mul (NormalEight.matrix_element 2) (show toMatrix a = decodeRows aRows from rfl)
    check_r

private theorem eval_r2 : toMatrix (r ^ 2) = decodeRows r2Rows := by
  rw [pow_two]
  exact eval_mul eval_r eval_r check_r2

private theorem eval_r4 : toMatrix (r ^ 4) = decodeRows r4Rows :=
  eval_pow_add (g := r) (m := 2) (n := 2) eval_r2 eval_r2 check_r4

private theorem eval_c : toMatrix (r ^ 5) = decodeRows cRows := by
  rw [pow_succ]
  exact eval_mul eval_r4 eval_r check_c

theorem eval_bridge : toMatrix bridge = decodeRows bridgeRows :=
  eval_mul eval_h eval_c check_bridge

-- Keep the matrix maps at their proved interfaces during word evaluation.
attribute [local irreducible] decodeRows toMatrix

private theorem eval_kernelProduct (i : Fin 8192) :
    toMatrix (kernelProduct i : Model) =
      (List.ofFn (fun j : Fin 13 =>
        if i.val.testBit j.val then decodeRows (factorRows j) else 1)).prod := by
  change (toMatrix.comp sourceSubgroup.subtype) (kernelProduct i) = _
  rw [kernelProduct, map_list_prod, List.map_ofFn]
  apply congrArg List.prod
  apply congrArg List.ofFn
  funext j
  dsimp only [Function.comp_apply]
  split_ifs
  · exact eval_factor j
  · exact map_one _

private theorem decoded_chain {xs zs ts : Vector ℕ 112} {ys : BinaryMatrix}
    (hy : ys = decodeRows zs) (hc : packedMul xs zs = ts) :
    decodeRows xs * ys = decodeRows ts :=
  (congrArg (fun y => decodeRows xs * y) hy).trans
    ((decode_packedMul xs zs).symm.trans (congrArg decodeRows hc))

private theorem mask_product_6607 {M : Type*} [Monoid M] (f : Fin 13 → M) :
    (List.ofFn (fun j : Fin 13 => if (6607 : Fin 8192).val.testBit j.val then f j else 1)).prod =
      f 0 * (f 1 * (f 2 * (f 3 * (f 6 * (f 7 * (f 8 * (f 11 * (f 12)))))))) := by
  change (List.prod [f 0, f 1, f 2, f 3, 1, 1, f 6, f 7, f 8, 1, 1, f 11, f 12]) = _
  simp only [List.prod_cons, List.prod_nil, one_mul, mul_one]

private theorem mask_product_3400 {M : Type*} [Monoid M] (f : Fin 13 → M) :
    (List.ofFn (fun j : Fin 13 => if (3400 : Fin 8192).val.testBit j.val then f j else 1)).prod =
      f 3 * (f 6 * (f 8 * (f 10 * (f 11)))) := by
  change (List.prod [1, 1, 1, f 3, 1, 1, f 6, 1, f 8, 1, f 10, f 11, 1]) = _
  simp only [List.prod_cons, List.prod_nil, one_mul, mul_one]

theorem eval_sourceP : toMatrix (sourceP : Model) = decodeRows p6607Rows := by
  refine (eval_kernelProduct 6607).trans ?_
  refine (mask_product_6607 (fun j => decodeRows (factorRows j))).trans ?_
  exact (decoded_chain (decoded_chain (decoded_chain (decoded_chain (decoded_chain (decoded_chain (decoded_chain (decoded_chain rfl check_p6144) check_p6400) check_p6528) check_p6592) check_p6600) check_p6604) check_p6606) check_p6607)

theorem eval_sourceQ : toMatrix (sourceQ : Model) = decodeRows q3400Rows := by
  refine (eval_kernelProduct 3400).trans ?_
  refine (mask_product_3400 (fun j => decodeRows (factorRows j))).trans ?_
  exact (decoded_chain (decoded_chain (decoded_chain (decoded_chain rfl check_q3072) check_q3328) check_q3392) check_q3400)


end CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover.MatrixNormalizerBounds.Max4EightCentralizer.MarkingCertificates
