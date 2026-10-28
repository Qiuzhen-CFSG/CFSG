module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryNormalizerCover.PureTwoA.NativePairCertificates
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.LinearFive.Coordinates

/-!
# A simultaneous-conjugacy invariant for the native pure pair

The rank of `(x - 1)(y - 1)` in the faithful binary representation is
unchanged by simultaneous conjugation. Its checked value is 20 for the
kernel masks 818 and 1449, and 16 for census row 2. This separates those
marked pairs and lets the pure-pair census select row 7.

Source: the native ATLAS coordinates and Kleidman--Wilson (1988), Table 1,
p.487. The certificates are in `NativePairCertificates`.
-/

public noncomputable section
namespace Janko4.LocalStructure.ElementaryNormalizerCover.PureTwoA.NativePair
open Cardinality KernelCount LocalInvolutionCensus
open LocalInvolutionCensus.FiberCensus
open LocalInvolutionCensus.FiberCensus.RepresentativeMatrices
open Janko4.GeneratorCertificates LinearFive
open Simplicity.Max1Fusion.KernelOrbits
open OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData
open LowerBound Coordinates
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 10000
attribute [local irreducible] modelGroup matrixA matrixB max1Subgroup localKernel basis

/-- The rank of the product of the two displacements in the native module. -/
@[expose] def pairRank (x y : Model) : ℕ :=
  ((toMatrix x - 1) * (toMatrix y - 1)).rank

private theorem displacement_conj (g x : Model) :
    toMatrix ((MulAut.conj g) x) - 1 =
      toMatrix g * (toMatrix x - 1) * toMatrix g⁻¹ := by
  change toMatrix (g * x * g⁻¹) - 1 = _
  rw [map_mul, map_mul, mul_sub, sub_mul, mul_one,
    ← map_mul toMatrix g g⁻¹, mul_inv_cancel, map_one]

theorem pairRank_conj (g x y : Model) :
    pairRank ((MulAut.conj g) x) ((MulAut.conj g) y) = pairRank x y := by
  unfold pairRank
  rw [displacement_conj, displacement_conj]
  have hi : toMatrix g⁻¹ * toMatrix g = 1 := by
    rw [← map_mul, inv_mul_cancel, map_one]
  have he : (toMatrix g * (toMatrix x - 1) * toMatrix g⁻¹) *
      (toMatrix g * (toMatrix y - 1) * toMatrix g⁻¹) =
      toMatrix g * ((toMatrix x - 1) * (toMatrix y - 1)) * toMatrix g⁻¹ := by
    calc
      _ = toMatrix g * (toMatrix x - 1) * (toMatrix g⁻¹ * toMatrix g) *
          (toMatrix y - 1) * toMatrix g⁻¹ := by simp only [mul_assoc]
      _ = _ := by rw [hi]; simp only [mul_one, mul_assoc]
  rw [he]
  have hu (v : Model) : IsUnit (toMatrix v).det :=
    ((Group.isUnit v).map toMatrix).map Matrix.detMonoidHom
  rw [Matrix.rank_mul_eq_left_of_isUnit_det _ _ (hu g⁻¹),
    Matrix.rank_mul_eq_right_of_isUnit_det _ _ (hu g)]

private theorem eval_basis (i : Fin 11) :
    toMatrix (kernelValue (2 ^ i.val) : Model) = decodeRows (basisRows i) := by
  change representation matrixA_mul_self matrixB_pow_four
    (maskValue matrixA_mul_self matrixB_pow_four (2 ^ i.val)) = _
  rw [maskValue_basis]
  exact representation_basis matrixA_mul_self matrixB_pow_four i

private theorem eval_xor (m n : ℕ) {rs ss ts : Vector ℕ 112}
    (hm : toMatrix (kernelValue m : Model) = decodeRows rs)
    (hn : toMatrix (kernelValue n : Model) = decodeRows ss)
    (hp : packedMul rs ss = ts) :
    toMatrix (kernelValue (m ^^^ n) : Model) = decodeRows ts := by
  refine (congrArg (fun u : M => toMatrix (u : Model)) (kernelValue_xor m n)).trans ?_
  change toMatrix ((kernelValue m : Model) * (kernelValue n : Model)) = _
  rw [map_mul, hm, hn, ← decode_packedMul, hp]

theorem eval_first : toMatrix (kernelValue 818 : Model) = decodeRows m818Rows := by
  have h18 := eval_xor 2 16 (eval_basis 1) (eval_basis 4) product_m18
  have h50 := eval_xor 18 32 h18 (eval_basis 5) product_m50
  have h306 := eval_xor 50 256 h50 (eval_basis 8) product_m306
  exact eval_xor 306 512 h306 (eval_basis 9) product_m818

theorem eval_second : toMatrix (kernelValue 1449 : Model) = decodeRows m1449Rows := by
  have h9 := eval_xor 1 8 (eval_basis 0) (eval_basis 3) product_m9
  have h41 := eval_xor 9 32 h9 (eval_basis 5) product_m41
  have h169 := eval_xor 41 128 h41 (eval_basis 7) product_m169
  have h425 := eval_xor 169 256 h169 (eval_basis 8) product_m425
  exact eval_xor 425 1024 h425 (eval_basis 10) product_m1449

theorem native_pairRank : pairRank (kernelValue 818) (kernelValue 1449) = 20 := by
  unfold pairRank
  rw [eval_first, eval_second, ← decode_displacement, ← decode_displacement,
    ← decode_packedMul, product_native, native_rank]

theorem row_two_pairRank : pairRank a (eH (representative 2)) = 16 := by
  have ha : a = h⁻¹ * ((sourceSeed ^ 2 : sourceSubgroup) : Model) * h := by
    exact (congrArg eH sourceEquiv_seed_sq).symm.trans
      (eH_sourceSubgroupEquivLocal (sourceSeed ^ 2))
  have hy : eH (representative 2) =
      h⁻¹ * (sourceRepresentative 2 : Model) * h := by
    rw [← sourceEquiv_representative, eH_sourceSubgroupEquivLocal]
  have hr := pairRank_conj h⁻¹ ((sourceSeed ^ 2 : sourceSubgroup) : Model)
    (sourceRepresentative 2 : Model)
  simp only [MulAut.conj_apply, inv_inv] at hr
  rw [← ha, ← hy] at hr
  apply hr.trans
  unfold pairRank
  rw [eval_marked, eval_representative2, ← decode_displacement, ← decode_displacement,
    ← decode_packedMul, product_census, census_rank]

end Janko4.LocalStructure.ElementaryNormalizerCover.PureTwoA.NativePair
