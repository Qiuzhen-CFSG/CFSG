module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.LargeCenterRadicals.OuterHalf.FirstPairProducts
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.LargeCenterRadicals.OuterHalf.InnerHalves
import Mathlib.Tactic.FinCases
/-!
# An actual reverse-character calculation for the first centralizer census

The dihedral word used for census representative 2 simultaneously sends that
representative to the source central involution and the central involution to
kernel word 5722. The twelve packed products in `FirstPairProducts` prove
these identities in the native J4 carrier. Both elements therefore lie in the
residual of the other's full centralizer. The final theorem transports this
to the whole conjugacy class inside the first centralizer, retaining its
local conjugator and the literal census embedding.

Source: Kleidman--Wilson (1988), p.487, Lemma 1.1.3 and Corollary 1.1.4.
This proves one of the finite comparisons needed for the intrinsic symmetry;
it does not assert the remaining comparisons or the global radical cover.
The imported matrix and word data retain the ATLAS attribution in
LocalInvolutionCensus/Fusion/source/README.md.
-/

set_option backward.isDefEq.respectTransparency true
@[expose] public noncomputable section
namespace Janko4.LocalStructure.LargeCenterRadicals.ReverseCertificate
open Janko4.GeneratorCertificates
open Janko4.Cardinality.LocalInvolutionCensus.FusionCertificates
open Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData
open LowerBound KernelSeparation
open Janko4.Cardinality.KernelCount.Relations
attribute [local irreducible] modelGroup matrixA matrixB sourceSubgroup kernelProduct kernelFactor

noncomputable def conjugator : Model :=
  h * Janko4.b ^ 2 *
    ((sourceRepresentative 2 : Model) *
      (Janko4.b ^ 2 * Janko4.a * (Janko4.b ^ 2)⁻¹)) ^ 5

attribute [local irreducible] conjugator sourceRepresentative

theorem eval_conjugator : toMatrix conjugator = decodeRows conjugatorRows := by
  have hb : toMatrix (Janko4.b ^ 2) = decodeRows bSquareRows := by
    rw [map_pow, pow_two, toMatrix_b]
    unfold matrixB
    exact decoded_product Common.product_10
  have hr : toMatrix ((sourceRepresentative 2 : Model) *
      (Janko4.b ^ 2 * Janko4.a * (Janko4.b ^ 2)⁻¹)) = decodeRows odd0_2Rows := by
    rw [map_mul, eval_rep_2, eval_bbzaRows, decoded_product Case0_2.product_01]
  have h2 : decodeRows odd0_2Rows ^ 2 = decodeRows odd0_2RowsP2 := by
    rw [pow_two, decoded_product Case0_2.product_02]
  have h4 : decodeRows odd0_2Rows ^ 4 = decodeRows odd0_2RowsP4 := by
    rw [show 4 = 2+2 from rfl, pow_add, h2, decoded_product Case0_2.product_03]
  have h5 : decodeRows odd0_2Rows ^ 5 = decodeRows odd0_2RowsP5 := by
    rw [pow_succ, h4, decoded_product Case0_2.product_04]
  rw [conjugator, map_mul, map_mul, eval_h, hb, map_pow, hr, h5,
    decoded_product product_00, decoded_product product_01]

private theorem expand_mask {M : Type*} [Monoid M] (e : Fin 13 → M) :
    (List.ofFn (fun j : Fin 13 => if (5722 : ℕ).testBit j.val then e j else 1)).prod =
      e 1 * (e 3 * (e 4 * (e 6 * (e 9 * (e 10 * e 12))))) := by
  have hv : (fun j : Fin 13 => if (5722 : ℕ).testBit j.val then e j else 1) =
      ![1,e 1,1,e 3,e 4,1,e 6,1,1,e 9,e 10,1,e 12] := by
    funext j
    fin_cases j <;> rfl
  rw [hv]
  simp [List.ofFn_succ]

theorem eval_kernel_5722 : toMatrix (kernelProduct 5722 : Model) =
    decodeRows kernel5722At1Rows := by
  have hk : kernelProduct 5722 =
      kernelFactor 1 * (kernelFactor 3 * (kernelFactor 4 * (kernelFactor 6 *
        (kernelFactor 9 * (kernelFactor 10 * kernelFactor 12))))) := by
    rw [kernelProduct, show (5722 : Fin 8192).val = 5722 from rfl]
    exact expand_mask kernelFactor
  rw [hk]
  simp only [Subgroup.coe_mul, map_mul, eval_factor]
  rw [decoded_product product_04, decoded_product product_05,
    decoded_product product_06, decoded_product product_07,
    decoded_product product_08, decoded_product product_09]

private theorem kernelFactor_zero : kernelFactor 0 = sourceSeed ^ 2 := by
  unfold kernelFactor
  rfl

theorem conjugator_first :
    conjugator * (sourceRepresentative 2 : Model) * conjugator⁻¹ =
      ((sourceSeed ^ 2 : sourceSubgroup) : Model) := by
  rw [←kernelFactor_zero]
  apply mul_inv_eq_iff_eq_mul.mpr
  apply toMatrix_injective
  rw [map_mul, map_mul, eval_conjugator, eval_rep_2]
  rw [eval_factor, decoded_product product_02, decoded_product product_03]

theorem conjugator_second :
    conjugator * ((sourceSeed ^ 2 : sourceSubgroup) : Model) * conjugator⁻¹ =
      (kernelProduct 5722 : Model) := by
  rw [←kernelFactor_zero]
  apply mul_inv_eq_iff_eq_mul.mpr
  apply toMatrix_injective
  rw [map_mul, map_mul, eval_conjugator, eval_kernel_5722]
  rw [eval_factor, decoded_product product_10, decoded_product product_11]
end Janko4.LocalStructure.LargeCenterRadicals.ReverseCertificate

public noncomputable section
open Subgroup Theory.GroupTheory
namespace Janko4.LocalStructure.LargeCenterRadicals.OuterHalf
attribute [local irreducible] Janko4.modelGroup Janko4.matrixA Janko4.matrixB
open Janko4.OuterReduction.FixedGenerator.NormalizerSquares
open TwoCoreCentralizerData LowerBound
open Janko4.Cardinality.LocalInvolutionCensus

private theorem localKernelProduct_mem (i : Fin 8192) :
    Coordinates.localKernelProduct i ∈ localNormalClosure := by
  apply (QuotientGroup.eq_one_iff _).mp
  let f := (QuotientGroup.mk' localNormalClosure).comp sourceSubgroupEquivLocal.toMonoidHom
  have hs : f sourceSeed = 1 := by
    change QuotientGroup.mk' localNormalClosure (sourceSubgroupEquivLocal sourceSeed) = 1
    rw [Coordinates.sourceEquiv_seed]
    exact (QuotientGroup.eq_one_iff _).mpr localSeed_mem_normalClosure
  exact map_kernelProduct_eq_one f hs i

theorem innerRelated_a_kernel (i : Fin 8192) :
    InnerRelated Janko4.a (eH (Coordinates.localKernelProduct i)) := by
  let u := Coordinates.localKernelProduct i
  have hu : (u : involutionCentralizer) ∈ involutionTwoCore := by
    rw [← InvolutionCentralizers.First.normalClosureImage_eq_twoCore]
    exact ⟨u, localKernelProduct_mem i, rfl⟩
  let q := InvolutionCentralizers.First.twoCoreEquiv.symm ⟨u, hu⟩
  refine ⟨q.val, InvolutionCentralizers.First.twoCore_le_residual q.property, ?_⟩
  apply toAmbient_injective
  change toAmbient (q.val : Model) = toAmbient (eH u)
  rw [← InvolutionCentralizers.First.centralizerEquiv_coe q.val,
    ← InvolutionCentralizers.First.twoCoreEquiv_coe q]
  have hq : (InvolutionCentralizers.First.twoCoreEquiv q : involutionCentralizer) = u :=
    congrArg Subtype.val
      (InvolutionCentralizers.First.twoCoreEquiv.apply_symm_apply ⟨u, hu⟩)
  exact congrArg (fun z : involutionCentralizer => (z : BinaryMatrixˣ)) hq

theorem innerRelated_source_kernel (i : Fin 8192) :
    InnerRelated ((sourceSeed ^ 2 : sourceSubgroup) : Model) (kernelProduct i) := by
  apply (innerRelated_equiv (MulAut.conj h⁻¹) _ _).mp
  have hs : (MulAut.conj h⁻¹) ((sourceSeed ^ 2 : sourceSubgroup) : Model) = Janko4.a := by
    simpa only [MulAut.conj_apply, inv_inv, coe_sourceSeed_sq] using conjugates_t
  rw [hs]
  have he := eH_sourceSubgroupEquivLocal (kernelProduct i)
  change eH (Coordinates.localKernelProduct i) = _ at he
  simpa only [MulAut.conj_apply, inv_inv, ←he] using innerRelated_a_kernel i

open Janko4.Cardinality.LocalInvolutionCensus.FusionCertificates
open ReverseCertificate

/-- Both directions for the literal source-word census pair. -/
theorem source_pair_inner :
    InnerRelated ((sourceSeed ^ 2 : sourceSubgroup) : Model) (sourceRepresentative 2) ∧
      InnerRelated (sourceRepresentative 2) ((sourceSeed ^ 2 : sourceSubgroup) : Model) := by
  constructor
  · have hu : sourceRepresentative 2 = kernelProduct 6 := by
      change kernelProduct 6 * 1 = kernelProduct 6
      exact mul_one _
    rw [hu]
    exact innerRelated_source_kernel 6
  · apply (innerRelated_equiv (MulAut.conj conjugator) _ _).mp
    simpa only [MulAut.conj_apply, conjugator_first, conjugator_second] using
      innerRelated_source_kernel 5722

/-- The two inner-half memberships in the actual first-centralizer census. -/
theorem first_pair_inner :
    InnerRelated Janko4.a (eH (representative 2)) ∧
      InnerRelated (eH (representative 2)) Janko4.a := by
  have hs : (MulAut.conj h⁻¹) ((sourceSeed ^ 2 : sourceSubgroup) : Model) = Janko4.a := by
    simpa only [MulAut.conj_apply, inv_inv, coe_sourceSeed_sq] using conjugates_t
  have hu : (MulAut.conj h⁻¹) (sourceRepresentative 2 : Model) =
      eH (representative 2) := by
    rw [representative_eq, eH_sourceSubgroupEquivLocal, MulAut.conj_apply, inv_inv]
  constructor
  · simpa only [MulEquiv.coe_toMonoidHom, hs, hu] using innerRelated_map (MulAut.conj h⁻¹).toMonoidHom source_pair_inner.1
  · simpa only [MulEquiv.coe_toMonoidHom, hs, hu] using innerRelated_map (MulAut.conj h⁻¹).toMonoidHom source_pair_inner.2

/-- Every member of this whole local conjugacy class satisfies the intrinsic
symmetry with both values in the inner halves. The conjugator stays in C(a). -/
theorem first_pair_class_inner (u : H) (hu : IsConj (representative 2) u) :
    InnerRelated Janko4.a (eH u) ∧ InnerRelated (eH u) Janko4.a := by
  obtain ⟨g, hg⟩ := isConj_iff.mp hu
  have ha : (MulAut.conj (eH g)) Janko4.a = Janko4.a := by
    have hc := (eH_commute_z g).eq
    change eH g * Janko4.a = Janko4.a * eH g at hc
    change eH g * Janko4.a * (eH g)⁻¹ = Janko4.a
    rw [hc, mul_inv_cancel_right]
  have hv : (MulAut.conj (eH g)) (eH (representative 2)) = eH u := by
    simpa only [map_mul, map_inv, MulAut.conj_apply] using congrArg eH hg
  constructor
  · simpa only [MulEquiv.coe_toMonoidHom, ha, hv] using
      innerRelated_map (MulAut.conj (eH g)).toMonoidHom first_pair_inner.1
  · simpa only [MulEquiv.coe_toMonoidHom, ha, hv] using
      innerRelated_map (MulAut.conj (eH g)).toMonoidHom first_pair_inner.2

end Janko4.LocalStructure.LargeCenterRadicals.OuterHalf
