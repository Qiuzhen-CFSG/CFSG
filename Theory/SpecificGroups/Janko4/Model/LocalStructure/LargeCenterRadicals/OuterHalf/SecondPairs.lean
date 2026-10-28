module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.LargeCenterRadicals.OuterHalf.SecondPairsProducts
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.LargeCenterRadicals.OuterHalf.FirstPair
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.LargeCenterRadicals.OuterHalf.ElementaryForm

/-!
# Two further native commuting-involution comparisons

The checked conjugators send census representatives 3 and 9 to the actual
second central involution, and the source central involution to kernel words
82 and 996. The full second-centralizer residual contains that elementary
kernel. In the forward direction, representative 3 is a first-core word;
representative 9 is a first-core word times a fourth power, hence belongs to
the actual index-two residual. Both comparisons are transported through the
literal embedding and every local conjugator.

Source: Kleidman--Wilson (1988), p.487, Lemma 1.1.3 and Corollary 1.1.4.
This closes these two pair classes only. Full commuting-involution symmetry
and native radical coverage remain separate obligations. Matrix data and
ATLAS attribution are retained through `SecondPairsProducts`.
-/

set_option backward.isDefEq.respectTransparency true
@[expose] public noncomputable section
namespace Janko4.LocalStructure.LargeCenterRadicals.SecondReverseCertificate
open Janko4.GeneratorCertificates
open Janko4.Cardinality.LocalInvolutionCensus.FusionCertificates
open Janko4.Cardinality.KernelCount
open Janko4.Cardinality.KernelCount.Relations (decoded_product)
open Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData
open LowerBound KernelSeparation
attribute [local irreducible] modelGroup matrixA matrixB sourceSubgroup sourceRepresentative
  Janko4.Cardinality.localKernelSeed Janko4.Cardinality.max1Subgroup

def secondWord3 : InvolutionCentralizers.Second.Local :=
  basis matrixA_mul_self matrixB_pow_four 1 *
    (basis matrixA_mul_self matrixB_pow_four 4 * basis matrixA_mul_self matrixB_pow_four 6)

def secondWord9 : InvolutionCentralizers.Second.Local :=
  basis matrixA_mul_self matrixB_pow_four 2 *
    (basis matrixA_mul_self matrixB_pow_four 5 *
      (basis matrixA_mul_self matrixB_pow_four 6 *
        (basis matrixA_mul_self matrixB_pow_four 7 *
          (basis matrixA_mul_self matrixB_pow_four 8 * basis matrixA_mul_self matrixB_pow_four 9))))

theorem secondWord3_mem : secondWord3 ∈ InvolutionCentralizers.Second.max1Kernel := by
  unfold secondWord3
  exact Subgroup.mul_mem _ (basis_mem_localKernel _ _ _) (Subgroup.mul_mem _
    (basis_mem_localKernel _ _ _) (basis_mem_localKernel _ _ _))

theorem secondWord9_mem : secondWord9 ∈ InvolutionCentralizers.Second.max1Kernel := by
  unfold secondWord9
  repeat' first | exact basis_mem_localKernel _ _ _ | apply Subgroup.mul_mem

theorem eval_secondWord3 : toMatrix (secondWord3 : Model) = decodeRows kernel82At1Rows := by
  change representation _ _ secondWord3 = _
  simp only [secondWord3, map_mul, representation_basis]
  change decodeRows e1Rows * (decodeRows e4Rows * decodeRows e6Rows) = _
  rw [decoded_product product_02, decoded_product product_03]

theorem eval_secondWord9 : toMatrix (secondWord9 : Model) = decodeRows kernel996At2Rows := by
  change representation _ _ secondWord9 = _
  simp only [secondWord9, map_mul, representation_basis]
  change decodeRows e2Rows * (decodeRows e5Rows * (decodeRows e6Rows *
    (decodeRows e7Rows * (decodeRows e8Rows * decodeRows e9Rows)))) = _
  rw [decoded_product product_08, decoded_product product_09, decoded_product product_10,
    decoded_product product_11, decoded_product product_12]

def conjugator3 : Model := ((sourceRepresentative 3 : Model) * InvolutionCentralizers.Second.seed) ^ 14

def conjugator9 : Model := ((sourceRepresentative 9 : Model) * InvolutionCentralizers.Second.seed) ^ 16

attribute [local irreducible] conjugator3 conjugator9 secondWord3 secondWord9

theorem eval_conjugator3 : toMatrix conjugator3 = decodeRows odd0_3RowsP14 := by
  have hr : toMatrix ((sourceRepresentative 3 : Model) * InvolutionCentralizers.Second.seed) =
      decodeRows odd0_3Rows := by
    rw [map_mul, eval_rep_3]
    change decodeRows kernel26At1Rows * toMatrix Janko4.Cardinality.LocalInvolutionCensus.t = _
    rw [eval_target, decoded_product Case0_3.product_01]
  have h2 : decodeRows odd0_3Rows ^ 2 = decodeRows odd0_3RowsP2 := by
    rw [pow_two, decoded_product Case0_3.product_02]
  have h3 : decodeRows odd0_3Rows ^ 3 = decodeRows odd0_3RowsP3 := by
    rw [pow_succ, h2, decoded_product Case0_3.product_03]
  have h6 : decodeRows odd0_3Rows ^ 6 = decodeRows odd0_3RowsP6 := by
    rw [show 6 = 3+3 from rfl, pow_add, h3, decoded_product Case0_3.product_04]
  have h7 : decodeRows odd0_3Rows ^ 7 = decodeRows odd0_3RowsP7 := by
    rw [pow_succ, h6, decoded_product Case0_3.product_05]
  rw [conjugator3, map_pow, hr, show 14 = 7+7 from rfl, pow_add, h7,
    decoded_product Case0_3.product_06]

theorem eval_conjugator9 : toMatrix conjugator9 = decodeRows odd0_9RowsP16 := by
  have hr : toMatrix ((sourceRepresentative 9 : Model) * InvolutionCentralizers.Second.seed) =
      decodeRows odd0_9Rows := by
    rw [map_mul, eval_rep_9]
    change decodeRows rep9Rows * toMatrix Janko4.Cardinality.LocalInvolutionCensus.t = _
    rw [eval_target, decoded_product Case0_9.product_01]
  have h2 : decodeRows odd0_9Rows ^ 2 = decodeRows odd0_9RowsP2 := by
    rw [pow_two, decoded_product Case0_9.product_02]
  have h4 : decodeRows odd0_9Rows ^ 4 = decodeRows odd0_9RowsP4 := by
    rw [show 4 = 2+2 from rfl, pow_add, h2, decoded_product Case0_9.product_03]
  have h8 : decodeRows odd0_9Rows ^ 8 = decodeRows odd0_9RowsP8 := by
    rw [show 8 = 4+4 from rfl, pow_add, h4, decoded_product Case0_9.product_04]
  rw [conjugator9, map_pow, hr, show 16 = 8+8 from rfl, pow_add, h8,
    decoded_product Case0_9.product_05]

private theorem eval_source_center :
    toMatrix ((sourceSeed ^ 2 : sourceSubgroup) : Model) = decodeRows (factorRows 0) :=
  eval_factor 0

theorem conjugator3_first :
    conjugator3 * (sourceRepresentative 3 : Model) * conjugator3⁻¹ =
      InvolutionCentralizers.Second.seed := by
  apply mul_inv_eq_iff_eq_mul.mpr
  apply toMatrix_injective
  rw [map_mul, map_mul, eval_conjugator3, eval_rep_3]
  change decodeRows odd0_3RowsP14 * decodeRows kernel26At1Rows = toMatrix Janko4.Cardinality.LocalInvolutionCensus.t * _
  rw [eval_target, decoded_product product_00, decoded_product product_01]

theorem conjugator3_second :
    conjugator3 * ((sourceSeed ^ 2 : sourceSubgroup) : Model) * conjugator3⁻¹ =
      secondWord3 := by
  apply mul_inv_eq_iff_eq_mul.mpr
  apply toMatrix_injective
  rw [map_mul, map_mul, eval_conjugator3, eval_source_center, eval_secondWord3,
    decoded_product product_04, decoded_product product_05]

theorem conjugator9_first :
    conjugator9 * (sourceRepresentative 9 : Model) * conjugator9⁻¹ =
      InvolutionCentralizers.Second.seed := by
  apply mul_inv_eq_iff_eq_mul.mpr
  apply toMatrix_injective
  rw [map_mul, map_mul, eval_conjugator9, eval_rep_9]
  change decodeRows odd0_9RowsP16 * decodeRows rep9Rows = toMatrix Janko4.Cardinality.LocalInvolutionCensus.t * _
  rw [eval_target, decoded_product product_06, decoded_product product_07]

theorem conjugator9_second :
    conjugator9 * ((sourceSeed ^ 2 : sourceSubgroup) : Model) * conjugator9⁻¹ =
      secondWord9 := by
  apply mul_inv_eq_iff_eq_mul.mpr
  apply toMatrix_injective
  rw [map_mul, map_mul, eval_conjugator9, eval_source_center, eval_secondWord9,
    decoded_product product_13, decoded_product product_14]

end Janko4.LocalStructure.LargeCenterRadicals.SecondReverseCertificate

public noncomputable section
open Subgroup Theory.GroupTheory
namespace Janko4.LocalStructure.LargeCenterRadicals.OuterHalf
attribute [local irreducible] Janko4.modelGroup Janko4.matrixA Janko4.matrixB
open Janko4.OuterReduction.FixedGenerator.NormalizerSquares
open TwoCoreCentralizerData LowerBound
open Janko4.Cardinality.LocalInvolutionCensus
open Janko4.Cardinality.LocalInvolutionCensus.FusionCertificates
open SecondReverseCertificate
attribute [local irreducible] sourceSubgroup sourceSubgroupEquivLocal

theorem innerRelated_second_kernel (u : InvolutionCentralizers.Second.Local)
    (hu : u ∈ InvolutionCentralizers.Second.max1Kernel) :
    InnerRelated InvolutionCentralizers.Second.seed u := by
  open InvolutionCentralizers.Second in
  let k : kernel := ⟨⟨u, max1Kernel_le_localCentralizer hu⟩, hu⟩
  have hk : ambientExtension.inl k ∈ solvableResidual ambientCentralizer := by
    rw [← second_innerHalf_eq_residual]
    exact MonoidHom.ker_le_comap _ _
      (ambientExtension.range_inl_eq_ker_rightHom ▸ (show ambientExtension.inl k ∈ ambientExtension.inl.range from ⟨k, rfl⟩))
  exact ⟨ambientExtension.inl k, hk, ambientExtension_inl_val k⟩

theorem source_pair3_inner :
    InnerRelated ((sourceSeed ^ 2 : sourceSubgroup) : Model) (sourceRepresentative 3) ∧
      InnerRelated (sourceRepresentative 3) ((sourceSeed ^ 2 : sourceSubgroup) : Model) := by
  constructor
  · have hu : sourceRepresentative 3 = kernelProduct 26 := by
      change kernelProduct 26 * 1 = kernelProduct 26
      exact mul_one _
    rw [hu]
    exact innerRelated_source_kernel 26
  · apply (innerRelated_equiv (MulAut.conj conjugator3) _ _).mp
    simpa only [MulAut.conj_apply, conjugator3_first, conjugator3_second] using
      innerRelated_second_kernel secondWord3 secondWord3_mem

private theorem source_center_order :
    orderOf ((sourceSeed ^ 2 : sourceSubgroup) : Model) = 2 := by
  calc
    _ = orderOf (sourceSeed ^ 2 : sourceSubgroup) :=
      orderOf_injective sourceSubgroup.subtype sourceSubgroup.subtype_injective _
    _ = orderOf (sourceSubgroupEquivLocal (sourceSeed ^ 2)) :=
      (orderOf_injective sourceSubgroupEquivLocal.toMonoidHom
        sourceSubgroupEquivLocal.injective (sourceSeed ^ 2)).symm
    _ = 2 := by rw [Coordinates.sourceEquiv_seed_sq]; exact orderOf_zH

private theorem source_square_inner (u : sourceSubgroup) :
    InnerRelated ((sourceSeed ^ 2 : sourceSubgroup) : Model) ((u ^ 2 : sourceSubgroup) : Model) := by
  have hc : u * sourceSeed ^ 2 = sourceSeed ^ 2 * u := by
    apply sourceSubgroupEquivLocal.injective
    simpa only [map_mul, Coordinates.sourceEquiv_seed_sq] using
      mem_center_iff.mp zH_mem_center (sourceSubgroupEquivLocal u)
  let v : centralizer ({((sourceSeed ^ 2 : sourceSubgroup) : Model)} : Set Model) :=
    ⟨u, mem_centralizer_singleton_iff.mpr (congrArg Subtype.val hc)⟩
  exact ⟨v ^ 2, (solvableResidual _).sq_mem_of_index_two
    (involution_residual_index _ source_center_order) v, rfl⟩

theorem source_pair9_forward :
    InnerRelated ((sourceSeed ^ 2 : sourceSubgroup) : Model) (sourceRepresentative 9) := by
  have hpow := source_square_inner (((sourceX * sourceY) ^ 5 * sourceY) ^ 2)
  have hfour : InnerRelated ((sourceSeed ^ 2 : sourceSubgroup) : Model)
      (((sourceX * sourceY) ^ 5 * sourceY) ^ 4 : sourceSubgroup) := by
    simpa only [← pow_mul] using hpow
  change ((kernelProduct 304 : sourceSubgroup) : Model) *
    ((((sourceX * sourceY) ^ 5 * sourceY) ^ 4 : sourceSubgroup) : Model) ∈ _
  exact Subgroup.mul_mem _ (innerRelated_source_kernel 304) hfour

theorem source_pair9_reverse :
    InnerRelated (sourceRepresentative 9) ((sourceSeed ^ 2 : sourceSubgroup) : Model) := by
  apply (innerRelated_equiv (MulAut.conj conjugator9) _ _).mp
  simpa only [MulAut.conj_apply, conjugator9_first, conjugator9_second] using
    innerRelated_second_kernel secondWord9 secondWord9_mem

theorem source_pair9_inner :
    InnerRelated ((sourceSeed ^ 2 : sourceSubgroup) : Model) (sourceRepresentative 9) ∧
      InnerRelated (sourceRepresentative 9) ((sourceSeed ^ 2 : sourceSubgroup) : Model) :=
  ⟨source_pair9_forward, source_pair9_reverse⟩

private theorem pair_class_of_source (i : Fin 11)
    (hi : InnerRelated ((sourceSeed ^ 2 : sourceSubgroup) : Model) (sourceRepresentative i) ∧
      InnerRelated (sourceRepresentative i) ((sourceSeed ^ 2 : sourceSubgroup) : Model))
    (u : H) (hu : IsConj (representative i) u) :
    InnerRelated Janko4.a (eH u) ∧ InnerRelated (eH u) Janko4.a := by
  have hs : (MulAut.conj h⁻¹) ((sourceSeed ^ 2 : sourceSubgroup) : Model) = Janko4.a := by
    simpa only [MulAut.conj_apply, inv_inv, coe_sourceSeed_sq] using conjugates_t
  have hv : (MulAut.conj h⁻¹) (sourceRepresentative i : Model) = eH (representative i) := by
    rw [representative_eq, eH_sourceSubgroupEquivLocal, MulAut.conj_apply, inv_inv]
  have hp : InnerRelated Janko4.a (eH (representative i)) ∧
      InnerRelated (eH (representative i)) Janko4.a := by
    constructor
    · simpa only [MulEquiv.coe_toMonoidHom, hs, hv] using
        innerRelated_map (MulAut.conj h⁻¹).toMonoidHom hi.1
    · simpa only [MulEquiv.coe_toMonoidHom, hs, hv] using
        innerRelated_map (MulAut.conj h⁻¹).toMonoidHom hi.2
  obtain ⟨g, hg⟩ := isConj_iff.mp hu
  have ha : (MulAut.conj (eH g)) Janko4.a = Janko4.a := by
    have hc := (eH_commute_z g).eq
    change eH g * Janko4.a = Janko4.a * eH g at hc
    change eH g * Janko4.a * (eH g)⁻¹ = Janko4.a
    rw [hc, mul_inv_cancel_right]
  have hv' : (MulAut.conj (eH g)) (eH (representative i)) = eH u := by
    simpa only [map_mul, map_inv, MulAut.conj_apply] using congrArg eH hg
  constructor
  · simpa only [MulEquiv.coe_toMonoidHom, ha, hv'] using
      innerRelated_map (MulAut.conj (eH g)).toMonoidHom hp.1
  · simpa only [MulEquiv.coe_toMonoidHom, ha, hv'] using
      innerRelated_map (MulAut.conj (eH g)).toMonoidHom hp.2

/-- Both directions on the entire representative-3 local conjugacy class. -/
theorem first_pair3_class_inner (u : H) (hu : IsConj (representative 3) u) :
    InnerRelated Janko4.a (eH u) ∧ InnerRelated (eH u) Janko4.a :=
  pair_class_of_source 3 source_pair3_inner u hu

/-- Both directions on the entire representative-9 local conjugacy class. -/
theorem first_pair9_class_inner (u : H) (hu : IsConj (representative 9) u) :
    InnerRelated Janko4.a (eH u) ∧ InnerRelated (eH u) Janko4.a :=
  pair_class_of_source 9 source_pair9_inner u hu

end Janko4.LocalStructure.LargeCenterRadicals.OuterHalf
