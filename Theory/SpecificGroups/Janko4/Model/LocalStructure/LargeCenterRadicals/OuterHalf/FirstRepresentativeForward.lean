module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.LargeCenterRadicals.OuterHalf.SecondPairs
public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalInvolutionCensus.FiberCensus.RepresentativeMatrices.WordEvaluations

/-!
# Forward first-half comparisons for two native representatives

The seventh representative is the fourth power of the source dihedral word;
the tenth is its product with the certified first-core word `kernelProduct 305`.
Squares of elements of the source subgroup lie in the marked involution's
index-two residual, so the literal source words give the forward inclusions.
The proof keeps the full intrinsic residual membership and does not infer the
reverse inclusions or any global coverage statement.

Source: Kleidman--Wilson (1988), p.487, Corollary 1.1.4; the source words and
their native representative indexing are certified in the LocalInvolutionCensus
modules imported below.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open Janko4.Cardinality.LocalInvolutionCensus
namespace Janko4.LocalStructure.LargeCenterRadicals.OuterHalf
open Janko4.OuterReduction.FixedGenerator.NormalizerSquares
open TwoCoreCentralizerData LowerBound
open Janko4.Cardinality.LocalInvolutionCensus.FusionCertificates
attribute [local irreducible] Janko4.modelGroup Janko4.matrixA Janko4.matrixB

private theorem source_center_order_forward :
    orderOf ((sourceSeed ^ 2 : sourceSubgroup) : Model) = 2 := by
  calc
    _ = orderOf (sourceSeed ^ 2 : sourceSubgroup) :=
      orderOf_injective sourceSubgroup.subtype sourceSubgroup.subtype_injective _
    _ = orderOf (sourceSubgroupEquivLocal (sourceSeed ^ 2)) :=
      (orderOf_injective sourceSubgroupEquivLocal.toMonoidHom
        sourceSubgroupEquivLocal.injective (sourceSeed ^ 2)).symm
    _ = 2 := by rw [Coordinates.sourceEquiv_seed_sq]; exact orderOf_zH

private theorem source_square_inner_forward (u : sourceSubgroup) :
    InnerRelated ((sourceSeed ^ 2 : sourceSubgroup) : Model)
      ((u ^ 2 : sourceSubgroup) : Model) := by
  have hc : u * sourceSeed ^ 2 = sourceSeed ^ 2 * u := by
    apply sourceSubgroupEquivLocal.injective
    simpa only [map_mul, Coordinates.sourceEquiv_seed_sq] using
      mem_center_iff.mp zH_mem_center (sourceSubgroupEquivLocal u)
  let v : centralizer ({((sourceSeed ^ 2 : sourceSubgroup) : Model)} : Set Model) :=
    ⟨u, mem_centralizer_singleton_iff.mpr (congrArg Subtype.val hc)⟩
  exact ⟨v ^ 2, (solvableResidual _).sq_mem_of_index_two
    (involution_residual_index _ source_center_order_forward) v, rfl⟩

private theorem source_lift3_inner :
    InnerRelated ((sourceSeed ^ 2 : sourceSubgroup) : Model) (sourceLift 3) := by
  have hpow := source_square_inner_forward (((sourceX * sourceY) ^ 5 * sourceY) ^ 2)
  have hfour : InnerRelated ((sourceSeed ^ 2 : sourceSubgroup) : Model)
      (((sourceX * sourceY) ^ 5 * sourceY) ^ 4 : sourceSubgroup) := by
    simpa only [← pow_mul] using hpow
  simpa [sourceLift] using hfour

private theorem source_representative7_forward :
    InnerRelated ((sourceSeed ^ 2 : sourceSubgroup) : Model) (sourceRepresentative 7) := by
  have hrep : sourceRepresentative 7 = kernelProduct 0 * sourceLift 3 := by
    rfl
  rw [hrep]
  rcases innerRelated_source_kernel 0 with ⟨qk, hqk, hkv⟩
  rcases source_lift3_inner with ⟨q4, hq4, h4v⟩
  refine ⟨qk * q4, Subgroup.mul_mem _ hqk hq4, ?_⟩
  rw [map_mul, hkv, h4v]
  rfl

private theorem source_representative10_forward :
    InnerRelated ((sourceSeed ^ 2 : sourceSubgroup) : Model) (sourceRepresentative 10) := by
  have hrep : sourceRepresentative 10 = kernelProduct 305 * sourceLift 3 := by
    rfl
  rw [hrep]
  rcases innerRelated_source_kernel 305 with ⟨qk, hqk, hkv⟩
  rcases source_lift3_inner with ⟨q4, hq4, h4v⟩
  refine ⟨qk * q4, Subgroup.mul_mem _ hqk hq4, ?_⟩
  rw [map_mul, hkv, h4v]
  rfl

/-- The forward orientation of the representative-7 comparison. -/
theorem first_pair7_forward :
    InnerRelated Janko4.a (eH (representative 7)) := by
  have hs : (MulAut.conj h⁻¹) ((sourceSeed ^ 2 : sourceSubgroup) : Model) = Janko4.a := by
    simpa only [MulAut.conj_apply, inv_inv, coe_sourceSeed_sq] using conjugates_t
  have hv : (MulAut.conj h⁻¹) (sourceRepresentative 7 : Model) =
      eH (representative 7) := by
    rw [representative_eq, eH_sourceSubgroupEquivLocal, MulAut.conj_apply, inv_inv]
  simpa only [MulEquiv.coe_toMonoidHom, hs, hv] using
    innerRelated_map (MulAut.conj h⁻¹).toMonoidHom source_representative7_forward

/-- The forward orientation of the representative-10 comparison. -/
theorem first_pair10_forward :
    InnerRelated Janko4.a (eH (representative 10)) := by
  have hs : (MulAut.conj h⁻¹) ((sourceSeed ^ 2 : sourceSubgroup) : Model) = Janko4.a := by
    simpa only [MulAut.conj_apply, inv_inv, coe_sourceSeed_sq] using conjugates_t
  have hv : (MulAut.conj h⁻¹) (sourceRepresentative 10 : Model) =
      eH (representative 10) := by
    rw [representative_eq, eH_sourceSubgroupEquivLocal, MulAut.conj_apply, inv_inv]
  simpa only [MulEquiv.coe_toMonoidHom, hs, hv] using
    innerRelated_map (MulAut.conj h⁻¹).toMonoidHom source_representative10_forward

private theorem first_pair_class_forward (i : Fin 11)
    (hi : InnerRelated Janko4.a (eH (representative i)))
    (u : H) (hu : IsConj (representative i) u) :
    InnerRelated Janko4.a (eH u) := by
  obtain ⟨g, hg⟩ := isConj_iff.mp hu
  have ha : (MulAut.conj (eH g)) Janko4.a = Janko4.a := by
    have hc := (eH_commute_z g).eq
    change eH g * Janko4.a = Janko4.a * eH g at hc
    change eH g * Janko4.a * (eH g)⁻¹ = Janko4.a
    rw [hc, mul_inv_cancel_right]
  have hv : (MulAut.conj (eH g)) (eH (representative i)) = eH u := by
    simpa only [map_mul, map_inv, MulAut.conj_apply] using congrArg eH hg
  simpa only [MulEquiv.coe_toMonoidHom, ha, hv] using
    innerRelated_map (MulAut.conj (eH g)).toMonoidHom hi

/-- The forward comparison holds on the complete local conjugacy class of
representative 7. -/
theorem first_pair7_class_forward (u : H) (hu : IsConj (representative 7) u) :
    InnerRelated Janko4.a (eH u) :=
  first_pair_class_forward 7 first_pair7_forward u hu

/-- The forward comparison holds on the complete local conjugacy class of
representative 10. -/
theorem first_pair10_class_forward (u : H) (hu : IsConj (representative 10) u) :
    InnerRelated Janko4.a (eH u) :=
  first_pair_class_forward 10 first_pair10_forward u hu

end Janko4.LocalStructure.LargeCenterRadicals.OuterHalf
