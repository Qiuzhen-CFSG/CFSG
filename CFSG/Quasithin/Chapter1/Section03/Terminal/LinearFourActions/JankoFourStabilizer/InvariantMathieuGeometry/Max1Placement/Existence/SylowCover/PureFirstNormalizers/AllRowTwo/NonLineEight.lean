module
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.PureFirstNormalizers.AllRowTwo.NonLineEightCertificates
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.PureFirstNormalizers.AllRowTwo.Uniqueness
/-!
# A native obstruction to unrestricted eight containment

The original max2 kernel words with masks 1, 6, and 6607 generate an actual
pure first-class elementary eight. The existing local conjugacy forest proves
purity. Kernel-checked displacement ranks are sixteen on every independent
pair, so the group contains no conjugate of the native row-seven pair.

The group contains the bridge-conjugate of the certified max4 plane. That
plane determines its certified-eight container uniquely, while a checked
matrix entry puts mask 6 outside this container. Hence this group is contained
in no ambient conjugate of the certified max4 eight.

This refutes the unrestricted container intermediate suggested by Section 2.1
of Kleidman--Wilson (1988), pp.488--489, for the literal native definitions.
The section classifies maximal two-local normalizers: no maximal-two-local
hypothesis is proved for this example, and no counterexample to that source
classification is asserted. The specialization using that hypothesis remains
an independent mathematical obligation. The original ATLAS words and license
attribution are retained in the imported max2/max4 source directories.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace Janko4.LocalStructure.PureFirstNormalizers.AllRowTwo.NonLineEight
open Janko4.GeneratorCertificates
open Cardinality.LocalInvolutionCensus Cardinality.LocalInvolutionCensus.Coordinates
open Cardinality.LocalInvolutionCensus.FiberCensus
open OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData
open LowerBound
open CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover.MatrixNormalizerBounds
open CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover.KernelOrders.PureNormalizers
open Max4EightCentralizer
attribute [local irreducible] modelGroup matrixA matrixB toMatrix
set_option backward.isDefEq.respectTransparency true

@[expose] def element (i : Fin 8) : sourceSubgroup :=
  ![1, sourceRepresentative 1, sourceRepresentative 2,
    sourceRepresentative 1 * sourceRepresentative 2,
    sourceP, sourceRepresentative 1 * sourceP,
    sourceRepresentative 2 * sourceP,
    sourceRepresentative 1 * (sourceRepresentative 2 * sourceP)] i

@[expose] def mask (i : Fin 8) : Fin 8192 := ![0,1,6,7,6607,6606,6601,6600] i
@[expose] def xorIndex (i j : Fin 8) : Fin 8 := ⟨(i.val ^^^ j.val) % 8, Nat.mod_lt _ (by decide)⟩

private theorem eval_mul {u v : sourceSubgroup} {rs ss ts : Vector ℕ 112}
    (hu : toMatrix (u : Model) = decodeRows rs)
    (hv : toMatrix (v : Model) = decodeRows ss) (h : packedMul rs ss = ts) :
    toMatrix ((u*v : sourceSubgroup) : Model) = decodeRows ts := by
  change toMatrix ((u : Model)*(v : Model)) = _
  rw [map_mul,hu,hv,← decode_packedMul,h]

private theorem eval_element (i : Fin 8) :
    toMatrix (element i : Model) = decodeRows (rows i) := by
  have h1 : toMatrix (sourceRepresentative 1 : Model) = decodeRows r1 := by
    have he : r1 = RepresentativeMatrices.r1 := by
      have hc : ∀ i : Fin 112, r1.get i = RepresentativeMatrices.r1.get i := by
        simp only [RepresentativeMatrices.r1, get_ofFn]
        decide +kernel
      apply Vector.ext
      intro i hi
      exact hc ⟨i,hi⟩
    rw [he]
    exact RepresentativeMatrices.eval_representative1
  have h2 : toMatrix (sourceRepresentative 2 : Model) = decodeRows r2 := by
    have he : r2 = RepresentativeMatrices.r2 := by
      have hc : ∀ i : Fin 112, r2.get i = RepresentativeMatrices.r2.get i := by
        simp only [RepresentativeMatrices.r2, get_ofFn]
        decide +kernel
      apply Vector.ext
      intro i hi
      exact hc ⟨i,hi⟩
    rw [he]
    exact RepresentativeMatrices.eval_representative2
  have h4 : toMatrix (sourceP : Model) = decodeRows r4 := by
    exact MarkingCertificates.eval_sourceP
  fin_cases i
  · change toMatrix (1 : Model) = decodeRows r0
    rw [map_one]
    have hc : r0 = packedOne := by
      have ht : ∀ i : Fin 112, r0.get i = 2^i.val := by decide +kernel
      apply Vector.ext
      intro i hi
      change r0.get ⟨i,hi⟩ = packedOne.get ⟨i,hi⟩
      rw [packedOne,get_ofFn,ht]
    rw [hc,decode_packedOne]
  · exact h1
  · exact h2
  · exact eval_mul h1 h2 multiply_1_2
  · exact h4
  · exact eval_mul h1 h4 multiply_1_4
  · exact eval_mul h2 h4 multiply_2_4
  · exact eval_mul h1 (eval_mul h2 h4 multiply_2_4) multiply_1_6

private theorem element_q (i : Fin 8) : quotientMap (element i) = 1 := by
  have hp (m : Fin 8192) : quotientMap (kernelProduct m) = 1 :=
    map_kernelProduct_eq_one _ quotientMap_seed m
  have h1 : quotientMap (sourceRepresentative 1) = 1 := by
    change quotientMap (kernelProduct 1 * 1) = 1
    rw [mul_one,hp]
  have h2 : quotientMap (sourceRepresentative 2) = 1 := by
    change quotientMap (kernelProduct 6 * 1) = 1
    rw [mul_one,hp]
  have h4 : quotientMap sourceP = 1 := hp 6607
  fin_cases i
  · exact map_one _
  · exact h1
  · exact h2
  · change quotientMap (sourceRepresentative 1 * sourceRepresentative 2) = 1
    rw [map_mul,h1,h2,mul_one]
  · exact h4
  · change quotientMap (sourceRepresentative 1 * sourceP) = 1
    rw [map_mul,h1,h4,mul_one]
  · change quotientMap (sourceRepresentative 2 * sourceP) = 1
    rw [map_mul,h2,h4,mul_one]
  · change quotientMap (sourceRepresentative 1 * (sourceRepresentative 2 * sourceP)) = 1
    rw [map_mul,map_mul,h1,h2,h4,mul_one,mul_one]

private theorem element_coordinates (i : Fin 8) : element i = kernelProduct (mask i) := by
  apply KernelRows.eq_of_quotient_eq_of_firstRow Cardinality.Thompson.max2_card.le
  · rw [element_q,map_kernelProduct_eq_one _ quotientMap_seed]
  · funext j
    rw [KernelRows.firstRow_kernelProduct]
    change toMatrix (element i : Model) 0 j = _
    rw [eval_element]
    change bit ((rows i).get 0) j.val = _
    have hc : ∀ i : Fin 8, (rows i).get 0 = KernelSeparation.row (mask i).val := by decide +kernel
    rw [hc]

private theorem element_mul (i j : Fin 8) : element i * element j = element (xorIndex i j) := by
  apply KernelRows.eq_of_quotient_eq_of_firstRow Cardinality.Thompson.max2_card.le
  · rw [map_mul,element_q,element_q,element_q,mul_one]
  · funext k
    change toMatrix ((element i : Model)*(element j : Model)) 0 k =
      toMatrix (element (xorIndex i j) : Model) 0 k
    rw [map_mul,eval_element,eval_element,eval_element,← decode_packedMul]
    simp only [decodeRows,packedMul,get_ofFn]
    have hc : ∀ i j : Fin 8, packedRow ((rows i).get 0) (rows j) =
        (rows (xorIndex i j)).get 0 := by decide +kernel
    rw [hc]

private theorem element_zero : element 0 = 1 := rfl
private theorem element_sq (i : Fin 8) : element i * element i = 1 := by
  rw [element_mul]
  have h : ∀ i : Fin 8, xorIndex i i = 0 := by decide +kernel
  rw [h,element_zero]

private theorem element_comm (i j : Fin 8) : Commute (element i) (element j) := by
  change element i * element j = element j * element i
  rw [element_mul,element_mul]
  have h : ∀ i j : Fin 8, xorIndex i j = xorIndex j i := by decide +kernel
  rw [h]

private theorem element_injective : Function.Injective element := by
  intro i j he
  rw [element_coordinates,element_coordinates] at he
  have hc : Function.Injective mask := by decide +kernel
  exact hc (kernelProduct_injective he)

/-- An actual elementary eight generated by the original source words
with masks 1, 6, and 6607. -/
@[expose] def sourceEight : Subgroup Model where
  carrier := Set.range (fun i => (element i : Model))
  one_mem' := ⟨0,rfl⟩
  mul_mem' := by
    rintro _ _ ⟨i,rfl⟩ ⟨j,rfl⟩
    exact ⟨xorIndex i j,congrArg Subtype.val (element_mul i j).symm⟩
  inv_mem' := by
    rintro _ ⟨i,rfl⟩
    refine ⟨i,?_⟩
    symm
    exact inv_eq_of_mul_eq_one_left (congrArg Subtype.val (element_sq i))

theorem sourceEight_card : Nat.card sourceEight = 8 := by
  let f : Fin 8 → sourceEight := fun i => ⟨element i,⟨i,rfl⟩⟩
  have hf : Function.Bijective f := by
    constructor
    · intro i j he
      have hv : (element i : Model) = (element j : Model) :=
        congrArg (fun z : sourceEight => (z : Model)) he
      exact element_injective (Subtype.ext hv)
    · rintro ⟨_,⟨i,rfl⟩⟩
      exact ⟨i,rfl⟩
  exact (Nat.card_congr (Equiv.ofBijective f hf).symm).trans (Nat.card_fin 8)

theorem sourceEight_elementary : IsElementaryAbelian 2 sourceEight where
  toIsMulCommutative := IsMulCommutative.of_comm fun x y => by
    apply Subtype.ext
    obtain ⟨i,hi⟩ := x.property
    obtain ⟨j,hj⟩ := y.property
    change (x : Model)*(y : Model) = (y : Model)*(x : Model)
    rw [← hi,← hj]
    exact congrArg Subtype.val (element_comm i j).eq
  exponent_dvd_p := by
    apply Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
    rintro ⟨_,⟨i,rfl⟩⟩
    apply Subtype.ext
    change (element i : Model)^2 = 1
    rw [pow_two]
    exact congrArg (fun z : sourceSubgroup => (z : Model)) (element_sq i)

private theorem element_pure (i : Fin 8) (hi : i ≠ 0) : IsConj a (element i : Model) := by
  have hm : mask i ∈ masks 1 ∨ mask i ∈ masks 2 := by
    have hc : ∀ i : Fin 8, i ≠ 0 → mask i ∈ masks 1 ∨ mask i ∈ masks 2 := by decide +kernel
    exact hc i hi
  have help (k : Fin 11) (hk : k = 1 ∨ k = 2) (hm : mask i ∈ masks k) :
      IsConj a (element i : Model) := by
    have hc := Forest.listed_isConj_of_edges (Forest.edges Cardinality.Thompson.max2_card.le) k (mask i) hm
    have hf : fiberIndex k = 0 := by rcases hk with rfl | rfl <;> rfl
    have he : sourceElement (fiberIndex k) (mask i) = element i := by
      rw [hf,sourceElement]
      change kernelProduct (mask i)*1 = element i
      rw [mul_one,element_coordinates]
    rw [he] at hc
    have hl := eH.map_isConj (sourceSubgroupEquivLocal.toMonoidHom.map_isConj hc)
    simp only [MulEquiv.toMonoidHom_eq_coe,MonoidHom.coe_coe,sourceEquiv_representative] at hl
    have ha : IsConj a (eH (representative k)) := by
      have hh := firstTarget_isConj_representative k
      rcases hk with rfl | rfl <;> exact hh
    have hp := ha.trans hl
    apply hp.trans
    apply isConj_iff.mpr
    refine ⟨h,?_⟩
    rw [eH_sourceSubgroupEquivLocal]
    simp [mul_assoc]
  rcases hm with hm | hm
  · exact help 1 (Or.inl rfl) hm
  · exact help 2 (Or.inr rfl) hm

theorem sourceEight_pure : ∀ x ∈ sourceEight, x ≠ 1 → IsConj a x := by
  rintro x ⟨i,rfl⟩ hx
  exact element_pure i (fun hi => hx (by subst i; rfl))

open ElementaryNormalizerCover.PureTwoA.NativePair
private theorem ordered_pair_rank (i j : Fin 8) (hi : i ≠ 0) (hij : i < j) :
    pairRank (element i) (element j) = 16 := by
  unfold pairRank
  rw [eval_element,eval_element,← RepresentativeMatrices.decode_displacement,
    ← RepresentativeMatrices.decode_displacement,← decode_packedMul,pair_product i j hi hij]
  exact pair_rows_rank _

private theorem element_pair_rank (i j : Fin 8) (hi : i ≠ 0) (hj : j ≠ 0) (hij : i ≠ j) :
    pairRank (element i) (element j) = 16 := by
  rcases lt_or_gt_of_ne hij with hh | hh
  · exact ordered_pair_rank i j hi hh
  · have hc : toMatrix (element i : Model) * toMatrix (element j : Model) =
        toMatrix (element j : Model) * toMatrix (element i : Model) := by
      simpa only [Subgroup.coe_mul,map_mul] using
        congrArg (fun z : sourceSubgroup => toMatrix (z : Model)) (element_comm i j).eq
    have hs : (toMatrix (element i : Model) - 1) * (toMatrix (element j : Model) - 1) =
        (toMatrix (element j : Model) - 1) * (toMatrix (element i : Model) - 1) := by
      simp only [mul_sub,sub_mul,mul_one,one_mul]
      rw [hc]
      abel
    unfold pairRank
    rw [hs]
    exact ordered_pair_rank j i hj hh

theorem sourceEight_no_native_pair :
    ¬ ∃ g : Model, nativePair.map (MulAut.conj g).toMonoidHom ≤ sourceEight := by
  let := sourceEight_elementary
  apply (no_native_pair_iff_pair_rank sourceEight sourceEight_pure).mpr
  rintro x ⟨i,rfl⟩ y ⟨j,rfl⟩ hx hy hxy
  exact element_pair_rank i j (fun hi => hx (by subst i; rfl))
    (fun hj => hy (by subst j; rfl)) (fun hij => hxy (hij ▸ rfl))

end Janko4.LocalStructure.PureFirstNormalizers.AllRowTwo.NonLineEight
public noncomputable section
open Subgroup
namespace Janko4.LocalStructure.PureFirstNormalizers.AllRowTwo.NonLineEight
open Janko4.GeneratorCertificates
open SymmetricLinear
open Cardinality.LocalInvolutionCensus.FiberCensus
open OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData
open CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover.MatrixNormalizerBounds
open CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover.KernelOrders.PureNormalizers
open Max4EightCentralizer
attribute [local irreducible] modelGroup matrixA matrixB toMatrix
set_option backward.isDefEq.respectTransparency true

private def separatingColumn (i : Fin 8) : Fin 112 := ![0,0,0,2,0,2,1,1] i
private theorem row_separation (i : Fin 8) :
    bit (packedRow (MarkingCertificates.bridgeRows.get 0) (NormalEight.elementRows i))
        (separatingColumn i).val ≠
      bit (packedRow (r2.get 0) MarkingCertificates.bridgeRows) (separatingColumn i).val := by
  fin_cases i
  · change bit (packedRow (MarkingCertificates.bridgeRows.get 0) packedOne) 0 ≠
      bit (packedRow (r2.get 0) MarkingCertificates.bridgeRows) 0
    simp only [packedRow,packedOne,get_ofFn]
    decide +kernel
  all_goals decide +kernel

/-- The mask-six element lies outside the bridge-conjugate of the certified eight. -/
theorem second_not_mem_marked_eight :
    (element 2 : Model) ∉ max4Eight.map (MulAut.conj bridge).toMonoidHom := by
  rintro ⟨_,⟨_,⟨i,rfl⟩,rfl⟩,he⟩
  change bridge*(NormalEight.element i : Model)*bridge⁻¹ = (element 2 : Model) at he
  have hh : bridge*(NormalEight.element i : Model) = (element 2 : Model)*bridge := by
    rw [← he]
    group
  have hm := congrArg toMatrix hh
  rw [map_mul,map_mul,MarkingCertificates.eval_bridge,
    (show toMatrix (NormalEight.element i : Model) = _ from NormalEight.matrix_element i),
    eval_element,← decode_packedMul,← decode_packedMul] at hm
  have hv := congrFun (congrFun hm 0) (separatingColumn i)
  simp only [decodeRows,packedMul,get_ofFn] at hv
  exact row_separation i hv

private theorem element_one_val : (element 1 : Model) = t := by
  have he : sourceRepresentative 1 = LowerBound.sourceSeed^2 := by
    change LowerBound.kernelProduct 1 * 1 = LowerBound.sourceSeed^2
    rw [mul_one]
    change (List.prod [LowerBound.kernelFactor 0,1,1,1,1,1,1,1,1,1,1,1,1]) = _
    simp only [List.prod_cons,List.prod_nil,mul_one]
    rfl
  change (sourceRepresentative 1 : Model) = t
  rw [he,LowerBound.coe_sourceSeed_sq]

/-- The same group contains the actual marked plane, with its literal conjugator. -/
theorem marked_plane_le : max4Plane.map (MulAut.conj bridge).toMonoidHom ≤ sourceEight := by
  have ht : t ∈ sourceEight := ⟨1,element_one_val⟩
  rintro _ ⟨_,⟨_,⟨i,rfl⟩,rfl⟩,rfl⟩
  fin_cases i
  · change (MulAut.conj bridge) (NormalEight.element 0 : Model) ∈ sourceEight
    rw [NormalEight.element_zero,Subgroup.coe_one,map_one]
    exact one_mem _
  · change (MulAut.conj bridge) (NormalEight.element 1 : Model) ∈ sourceEight
    rw [marking.1]
    exact ⟨4,rfl⟩
  · change (MulAut.conj bridge) (NormalEight.element 2 : Model) ∈ sourceEight
    rw [marking.2.1]
    exact ht
  · change (MulAut.conj bridge) (NormalEight.element 5 : Model) ∈ sourceEight
    have he : (NormalEight.element 5 : Model) =
        (NormalEight.element 1 : Model)*(NormalEight.element 2 : Model) :=
      congrArg (fun z : max4Subgroup => (z : Model)) (NormalEight.element_mul 1 2).symm
    rw [he,map_mul,marking.1,marking.2.1]
    exact sourceEight.mul_mem ⟨4,rfl⟩ ht

/-- No ambient conjugate of the certified eight contains this all-row-two group. -/
theorem sourceEight_no_eight_container :
    ¬ ∃ g : Model, sourceEight ≤ max4Eight.map (MulAut.conj g).toMonoidHom := by
  rintro ⟨g,hg⟩
  have hp : max4Plane ≤ max4Eight := by
    apply map_mono
    rintro _ ⟨i,rfl⟩
    exact ⟨planeIndex i,rfl⟩
  have he := eight_unique_over_plane (max4Plane.map (MulAut.conj bridge).toMonoidHom)
    ((card_map_of_injective (MulAut.conj bridge).injective).trans max4Plane_card)
    g bridge (marked_plane_le.trans hg) (map_mono hp)
  rw [he] at hg
  exact second_not_mem_marked_eight (hg ⟨2,rfl⟩)

/-- The unrestricted eight-container intermediate is false for the actual
native action. No maximal-two-local hypothesis is asserted for this example. -/
theorem exists_all_row_two_without_eight_container :
    ∃ X : Subgroup Model, IsElementaryAbelian 2 X ∧ Nat.card X = 8 ∧
      (∀ x ∈ X, x ≠ 1 → IsConj a x) ∧
      (¬ ∃ g : Model, ElementaryNormalizerCover.PureTwoA.NativePair.nativePair.map
        (MulAut.conj g).toMonoidHom ≤ X) ∧
      (¬ ∃ g : Model, X ≤ max4Eight.map (MulAut.conj g).toMonoidHom) :=
  ⟨sourceEight,sourceEight_elementary,sourceEight_card,sourceEight_pure,
    sourceEight_no_native_pair,sourceEight_no_eight_container⟩

end Janko4.LocalStructure.PureFirstNormalizers.AllRowTwo.NonLineEight
