module
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.PureFirstNormalizers.AllRowTwo.CanonicalOvergroups
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.PureFirstNormalizers.AllRowTwo.IntersectionCertificates

/-!
# The exhaustive native marked point-core intersection

The intersection of O₂(C(t)) and O₂(C(sourceP)) is elementary of order 128.
The seven source masks 1, 6, 192, 562, 1048, 2384, 4184 belong to both cores:
the checked max4 actor conjugates seven actual max2 kernel words to them.
Their 128 binary products have distinct certified kernel coordinates. The
extraspecial intersection bound therefore makes this list exhaustive.

The final source application uses one ambient conjugator for the original
all-row-two group, every eligible sixteen overgroup, and their canonical join.
Every element of that join receives a literal native kernel-word coordinate;
the full original normalizer is transported by the same conjugator. No JSON
statement, first-row-only equality, or unproved line containment is used.

Source: Kleidman--Wilson (1988), Corollary 1.2.2(a) and Section 2.1,
pp.488--489. The native ATLAS max2/max4 words and their attribution are retained
in the imported source directories. The census of pure eights and sixteens
inside this container and the named-local whole-normalizer placement remain
separate obligations; this finite reduction does not assert either one.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace Janko4.LocalStructure.PureFirstNormalizers.AllRowTwo.MarkedIntersection
open ElementaryNormalizerCover
open Janko4.GeneratorCertificates
open Cardinality.LocalInvolutionCensus Cardinality.LocalInvolutionCensus.Coordinates
open OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData
open LowerBound NormalClosureControl
open CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover.MatrixNormalizerBounds.Max4EightCentralizer
open CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover.MatrixNormalizerBounds.Max4EightCentralizer.PairOrbitData
open IntersectionCertificates
local notation "t₀" => OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.t
attribute [local irreducible] modelGroup matrixA matrixB toMatrix

@[expose] def actor : Model := bridge * (SymmetricLinear.NormalEight.y : Model)^3 * bridge⁻¹

private theorem eval_actor : toMatrix actor = decodeRows actorRows := by
  have hi : toMatrix bridge⁻¹ = decodeRows bridgeInverse := by
    have hh : toMatrix bridge * decodeRows bridgeInverse = 1 := by
      rw [MarkingCertificates.eval_bridge,← decode_packedMul,bridge_inverse,decode_packedOne]
    calc
      _ = toMatrix bridge⁻¹ * (toMatrix bridge * decodeRows bridgeInverse) := by rw [hh,mul_one]
      _ = _ := by rw [← mul_assoc,← map_mul,inv_mul_cancel,map_one,one_mul]
  have hy : toMatrix (SymmetricLinear.NormalEight.y : Model) =
      decodeRows SymmetricLinear.NormalEight.yRows := SymmetricLinear.NormalEight.matrix_y
  change toMatrix (bridge * (SymmetricLinear.NormalEight.y : Model)^3 * bridge⁻¹) = _
  rw [show (SymmetricLinear.NormalEight.y : Model)^3 =
      (SymmetricLinear.NormalEight.y : Model) * SymmetricLinear.NormalEight.y *
        SymmetricLinear.NormalEight.y by simp only [pow_succ,pow_zero,one_mul]]
  simp only [← mul_assoc,map_mul,MarkingCertificates.eval_bridge,hy,hi]
  rw [← decode_packedMul,actor_mul_1,← decode_packedMul,actor_mul_2,
    ← decode_packedMul,actor_mul_3,← decode_packedMul,actor_mul_4]

private theorem actor_moves_point : (MulAut.conj actor⁻¹) t₀ = (sourceP : Model) := by
  have hy : (SymmetricLinear.NormalEight.y^3)⁻¹ *
      SymmetricLinear.NormalEight.element 2 * SymmetricLinear.NormalEight.y^3 =
        SymmetricLinear.NormalEight.element 1 := by
    calc
      _ = SymmetricLinear.NormalEight.y⁻¹ *
        (SymmetricLinear.NormalEight.y⁻¹ *
          (SymmetricLinear.NormalEight.y⁻¹ * SymmetricLinear.NormalEight.element 2 *
            SymmetricLinear.NormalEight.y) * SymmetricLinear.NormalEight.y) *
          SymmetricLinear.NormalEight.y := by simp only [pow_succ,pow_zero,one_mul,mul_inv_rev,mul_assoc]
      _ = _ := by
        rw [SymmetricLinear.NormalEight.element_conj_y]
        change SymmetricLinear.NormalEight.y⁻¹ *
          (SymmetricLinear.NormalEight.y⁻¹ * SymmetricLinear.NormalEight.element 4 *
            SymmetricLinear.NormalEight.y) * SymmetricLinear.NormalEight.y = _
        rw [SymmetricLinear.NormalEight.element_conj_y]
        change SymmetricLinear.NormalEight.y⁻¹ * SymmetricLinear.NormalEight.element 6 *
          SymmetricLinear.NormalEight.y = _
        exact SymmetricLinear.NormalEight.element_conj_y 6
  have hym := congrArg (fun z : SymmetricLinear.max4Subgroup => (z : Model)) hy
  simp only [MulAut.conj_apply,inv_inv]
  change actor⁻¹ * t₀ * actor = _
  calc
    _ = bridge * (((SymmetricLinear.NormalEight.y : Model)^3)⁻¹ *
        (SymmetricLinear.NormalEight.element 2 : Model) * (SymmetricLinear.NormalEight.y : Model)^3) * bridge⁻¹ := by
      rw [← marking.2.1]
      change (bridge * _ * bridge⁻¹)⁻¹ *
        (bridge * (SymmetricLinear.NormalEight.element 2 : Model) * bridge⁻¹) *
        (bridge * _ * bridge⁻¹) = _
      group
    _ = bridge * (SymmetricLinear.NormalEight.element 1 : Model) * bridge⁻¹ :=
      congrArg (fun z : Model => bridge*z*bridge⁻¹) hym
    _ = _ := marking.1

private theorem source_point_conjugate : (MulAut.conj h) a = t₀ := by
  have hh := congrArg (MulAut.conj h) conjugates_t
  simpa only [MulAut.conj_apply,mul_assoc,mul_inv_cancel_left,mul_inv_cancel,mul_one] using hh.symm

private theorem kernel_mem_point_core (i : Fin 8192) :
    (kernelProduct i : Model) ∈ (centralizer ({t₀} : Set Model)).pCoreIn 2 := by
  have hm : eH (localKernelProduct i) ∈ firstCore := by
    rw [← firstKernel_eq_firstCore]
    exact (mem_firstKernel_iff _).mpr ⟨i,rfl⟩
  have hh := mem_map_of_mem (MulAut.conj h).toMonoidHom hm
  rw [firstCore_conjugate,source_point_conjugate] at hh
  simpa only [localKernelProduct,eH_sourceSubgroupEquivLocal,MulEquiv.toMonoidHom_eq_coe,
    MonoidHom.coe_coe,MulAut.conj_apply,mul_assoc,mul_inv_cancel_left,mul_inv_cancel,mul_one] using hh

private theorem kernel_one : (kernelProduct 1 : Model) = t₀ := by
  have hh : kernelProduct 1 = kernelFactor 0 := by
    change kernelFactor 0 * (1 * (1 * (1 * (1 * (1 * (1 * (1 * (1 * (1 * (1 * (1 * (1 * 1)))))))))))) = _
    simp only [mul_one]
  rw [hh]
  exact coe_sourceSeed_sq

private theorem points_distinct : t₀ ≠ (sourceP : Model) := by
  intro he
  have hi := kernelProduct_injective (Subtype.ext (kernel_one.trans he))
  exact (by decide : (1 : Fin 8192) ≠ 6607) hi

private theorem t_pure : IsConj a t₀ := isConj_iff.mpr ⟨h,source_point_conjugate⟩
private theorem p_pure : IsConj a (sourceP : Model) :=
  t_pure.trans (isConj_iff.mpr ⟨actor⁻¹,actor_moves_point⟩)

/-- The literal two-point core intersection used by the marked-plane search. -/
@[expose] def markedIntersection : Subgroup Model :=
  (centralizer ({t₀} : Set Model)).pCoreIn 2 ⊓
    (centralizer ({(sourceP : Model)} : Set Model)).pCoreIn 2

theorem markedIntersection_elementary : IsElementaryAbelian 2 markedIntersection :=
  point_core_intersection_elementary t₀ sourceP t_pure p_pure points_distinct

theorem markedIntersection_card_le : Nat.card markedIntersection ≤ 128 :=
  point_core_intersection_card_le t₀ sourceP t_pure p_pure points_distinct

private theorem conjugate_kernel_mem (m : Fin 8192) :
    (MulAut.conj actor⁻¹) (kernelProduct m : Model) ∈
      (centralizer ({(sourceP : Model)} : Set Model)).pCoreIn 2 := by
  have hh := mem_map_of_mem (MulAut.conj actor⁻¹).toMonoidHom (kernel_mem_point_core m)
  rw [map_pCoreIn_of_injective 2 _ _ (MulAut.conj actor⁻¹).injective,
    map_centralizer_equiv,Set.image_singleton,actor_moves_point] at hh
  exact hh

private theorem conjugation_of_intertwining (m n : Fin 8192) (mr nr : Vector ℕ 112)
    (hm : toMatrix (kernelProduct m : Model) = decodeRows mr)
    (hn : toMatrix (kernelProduct n : Model) = decodeRows nr)
    (hc : packedMul mr actorRows = packedMul actorRows nr) :
    (MulAut.conj actor⁻¹) (kernelProduct m : Model) = (kernelProduct n : Model) := by
  have he : (kernelProduct m : Model)*actor = actor*(kernelProduct n : Model) := by
    apply toMatrix_injective
    simpa only [map_mul,hm,hn,eval_actor,← decode_packedMul] using congrArg decodeRows hc
  simp only [MulAut.conj_apply,inv_inv]
  rw [mul_assoc,he,inv_mul_cancel_left]
@[expose] def generatorMask : Fin 7 → Fin 8192 := ![1,6,192,562,1048,2384,4184]
@[expose] def coordinate : Fin 128 → Fin 8192 := ![0,1,6,7,192,193,198,199,562,563,565,564,754,755,757,756,1048,1049,1054,1055,1240,1241,1246,1247,1578,1579,1581,1580,1770,1771,1773,1772,2384,2385,2390,2391,2448,2449,2454,2455,2915,2914,2916,2917,2979,2978,2980,2981,3400,3401,3406,3407,3464,3465,3470,3471,3963,3962,3964,3965,4027,4026,4028,4029,4184,4185,4190,4191,4249,4248,4255,4254,4715,4714,4716,4717,4778,4779,4781,4780,5185,5184,5191,5190,5248,5249,5254,5255,5746,5747,5749,5748,5811,5810,5812,5813,6408,6409,6414,6415,6601,6600,6607,6606,6970,6971,6973,6972,7163,7162,7164,7165,7441,7440,7447,7446,7632,7633,7638,7639,7971,7970,7972,7973,8162,8163,8165,8164]
@[expose] def parent : Fin 128 → Fin 128 := ![0,0,0,1,0,1,2,3,0,1,2,3,4,5,6,7,0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,51,52,53,54,55,56,57,58,59,60,61,62,63]
@[expose] def last : Fin 128 → Fin 7 := ![0,0,1,1,2,2,2,2,3,3,3,3,3,3,3,3,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6]
private theorem parent_lt (i : Fin 128) (hi : i ≠ 0) : parent i < i := by
  have hc : ∀ i : Fin 128, i ≠ 0 → parent i < i := by decide +kernel
  exact hc i hi
private theorem coordinate_injective : Function.Injective coordinate := by decide +kernel
private theorem coordinate_step (i : Fin 128) (hi : i ≠ 0) :
    maskMultiply (coordinate (parent i)).val (generatorMask (last i)).val = (coordinate i).val := by
  have hc : ∀ i : Fin 128, i ≠ 0 →
      maskMultiply (coordinate (parent i)).val (generatorMask (last i)).val = (coordinate i).val := by
    decide +kernel
  exact hc i hi
private theorem generator_mem (i : Fin 7) :
    (kernelProduct (generatorMask i) : Model) ∈ markedIntersection := by
  refine ⟨kernel_mem_point_core _,?_⟩
  fin_cases i
  · exact (conjugation_of_intertwining 5254 1 k5254 k1 eval_5254 eval_1
      (intertwine_left_0.trans intertwine_right_0.symm)) ▸ conjugate_kernel_mem 5254
  · exact (conjugation_of_intertwining 4552 6 k4552 k6 eval_4552 eval_6
      (intertwine_left_1.trans intertwine_right_1.symm)) ▸ conjugate_kernel_mem 4552
  · exact (conjugation_of_intertwining 2744 192 k2744 k192 eval_2744 eval_192
      (intertwine_left_2.trans intertwine_right_2.symm)) ▸ conjugate_kernel_mem 2744
  · exact (conjugation_of_intertwining 7889 562 k7889 k562 eval_7889 eval_562
      (intertwine_left_3.trans intertwine_right_3.symm)) ▸ conjugate_kernel_mem 7889
  · exact (conjugation_of_intertwining 1254 1048 k1254 k1048 eval_1254 eval_1048
      (intertwine_left_4.trans intertwine_right_4.symm)) ▸ conjugate_kernel_mem 1254
  · exact (conjugation_of_intertwining 2478 2384 k2478 k2384 eval_2478 eval_2384
      (intertwine_left_5.trans intertwine_right_5.symm)) ▸ conjugate_kernel_mem 2478
  · exact (conjugation_of_intertwining 4830 4184 k4830 k4184 eval_4830 eval_4184
      (intertwine_left_6.trans intertwine_right_6.symm)) ▸ conjugate_kernel_mem 4830

private theorem coordinate_mem (i : Fin 128) :
    (kernelProduct (coordinate i) : Model) ∈ markedIntersection := by
  induction i using Fin.strong_induction_on with
  | h i ih =>
    by_cases hi : i = 0
    · subst i
      have hz : kernelProduct (coordinate 0) = 1 := by
        change kernelProduct 0 = 1
        simp [kernelProduct]
      rw [hz]
      exact markedIntersection.one_mem
    · have he : kernelProduct (coordinate i) =
        kernelProduct (coordinate (parent i)) * kernelProduct (generatorMask (last i)) := by
        change maskProduct kernelFactor (coordinate i).val =
          maskProduct kernelFactor (coordinate (parent i)).val *
            maskProduct kernelFactor (generatorMask (last i)).val
        rw [← source_mask_multiply,coordinate_step i hi]
      rw [he]
      exact markedIntersection.mul_mem (ih (parent i) (parent_lt i hi)) (generator_mem (last i))

/-- All 128 distinct literal native words lie in the intersection, saturating
the extraspecial order bound. -/
theorem markedIntersection_card : Nat.card markedIntersection = 128 := by
  apply le_antisymm markedIntersection_card_le
  let f : Fin 128 → markedIntersection := fun i => ⟨kernelProduct (coordinate i),coordinate_mem i⟩
  have hf : Function.Injective f := by
    intro i j hij
    apply coordinate_injective
    apply kernelProduct_injective
    exact Subtype.ext (congrArg (fun u : markedIntersection => (u : Model)) hij)
  simpa only [Nat.card_fin] using Nat.card_le_card_of_injective f hf

/-- The native embedding and exhaustive coordinates, with no imported JSON
or first-row-only equality assertion. -/
theorem mem_markedIntersection_iff (u : Model) : u ∈ markedIntersection ↔
    ∃ i : Fin 128, (kernelProduct (coordinate i) : Model) = u := by
  let f : Fin 128 → markedIntersection := fun i => ⟨kernelProduct (coordinate i),coordinate_mem i⟩
  have hf : Function.Injective f := by
    intro i j hij
    apply coordinate_injective
    apply kernelProduct_injective
    exact Subtype.ext (congrArg (fun u : markedIntersection => (u : Model)) hij)
  have hs : Function.Surjective f := (hf.bijective_of_nat_card_le (by rw [markedIntersection_card,Nat.card_fin])).2
  constructor
  · intro hu
    obtain ⟨i,hi⟩ := hs ⟨u,hu⟩
    exact ⟨i,congrArg (fun u : markedIntersection => (u : Model)) hi⟩
  · rintro ⟨i,rfl⟩
    exact coordinate_mem i

/-- Every original all-row-two source group containing the two marked points
lies in this exact 128-element native container. -/
theorem marked_all_row_two_le (X : Subgroup Model) [IsElementaryAbelian 2 X]
    (hpure : ∀ x ∈ X, x ≠ 1 → IsConj a x)
    (hno : ¬ ∃ g : Model, PureTwoA.NativePair.nativePair.map
      (MulAut.conj g).toMonoidHom ≤ X)
    (ht : t₀ ∈ X) (hp : (sourceP : Model) ∈ X) : X ≤ markedIntersection := by
  have ht1 : t₀ ≠ 1 := by
    intro he
    have ha := isConj_one_left.mp (he ▸ t_pure)
    have ho := orderOf_a
    simp [ha] at ho
  have hp1 : (sourceP : Model) ≠ 1 := by
    intro he
    have ha := isConj_one_left.mp (he ▸ p_pure)
    have ho := orderOf_a
    simp [ha] at ho
  exact le_inf (le_point_core X hpure hno t₀ ht ht1) (le_point_core X hpure hno sourceP hp hp1)

/-- One ambient conjugator puts the original group and every eligible
sixteen overgroup into the same exhaustively certified native intersection. -/
theorem simultaneous_marked_overgroup_coordinates
    (X : Subgroup Model) [IsElementaryAbelian 2 X]
    (hcard : 4 < Nat.card X) (hpure : ∀ x ∈ X, x ≠ 1 → IsConj a x)
    (hno : ¬ ∃ g : Model, PureTwoA.NativePair.nativePair.map
      (MulAut.conj g).toMonoidHom ≤ X) :
    ∃ g : Model,
      X.map (MulAut.conj g).toMonoidHom ≤ markedIntersection ∧
      (sixteenHull X).map (MulAut.conj g).toMonoidHom ≤ markedIntersection ∧
      (∀ Y ∈ sixteenOvergroups X, Y.map (MulAut.conj g).toMonoidHom ≤ markedIntersection) ∧
      (∀ u ∈ sixteenHull X, ∃ i : Fin 128, (kernelProduct (coordinate i) : Model) = (MulAut.conj g) u) ∧
      (normalizer (X : Set Model)).map (MulAut.conj g).toMonoidHom =
        normalizer (X.map (MulAut.conj g).toMonoidHom : Set Model) := by
  obtain ⟨k,hplane,_,_⟩ := max4_group_placement X hcard hpure hno
  let g := bridge*k⁻¹
  have hp0 : (SymmetricLinear.NormalEight.element 1 : Model) ∈
      CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover.KernelOrders.PureNormalizers.max4Plane := by
    exact ⟨_,⟨(1 : Fin 4),rfl⟩,rfl⟩
  have ht0 : (SymmetricLinear.NormalEight.element 2 : Model) ∈
      CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover.KernelOrders.PureNormalizers.max4Plane := by
    exact ⟨_,⟨(2 : Fin 4),rfl⟩,rfl⟩
  have hpoints (Y : Subgroup Model) (hXY : X ≤ Y) :
      t₀ ∈ Y.map (MulAut.conj g).toMonoidHom ∧
        (sourceP : Model) ∈ Y.map (MulAut.conj g).toMonoidHom := by
    constructor
    · refine ⟨(MulAut.conj k) (SymmetricLinear.NormalEight.element 2 : Model),
        hXY (hplane (mem_map_of_mem _ ht0)),?_⟩
      change (bridge*k⁻¹)*(k*_ *k⁻¹)*(bridge*k⁻¹)⁻¹ = t₀
      simpa only [MulAut.conj_apply,mul_inv_rev,inv_inv,mul_assoc,inv_mul_cancel_left,
        inv_mul_cancel,mul_one] using marking.2.1
    · refine ⟨(MulAut.conj k) (SymmetricLinear.NormalEight.element 1 : Model),
        hXY (hplane (mem_map_of_mem _ hp0)),?_⟩
      change (bridge*k⁻¹)*(k*_ *k⁻¹)*(bridge*k⁻¹)⁻¹ = (sourceP : Model)
      simpa only [MulAut.conj_apply,mul_inv_rev,inv_inv,mul_assoc,inv_mul_cancel_left,
        inv_mul_cancel,mul_one] using marking.1
  have hplace (Y : Subgroup Model) [IsElementaryAbelian 2 Y]
      (hXY : X ≤ Y) (hp : ∀ y ∈ Y, y ≠ 1 → IsConj a y)
      (hn : ¬ ∃ c : Model, PureTwoA.NativePair.nativePair.map
        (MulAut.conj c).toMonoidHom ≤ Y) :
      Y.map (MulAut.conj g).toMonoidHom ≤ markedIntersection := by
    let : IsElementaryAbelian 2 (Y.map (MulAut.conj g).toMonoidHom) := IsElementaryAbelian.map _
    apply marked_all_row_two_le _ ?_ (no_native_pair_map Y hn g)
      (hpoints Y hXY).1 (hpoints Y hXY).2
    rintro y ⟨z,hz,rfl⟩ hy
    exact (hp z hz (fun he => hy (by simp [he]))).trans (isConj_iff.mpr ⟨g,rfl⟩)
  have hXplace := hplace X le_rfl hpure hno
  have hfamily : ∀ Y ∈ sixteenOvergroups X,
      Y.map (MulAut.conj g).toMonoidHom ≤ markedIntersection := by
    rintro Y ⟨hXY,_,hE,hp,hn⟩
    let := hE
    exact hplace Y hXY hp hn
  have hhull : (sixteenHull X).map (MulAut.conj g).toMonoidHom ≤ markedIntersection := by
    apply map_le_iff_le_comap.mpr
    exact sup_le (map_le_iff_le_comap.mp hXplace)
      (sSup_le fun Y hY => map_le_iff_le_comap.mp (hfamily Y hY))
  refine ⟨g,hXplace,hhull,hfamily,?_,map_equiv_normalizer_eq _ _⟩
  intro u hu
  exact (mem_markedIntersection_iff _).mp (hhull (mem_map_of_mem _ hu))

end Janko4.LocalStructure.PureFirstNormalizers.AllRowTwo.MarkedIntersection
