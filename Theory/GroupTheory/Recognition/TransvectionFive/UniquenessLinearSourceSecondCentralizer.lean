module
public import Theory.GroupTheory.Recognition.TransvectionFive.UniquenessLinearSourceGenerationReduction
public import Theory.GroupTheory.UniqueFixedCosetCommutingProducts
import all Theory.GroupTheory.Recognition.TransvectionFive.UniquenessLinearSourceRectangleOrbits
import all Theory.GroupTheory.Recognition.TransvectionFive.UniquenessLinearSourcePlaneCoordinates

/-!
# The two fixed-coset steps in the linear second centralizer

The marked codes 34 and 52 span a literal four-group B in the intersection
of the original rectangles. Every nonidentity element of B is in the second
involution class. A checked four-element table shows that every nonidentity
coset of the plane modulo B has a point-class representative. Thus its image
in C_G(B)/B has a unique fixed coset in the quotient by (L ∩ C_G(B))/B.
Two quotient classes are separated directly by point-class lifts, without
assuming the source's 3/12 orbit calculation.

The first application of 7.5 is in C_G(t), using the marked point and code 2;
their products with t have different ambient fusion types. The second
application is in C_G(B)/B. The literal maps, kernels and relative stabilizers
are retained throughout. The normal elementary criterion supplies the final
contradiction once normality of the plane image is proved.

`SecondCentralizerLocalData` records the two remaining local calculations:
relative normality of this plane image, and transport of a point-free four-group
from the selected commuting pairs to B by an element of L. The concluding
source comparison is conditional on this data; no ambient centralizer bound,
simplicity of L, or final classification is assumed. In particular this module
does not assert the source identity D = O²(I), and never replaces it by O₂(I).

Source: Aschbacher, *Sporadic Groups* (1994), 7.5, p.20, and the linear branch
of 41.1, p.220. The internal imports reuse the existing marked coordinate and
second-involution implementations without widening their public boundaries.
-/

public noncomputable section
open Subgroup
namespace Theory.GroupTheory.TransvectionFive.UniquenessLinear
open PlaneCensus PlaneTensor
variable {G : Type*} [Group G] {z : G} (F : MarkedCentralizer z)

private def fourCodes : Finset Code := {0,22,34,52}
private theorem fourCodes_xor : ∀ x ∈ fourCodes, ∀ y ∈ fourCodes, x ^^^ y ∈ fourCodes := by decide
private theorem fourCodes_nonpure : ∀ x ∈ fourCodes, pure x = false := by decide
private theorem fourCodes_cover : ∀ x : Code, x ∉ fourCodes →
    ∃ b ∈ fourCodes, pure (x ^^^ b) = true := by decide

private theorem element_square (x : Code) : element F x * element F x = 1 := by
  rw [← element_xor, BitVec.xor_self]
  exact element_zero F
private theorem element_inv (x : Code) : (element F x)⁻¹ = element F x :=
  inv_eq_of_mul_eq_one_right (element_square F x)

/-- The literal marked field four-group, with its four rectangle coordinates. -/
def sourceSecondFour : Subgroup G where
  carrier := {a | ∃ x ∈ fourCodes, element F x = a}
  one_mem' := ⟨0, by decide, element_zero F⟩
  mul_mem' := by
    rintro _ _ ⟨x,hx,rfl⟩ ⟨y,hy,rfl⟩
    exact ⟨x ^^^ y, fourCodes_xor x hx y hy, element_xor F x y⟩
  inv_mem' := by
    rintro _ ⟨x,hx,rfl⟩
    exact ⟨x,hx,(element_inv F x).symm⟩

/-- The four-group is contained in the original plane. -/
theorem sourceSecondFour_le_plane : sourceSecondFour F ≤ F.plane := by
  rintro _ ⟨x,_,rfl⟩
  exact element_mem F x

private theorem element_mem_sourceSecondFour (x : Code) :
    element F x ∈ sourceSecondFour F ↔ x ∈ fourCodes := by
  constructor
  · rintro ⟨y,hy,he⟩
    exact (element_injective F he) ▸ hy
  · exact fun h => ⟨x,h,rfl⟩

/-- The prescribed second involution is in the four-group. -/
theorem sourceSecondFour_second_mem : planeSecondPoint F ∈ sourceSecondFour F :=
  (element_mem_sourceSecondFour F 34).mpr (by decide)

/-- Its four marked coordinates are distinct. -/
theorem sourceSecondFour_card : Nat.card (sourceSecondFour F) = 4 := by
  have he : (sourceSecondFour F : Set G) = element F '' (fourCodes : Set Code) := by
    ext g
    rfl
  change Nat.card (sourceSecondFour F : Set G) = 4
  rw [Nat.card_coe_set_eq, he, Set.ncard_image_of_injective _ (element_injective F),
    Set.ncard_coe_finset]
  decide

/-- The marked field four-group is the literal join of its two displayed
rank-two generators. -/
theorem sourceSecondFour_eq : sourceSecondFour F =
    zpowers (planeSecondPoint F) ⊔ zpowers (element F 52) := by
  apply le_antisymm
  · rintro _ ⟨c,hc,rfl⟩
    have hc' : c = 0 ∨ c = 22 ∨ c = 34 ∨ c = 52 := by
      simpa only [fourCodes, Finset.mem_insert, Finset.mem_singleton] using hc
    rcases hc' with rfl | rfl | rfl | rfl
    · rw [element_zero]
      exact one_mem _
    · have he : element F 22 = planeSecondPoint F * element F 52 :=
        element_xor F 34 52
      rw [he]
      exact mul_mem_sup (mem_zpowers _) (mem_zpowers _)
    · exact (show zpowers (planeSecondPoint F) ≤ _ from le_sup_left) (mem_zpowers _)
    · exact (show zpowers (element F 52) ≤ _ from le_sup_right) (mem_zpowers _)
  · apply sup_le
    · exact zpowers_le.mpr (sourceSecondFour_second_mem F)
    · exact zpowers_le.mpr ((element_mem_sourceSecondFour F 52).mpr (by decide))

/-- The field four-group lies in the original common rectangle E. -/
theorem sourceSecondFour_le_threeSpace : sourceSecondFour F ≤ F.threeSpace := by
  rintro _ ⟨c,hc,rfl⟩
  have hc0 : decode c 0 0 = 0 ∧ decode c 1 0 = 0 :=
    (by decide : ∀ c ∈ fourCodes, decode c 0 0 = 0 ∧ decode c 1 0 = 0) c hc
  apply (F.mem_pullback_iff Model.threeSpace
    ⟨element F c,F.pullback_le _ (element_mem F c)⟩).mpr
  rw [element_model]
  apply (RectangleCoordinates.mem3_iff _).mpr
  rw [UniquenessMathieu.SourceNormalizer.modelPlaneCoordinates_matrix,
    UniquenessMathieu.SourceNormalizer.modelPlaneCoordinates.apply_symm_apply]
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    simp_all [Matrix.single]

variable [Finite G]

/-- No element of the four-group is fused to the marked point. -/
theorem sourceSecondFour_no_point (hlinear : F.LinearFusion) {x : G}
    (hx : x ∈ sourceSecondFour F) : ¬ IsConj z x := by
  obtain ⟨c,hc,rfl⟩ := hx
  rw [fusion_iff_pure F hlinear, fourCodes_nonpure c hc]
  decide

/-- Every nontrivial plane coset modulo the four-group contains a point involution. -/
theorem sourceSecondFour_point_lift (hlinear : F.LinearFusion)
    {a : G} (ha : a ∈ F.plane) (haB : a ∉ sourceSecondFour F) :
    ∃ b : sourceSecondFour F, IsConj z (a * (b : G)) := by
  obtain ⟨c,hc⟩ := (sourceEquiv F).surjective ⟨a,ha⟩
  have hca : element F c = a := congrArg Subtype.val hc
  have hcb : c ∉ fourCodes := by
    intro hm
    exact haB (hca ▸ (element_mem_sourceSecondFour F c).mpr hm)
  obtain ⟨b,hb,hpure⟩ := fourCodes_cover c hcb
  refine ⟨⟨element F b,(element_mem_sourceSecondFour F b).mpr hb⟩,?_⟩
  rw [← hca, ← element_xor]
  exact (fusion_iff_pure F hlinear _).mpr hpure

omit [Finite G] in
private theorem plane_commute {a b : G} (ha : a ∈ F.plane) (hb : b ∈ F.plane) :
    Commute a b := by
  obtain ⟨x,hx⟩ := (sourceEquiv F).surjective ⟨a,ha⟩
  obtain ⟨y,hy⟩ := (sourceEquiv F).surjective ⟨b,hb⟩
  have hx' : element F x = a := congrArg Subtype.val hx
  have hy' : element F y = b := congrArg Subtype.val hy
  rw [← hx', ← hy']
  apply (commute_iff_eq _ _).mpr
  rw [← element_xor, ← element_xor, BitVec.xor_comm]

abbrev secondFourCentralizer : Subgroup G := centralizer (sourceSecondFour F : Set G)
abbrev secondFourKernel : Subgroup (secondFourCentralizer F) :=
  (sourceSecondFour F).subgroupOf (secondFourCentralizer F)

instance secondFourKernel_normal : (secondFourKernel F).Normal where
  conj_mem x hx g := by
    have he : g * x = x * g := Subtype.ext
      ((mem_centralizer_iff.mp g.property (x : G) hx).symm)
    rw [he, mul_inv_cancel_right]
    exact hx

omit [Finite G] in
theorem plane_le_secondFourCentralizer : F.plane ≤ secondFourCentralizer F := by
  intro a ha
  apply mem_centralizer_iff.mpr
  intro b hb
  exact (plane_commute F (sourceSecondFour_le_plane F hb) ha).eq

abbrev secondFourQuotient := secondFourCentralizer F ⧸ secondFourKernel F
abbrev secondFourStabilizer : Subgroup (secondFourCentralizer F) :=
  (normalizerSpan F).subgroupOf (secondFourCentralizer F)
abbrev secondFourStabilizerImage : Subgroup (secondFourQuotient F) :=
  (secondFourStabilizer F).map (QuotientGroup.mk' (secondFourKernel F))
abbrev secondFourPlaneImage : Subgroup (secondFourStabilizerImage F) :=
  (((F.plane).subgroupOf (secondFourCentralizer F)).map
    (QuotientGroup.mk' (secondFourKernel F))).subgroupOf (secondFourStabilizerImage F)

omit [Finite G] in
private theorem plane_le_span : F.plane ≤ normalizerSpan F :=
  (F.pullback_le _).trans (point_centralizer_le_normalizerSpan F)

private theorem point_unique_in_subgroup (hlinear : F.LinearFusion)
    (K : Subgroup G) (a : K) (haL : (a : G) ∈ normalizerSpan F)
    (ha : IsConj z (a : G)) :
    ∃! q : K ⧸ (normalizerSpan F).subgroupOf K, a • q = q := by
  have hu : ∃! q : G ⧸ normalizerSpan F, (a : G) • q = q := by
    refine ⟨GraphUniquenessSystem.Cosets.vertex (normalizerSpan F) 1, ?_, ?_⟩
    · simpa only [GraphUniquenessSystem.Cosets.smul_vertex, mul_one] using
        (GraphUniquenessSystem.Cosets.vertex_eq_base (normalizerSpan F) (a : G)).mpr haL
    · exact normalizerSpan_point_unique_fixed F hlinear ⟨a,haL⟩ ha
  apply UniqueFixedCoset.unique_of_transporter (G := K)
    (show a ∈ (normalizerSpan F).subgroupOf K from haL)
  intro g hg
  change (g : G) ∈ normalizerSpan F
  exact UniqueFixedCoset.transporter_mem (G := G) haL hu
    (show (g : G) * (a : G) * (g : G)⁻¹ ∈ normalizerSpan F from hg)

/-- Point representatives lift through the actual centralizer quotient map. -/
theorem secondFourPlaneImage_point_lifts (hlinear : F.LinearFusion)
    (x : secondFourPlaneImage F) (hx : x ≠ 1) :
    ∃ y : secondFourStabilizer F,
      QuotientGroup.mk' (secondFourKernel F) y =
        ((x : secondFourStabilizerImage F) : secondFourQuotient F) ∧
      IsConj z ((y : secondFourCentralizer F) : G) := by
  obtain ⟨a, ha, he⟩ := x.property
  have haB : (a : G) ∉ sourceSecondFour F := by
    intro hm
    have hzq : QuotientGroup.mk' (secondFourKernel F) a = 1 :=
      (QuotientGroup.eq_one_iff a).mpr hm
    apply hx
    apply Subtype.ext
    apply Subtype.ext
    exact he.symm.trans hzq
  obtain ⟨b,hb⟩ := sourceSecondFour_point_lift F hlinear ha haB
  let bK : secondFourCentralizer F :=
    ⟨b, plane_le_secondFourCentralizer F (sourceSecondFour_le_plane F b.property)⟩
  let y : secondFourStabilizer F := ⟨a * bK,
    (normalizerSpan F).mul_mem (plane_le_span F ha)
      (plane_le_span F (sourceSecondFour_le_plane F b.property))⟩
  refine ⟨y, ?_, hb⟩
  change QuotientGroup.mk' (secondFourKernel F) (a * bK) = _
  rw [map_mul, show QuotientGroup.mk' (secondFourKernel F) bK = 1 from
    (QuotientGroup.eq_one_iff bK).mpr b.property, mul_one]
  exact he

/-- The marked point lifts give unique fixed cosets in the centralizer quotient. -/
theorem secondFourPlaneImage_unique_fixed (hlinear : F.LinearFusion)
    (x : secondFourPlaneImage F) (hx : x ≠ 1) :
    ∃! q : secondFourQuotient F ⧸ secondFourStabilizerImage F,
      ((x : secondFourStabilizerImage F) : secondFourQuotient F) • q = q := by
  obtain ⟨y,hy,hpoint⟩ := secondFourPlaneImage_point_lifts F hlinear x hx
  rw [← hy]
  apply UniqueFixedCoset.unique_map_of_surjective _ (QuotientGroup.mk'_surjective _)
    (show (QuotientGroup.mk' (secondFourKernel F)).ker ≤ secondFourStabilizer F from ?_)
    y.property
  · exact point_unique_in_subgroup F hlinear (secondFourCentralizer F) (y : secondFourCentralizer F)
      (show ((y : secondFourCentralizer F) : G) ∈ normalizerSpan F from y.property) hpoint
  · intro a ha
    have hab : (a : G) ∈ sourceSecondFour F :=
      (QuotientGroup.eq_one_iff a).mp ha
    exact plane_le_span F (sourceSecondFour_le_plane F hab)

omit [Finite G] in
/-- The actual plane image is a binary elementary group. -/
theorem secondFourPlaneImage_square (x : secondFourPlaneImage F) : x ^ 2 = 1 := by
  obtain ⟨a,ha,he⟩ := x.property
  have ha2 : a ^ 2 = 1 := by
    obtain ⟨c,hc⟩ := (sourceEquiv F).surjective ⟨a,ha⟩
    have hca : element F c = (a : G) := congrArg Subtype.val hc
    apply Subtype.ext
    change (a : G) ^ 2 = 1
    rw [← hca, pow_two]
    exact element_square F c
  apply Subtype.ext
  apply Subtype.ext
  change (((x : secondFourStabilizerImage F) : secondFourQuotient F)) ^ 2 = 1
  change QuotientGroup.mk' (secondFourKernel F) a = ((x : secondFourStabilizerImage F) : secondFourQuotient F) at he
  rw [← he, ← map_pow, ha2, map_one]

private def planeInFourCentralizer (c : Code) : secondFourCentralizer F :=
  ⟨element F c, plane_le_secondFourCentralizer F (element_mem F c)⟩

private def secondFourPlaneCode (c : Code) : secondFourPlaneImage F :=
  ⟨⟨QuotientGroup.mk' (secondFourKernel F) (planeInFourCentralizer F c),
    ⟨planeInFourCentralizer F c, plane_le_span F (element_mem F c), rfl⟩⟩,
    ⟨planeInFourCentralizer F c, element_mem F c, rfl⟩⟩

private theorem secondFourPlaneCode_ne_one (hlinear : F.LinearFusion) {c : Code}
    (hc : pure c = true) : secondFourPlaneCode F c ≠ 1 := by
  intro he
  have hh : QuotientGroup.mk' (secondFourKernel F) (planeInFourCentralizer F c) = 1 :=
    congrArg (fun x : secondFourPlaneImage F =>
      ((x : secondFourStabilizerImage F) : secondFourQuotient F)) he
  have hm : element F c ∈ sourceSecondFour F := (QuotientGroup.eq_one_iff (N := secondFourKernel F) (planeInFourCentralizer F c)).mp hh
  exact sourceSecondFour_no_point F hlinear hm ((fusion_iff_pure F hlinear c).mpr hc)

private theorem secondFour_point_cosets_not_conj (hlinear : F.LinearFusion) :
    ¬ IsConj (QuotientGroup.mk' (secondFourKernel F) (planeInFourCentralizer F 4))
      (QuotientGroup.mk' (secondFourKernel F) (planeInFourCentralizer F 1)) := by
  intro hh
  obtain ⟨g,hg⟩ := isConj_iff.mp hh
  obtain ⟨k,rfl⟩ := QuotientGroup.mk'_surjective (secondFourKernel F) g
  let x := planeInFourCentralizer F 4
  let y := planeInFourCentralizer F 1
  let q := QuotientGroup.mk' (secondFourKernel F)
  have hq : q (k * x * k⁻¹) = q y := by
    simpa only [map_mul, map_inv] using hg
  let d := y⁻¹ * (k * x * k⁻¹)
  have hd : d ∈ secondFourKernel F := by
    apply (QuotientGroup.eq_one_iff d).mp
    change q d = 1
    dsimp only [d]
    rw [map_mul, map_inv, hq, inv_mul_cancel]
  obtain ⟨c,hc,he⟩ := hd
  have hconj : (k : G) * element F 4 * (k : G)⁻¹ = element F 1 * element F c := by
    rw [he]
    change (k : G) * element F 4 * (k : G)⁻¹ =
      element F 1 * ((element F 1)⁻¹ * ((k : G) * element F 4 * (k : G)⁻¹))
    rw [mul_inv_cancel_left]
  have h22 : (k : G) * element F 22 * (k : G)⁻¹ = element F 22 := by
    rw [← mem_centralizer_iff.mp k.property (element F 22)
      ((element_mem_sourceSecondFour F 22).mpr (by decide)), mul_inv_cancel_right]
  have hconj2 : (k : G) * element F 18 * (k : G)⁻¹ =
      element F ((1 ^^^ c) ^^^ 22) := by
    have hex : element F 18 = element F 4 * element F 22 := element_xor F 4 22
    rw [hex, element_xor F (1 ^^^ c) 22, element_xor F 1 c]
    calc
      (k : G) * (element F 4 * element F 22) * (k : G)⁻¹ =
        ((k : G) * element F 4 * (k : G)⁻¹) *
          ((k : G) * element F 22 * (k : G)⁻¹) := by group
      _ = _ := by rw [hconj,h22]
  have hp : pure (1 ^^^ c) = true := by
    apply (fusion_iff_pure F hlinear _).mp
    apply ((fusion_iff_pure F hlinear 4).mpr (by decide)).trans
    exact isConj_iff.mpr ⟨k, hconj.trans (element_xor F 1 c).symm⟩
  have hp2 : pure ((1 ^^^ c) ^^^ 22) = true := by
    apply (fusion_iff_pure F hlinear _).mp
    exact ((fusion_iff_pure F hlinear 18).mpr (by decide)).trans
      (isConj_iff.mpr ⟨k,hconj2⟩)
  exact (by decide : ∀ c ∈ fourCodes,
    pure (1 ^^^ c) = true → pure ((1 ^^^ c) ^^^ 22) = true → False) c hc hp hp2

/-- Two classes in the literal centralizer quotient are separated by their
point-class lifts. The first coset has three such lifts, whereas the second has
only one; the proof uses two distinct lifts and the checked four-element table. -/
theorem secondFourPlaneImage_two_classes (hlinear : F.LinearFusion) :
    ∃ a b : secondFourPlaneImage F, a ≠ 1 ∧ b ≠ 1 ∧
      ¬ IsConj (a : secondFourStabilizerImage F) (b : secondFourStabilizerImage F) := by
  refine ⟨secondFourPlaneCode F 4, secondFourPlaneCode F 1,
    secondFourPlaneCode_ne_one F hlinear (by decide : PlaneCensus.pure 4 = true),
    secondFourPlaneCode_ne_one F hlinear (by decide : PlaneCensus.pure 1 = true), ?_⟩
  intro h
  exact secondFour_point_cosets_not_conj F hlinear
    ((secondFourStabilizerImage F).subtype.map_isConj h)

/-- The second use of 7.5, retaining relative normality in the quotient stabilizer. -/
theorem secondFour_centralizer_le_of_quotient_classes (hlinear : F.LinearFusion)
    (hnormal : (secondFourPlaneImage F).Normal)
    (a b : secondFourPlaneImage F) (ha : a ≠ 1) (hb : b ≠ 1)
    (hne : ¬ IsConj (a : secondFourStabilizerImage F) (b : secondFourStabilizerImage F)) :
    secondFourCentralizer F ≤ normalizerSpan F := by
  let := hnormal
  apply Subgroup.subgroupOf_eq_top.mp
  apply UniqueFixedCoset.eq_top_of_normal_binary_image (secondFourStabilizer F)
    (QuotientGroup.mk' (secondFourKernel F)) (QuotientGroup.mk'_surjective _)
    (show (QuotientGroup.mk' (secondFourKernel F)).ker ≤ secondFourStabilizer F from ?_)
    (secondFourPlaneImage F) (secondFourPlaneImage_square F) a b ha hb hne
  · intro x hx
    obtain ⟨y,hy,hpoint⟩ := secondFourPlaneImage_point_lifts F hlinear x hx
    refine ⟨y,hy,?_⟩
    exact point_unique_in_subgroup F hlinear (secondFourCentralizer F)
      (y : secondFourCentralizer F)
      (show ((y : secondFourCentralizer F) : G) ∈ normalizerSpan F from y.property) hpoint
  · intro x hx
    have hB : (x : G) ∈ sourceSecondFour F :=
      (QuotientGroup.eq_one_iff x).mp hx
    exact plane_le_span F (sourceSecondFour_le_plane F hB)

abbrev secondCentralizer : Subgroup G := centralizer ({planeSecondPoint F} : Set G)
abbrev secondStabilizer : Subgroup (secondCentralizer F) :=
  (normalizerSpan F).subgroupOf (secondCentralizer F)

private def secondCode (c : Code) : secondStabilizer F :=
  ⟨⟨element F c, mem_centralizer_singleton_iff.mpr
    (plane_commute F (element_mem F c) (planeSecondPoint_mem F)).eq⟩,
    plane_le_span F (element_mem F c)⟩

def secondCentralizerPoint : secondStabilizer F := secondCode F 4
def secondCentralizerOtherPoint : secondStabilizer F := secondCode F 2

omit [Finite G] in
theorem secondCentralizerPoint_val :
    ((secondCentralizerPoint F : secondCentralizer F) : G) = z := element_point F

omit [Finite G] in
theorem secondCentralizerOtherPoint_val :
    ((secondCentralizerOtherPoint F : secondCentralizer F) : G) = element F 2 := by rfl

omit [Finite G] in
private theorem secondCode_order {c : Code} (hc : c ≠ 0) : orderOf (secondCode F c) = 2 := by
  apply orderOf_eq_prime
  · apply Subtype.ext
    apply Subtype.ext
    change element F c ^ 2 = 1
    rw [pow_two]
    exact element_square F c
  · intro he
    have he' : element F c = element F 0 := by
      rw [element_zero]
      exact congrArg (fun a : secondStabilizer F => ((a : secondCentralizer F) : G)) he
    exact hc (element_injective F he')

/-- Multiplication by the fixed second involution separates two point classes
in its full centralizer. -/
theorem secondCentralizer_two_point_classes (hlinear : F.LinearFusion) :
    ¬ IsConj (secondCentralizerPoint F : secondCentralizer F)
      (secondCentralizerOtherPoint F : secondCentralizer F) := by
  intro hc
  obtain ⟨g,hg⟩ := isConj_iff.mp hc
  have hgpoint : (g : G) * z * (g : G)⁻¹ = element F 2 := by
    have hh := congrArg Subtype.val hg
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv, secondCentralizerPoint_val,
      secondCentralizerOtherPoint_val] using hh
  have hgt : (g : G) * planeSecondPoint F * (g : G)⁻¹ = planeSecondPoint F := by
    rw [mem_centralizer_singleton_iff.mp g.property, mul_inv_cancel_right]
  have he : IsConj (element F 38) (element F 32) := by
    have hleft : element F 38 = planeSecondPoint F * z := by
      calc
        element F 38 = element F 34 * element F 4 := element_xor F 34 4
        _ = _ := congrArg (fun y => planeSecondPoint F * y) (element_point F)
    have hright : element F 32 = planeSecondPoint F * element F 2 := element_xor F 34 2
    rw [hleft,hright]
    apply isConj_iff.mpr
    refine ⟨g, ?_⟩
    calc
      (g : G) * (planeSecondPoint F * z) * (g : G)⁻¹ =
          ((g : G) * planeSecondPoint F * (g : G)⁻¹) *
            ((g : G) * z * (g : G)⁻¹) := by group
      _ = _ := by rw [hgt,hgpoint]
  have hpoint : IsConj z (element F 32) := (fusion_iff_pure F hlinear _).mpr (by decide)
  have hnot : ¬ IsConj z (element F 38) := by
    rw [fusion_iff_pure F hlinear]
    decide
  exact hnot (hpoint.trans he.symm)

private theorem secondCode_unique (hlinear : F.LinearFusion) {c : Code}
    (hc : pure c = true) :
    ∃! q : secondCentralizer F ⧸ secondStabilizer F,
      (secondCode F c : secondCentralizer F) • q = q :=
  point_unique_in_subgroup F hlinear (secondCentralizer F)
    (secondCode F c : secondCentralizer F) (secondCode F c).property
    ((fusion_iff_pure F hlinear c).mpr hc)

/-- The first use of source 7.5 takes place in the literal full centralizer
of the second involution. Both selected classes and their unique fixed cosets
are proved from the original 21-point fusion set. -/
theorem second_centralizer_le_of_commuting_products (hlinear : F.LinearFusion)
    (hprod : ∀ a b : secondStabilizer F,
      IsConj (secondCentralizerPoint F) a →
      (IsConj (secondCentralizerPoint F) b ∨ IsConj (secondCentralizerOtherPoint F) b) →
      a ≠ b → Commute a b →
      centralizer ({planeSecondPoint F, (((a * b : secondStabilizer F) : secondCentralizer F) : G)} : Set G)
        ≤ normalizerSpan F) :
    secondCentralizer F ≤ normalizerSpan F := by
  apply Subgroup.subgroupOf_eq_top.mp
  apply UniqueFixedCoset.eq_top_of_commuting_products (secondStabilizer F)
    (secondCentralizerPoint F) (secondCentralizerOtherPoint F)
    (secondCode_order F (by decide : (4 : Code) ≠ 0))
    (secondCode_order F (by decide : (2 : Code) ≠ 0))
    (secondCentralizer_two_point_classes F hlinear)
  · intro x hx
    rcases hx with hx | hx
    · exact UniqueFixedCoset.unique_of_isConj (secondCode_unique F hlinear (by decide : PlaneCensus.pure 4 = true)) hx
    · exact UniqueFixedCoset.unique_of_isConj (secondCode_unique F hlinear (by decide : PlaneCensus.pure 2 = true)) hx
  · intro a b ha hb hab hcomm
    have ha' := UniqueFixedCoset.fusion_of_unique
      (secondCode_unique F hlinear (by decide : PlaneCensus.pure 4 = true)) ha
    have hb' : IsConj (secondCentralizerPoint F) b ∨ IsConj (secondCentralizerOtherPoint F) b :=
      hb.imp (UniqueFixedCoset.fusion_of_unique (secondCode_unique F hlinear (by decide : PlaneCensus.pure 4 = true)))
        (UniqueFixedCoset.fusion_of_unique (secondCode_unique F hlinear (by decide : PlaneCensus.pure 2 = true)))
    intro g hg
    apply hprod a b ha' hb' hab hcomm
    apply mem_centralizer_iff.mpr
    intro x hx
    rcases hx with rfl | hx
    · exact (mem_centralizer_singleton_iff.mp g.property).symm
    · have he : x = (((a * b : secondStabilizer F) : secondCentralizer F) : G) :=
        Set.mem_singleton_iff.mp hx
      rw [he]
      exact (congrArg Subtype.val (mem_centralizer_singleton_iff.mp hg)).symm

/-- The remaining local calculations of source 41.1. These statements involve
only the generated subgroup, its literal centralizer intersection and quotient.
The four-group transport must retain a conjugator in the generated subgroup;
normality is relative to the displayed quotient stabilizer. -/
structure SecondCentralizerLocalData where
  plane_normal : (secondFourPlaneImage F).Normal
  four_transport : ∀ a b : secondStabilizer F,
    IsConj (secondCentralizerPoint F) a →
    (IsConj (secondCentralizerPoint F) b ∨ IsConj (secondCentralizerOtherPoint F) b) →
    a ≠ b → Commute a b →
    let B := zpowers (planeSecondPoint F) ⊔
      zpowers (((a * b : secondStabilizer F) : secondCentralizer F) : G)
    (∀ x ∈ B, ¬ IsConj z x) →
    ∃ g ∈ normalizerSpan F, B.map (MulAut.conj g).toMonoidHom = sourceSecondFour F

omit [Finite G] in
private theorem centralizer_le_of_transport {B : Subgroup G} {g : G}
    (hg : g ∈ normalizerSpan F)
    (he : B.map (MulAut.conj g).toMonoidHom = sourceSecondFour F)
    (hc : secondFourCentralizer F ≤ normalizerSpan F) :
    centralizer (B : Set G) ≤ normalizerSpan F := by
  intro x hx
  have hm : g * x * g⁻¹ ∈ secondFourCentralizer F := by
    apply mem_centralizer_iff.mpr
    intro y hy
    rw [← he] at hy
    obtain ⟨b,hb,rfl⟩ := hy
    have hh := congrArg (MulAut.conj g) (mem_centralizer_iff.mp hx b hb)
    simpa only [map_mul, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using hh
  have hh := (normalizerSpan F).mul_mem
    ((normalizerSpan F).mul_mem ((normalizerSpan F).inv_mem hg) (hc hm)) hg
  simpa only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one] using hh

/-- The source's two fixed-coset arguments now discharge the full second
centralizer from the remaining local normality and marked four-group transport. No centralizer containment is assumed in this contract. -/
theorem second_centralizer_le_of_local_data (hlinear : F.LinearFusion)
    (D : SecondCentralizerLocalData F) :
    centralizer ({planeSecondPoint F} : Set G) ≤ normalizerSpan F := by
  obtain ⟨u,v,hu,hv,hsep⟩ := secondFourPlaneImage_two_classes F hlinear
  have hfour := secondFour_centralizer_le_of_quotient_classes F hlinear
    D.plane_normal u v hu hv hsep
  apply second_centralizer_le_of_commuting_products F hlinear
  intro a b ha hb hab hcomm
  let B : Subgroup G := zpowers (planeSecondPoint F) ⊔
    zpowers (((a * b : secondStabilizer F) : secondCentralizer F) : G)
  have hBL : B ≤ normalizerSpan F := sup_le
    (zpowers_le.mpr (plane_le_span F (planeSecondPoint_mem F)))
    (zpowers_le.mpr (a * b).property)
  have hBC : centralizer (B : Set G) ≤ normalizerSpan F := by
    by_cases hp : ∃ x ∈ B, IsConj z x
    · obtain ⟨x,hx,hpoint⟩ := hp
      apply le_trans (centralizer_le (Set.singleton_subset_iff.mpr hx))
      exact normalizerSpan_point_centralizer_le F hlinear ⟨x,hBL hx⟩ hpoint
    · have hn : ∀ x ∈ B, ¬ IsConj z x := by
        intro x hx hh
        exact hp ⟨x,hx,hh⟩
      obtain ⟨g,hg,he⟩ := D.four_transport a b ha hb hab hcomm hn
      exact centralizer_le_of_transport F hg he hfour
  have he : B = closure ({planeSecondPoint F,
      (((a * b : secondStabilizer F) : secondCentralizer F) : G)} : Set G) := by
    simp only [B, zpowers_eq_closure, ← Subgroup.closure_union, Set.singleton_union]
  rw [he, centralizer_closure] at hBC
  exact hBC

/-- Ambient generation with only the explicit remaining finite local
calculations as input. -/
theorem normalizer_generation_of_second_local_data (hlinear : F.LinearFusion)
    (D : SecondCentralizerLocalData F) :
    rowNormalizer F ⊔ sourceThreeSpaceNormalizer F = ⊤ :=
  normalizer_generation_of_second_centralizer F hlinear
    (second_centralizer_le_of_local_data F hlinear D)

/-- Apply the actual quotient and commuting-product argument to the literal
source geometry. The local data producer remains to be proved from the original
hypotheses before this gives the unconditional source theorem. -/
theorem nonempty_sourceComparison_of_second_local_data (hlinear : F.LinearFusion)
    (D : SecondCentralizerLocalData F) : Nonempty (SourceComparison F) :=
  nonempty_sourceComparison_of_second_centralizer F hlinear
    (second_centralizer_le_of_local_data F hlinear D)
end Theory.GroupTheory.TransvectionFive.UniquenessLinear

