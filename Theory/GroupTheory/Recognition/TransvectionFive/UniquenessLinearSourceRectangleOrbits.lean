module
public import Theory.GroupTheory.Recognition.TransvectionFive.UniquenessLinearSourcePlaneImage

/-!
# The second involution orbit in each source rectangle

The original 21-point fusion set is the rank-one locus. The natural GL₃(2)
factor transports ordered independent row pairs, so all 42 remaining
nonzero rectangle vectors form a single orbit of the full normalizer.
Thus each original rectangle has exactly two nonidentity orbits, and the
second is an actual ambient conjugacy class intersection.

This completes the rectangle orbit assertion in Aschbacher, *Sporadic
Groups* (1994), 40.3, pp.217–218, and the local input to 40.6. It does not
yet claim that all involutions of G are fused into these rectangles or that
the two second-orbit representatives are fused to one another.
-/

public noncomputable section
open Subgroup BinaryLinear.TransvectionFiveLocal
namespace Theory.GroupTheory.TransvectionFive.UniquenessLinear
open PlaneCensus
variable {G : Type*} [Group G] [Finite G] {z : G} (F : MarkedCentralizer z)

omit [Finite G] in
private theorem element_ne_one_iff (x : Code) : PlaneTensor.element F x ≠ 1 ↔ x ≠ 0 := by
  rw [← PlaneTensor.element_zero F]
  exact not_congr (PlaneTensor.element_injective F).eq_iff

/-- The complement of the point-fusion orbit is one literal plane-normalizer orbit. -/
theorem linear_plane_nonpoint_transitive (h : F.LinearFusion)
    {a b : G} (ha : a ∈ F.plane) (hb : b ∈ F.plane)
    (ha1 : a ≠ 1) (hb1 : b ≠ 1) (haz : ¬ IsConj z a) (hbz : ¬ IsConj z b) :
    ∃ n ∈ sourcePlaneNormalizer F, n * a * n⁻¹ = b := by
  obtain ⟨x, hx⟩ := (PlaneTensor.sourceEquiv F).surjective ⟨a, ha⟩
  obtain ⟨y, hy⟩ := (PlaneTensor.sourceEquiv F).surjective ⟨b, hb⟩
  have hxe : PlaneTensor.element F x = a := congrArg Subtype.val hx
  have hye : PlaneTensor.element F y = b := congrArg Subtype.val hy
  have hx0 : x ≠ 0 := (element_ne_one_iff F x).mp (hxe.symm ▸ ha1)
  have hy0 : y ≠ 0 := (element_ne_one_iff F y).mp (hye.symm ▸ hb1)
  have hpx : pure x = false := Bool.eq_false_iff.mpr (fun hh =>
    haz (hxe ▸ (PlaneTensor.fusion_iff_pure F h x).mpr hh))
  have hpy : pure y = false := Bool.eq_false_iff.mpr (fun hh =>
    hbz (hye ▸ (PlaneTensor.fusion_iff_pure F h y).mpr hh))
  obtain ⟨g, hg⟩ := rankOneGroup_transitive_nonpure x y hx0 hy0 hpx hpy
  obtain ⟨q, hq⟩ := (PlaneTensor.quotientRankOneEquiv F h).surjective g
  obtain ⟨n, hn⟩ := QuotientGroup.mk'_surjective
    (F.plane.subgroupOf (sourcePlaneNormalizer F)) q
  refine ⟨n, n.property, ?_⟩
  rw [← hxe, ← hye, ← PlaneTensor.quotientRankOneEquiv_action F h n]
  change PlaneTensor.element F ((PlaneTensor.quotientRankOneEquiv F h
    ((QuotientGroup.mk' _) n)).val x) = _
  rw [hn, hq, hg]

/-- The original three-space normalizer is likewise transitive on its
nonpoint involutions, using the same ambient conjugacy convention. -/
theorem linear_threeSpace_nonpoint_transitive (h : F.LinearFusion)
    {a b : G} (ha : a ∈ F.threeSpace) (hb : b ∈ F.threeSpace)
    (ha1 : a ≠ 1) (hb1 : b ≠ 1) (haz : ¬ IsConj z a) (hbz : ¬ IsConj z b) :
    ∃ n ∈ sourceThreeSpaceNormalizer F, n * a * n⁻¹ = b := by
  have hm := linear_plane_nonpoint_transitive (oppositeMarking F)
    (oppositeMarking_linearFusion F h) (a := a) (b := b)
  rw [oppositeMarking_plane F] at hm
  obtain ⟨n, hn, he⟩ := hm ha hb ha1 hb1 haz hbz
  change n ∈ normalizer ((oppositeMarking F).plane : Set G) at hn
  rw [oppositeMarking_plane F] at hn
  exact ⟨n, hn, he⟩

/-- A literal rank-two involution of the original plane group. -/
def planeSecondPoint : G := PlaneTensor.element F 34

omit [Finite G] in
theorem planeSecondPoint_mem : planeSecondPoint F ∈ F.plane := PlaneTensor.element_mem F 34

omit [Finite G] in
theorem planeSecondPoint_order : orderOf (planeSecondPoint F) = 2 := by
  apply orderOf_eq_prime
  · change PlaneTensor.element F 34 ^ 2 = 1
    rw [pow_two, ← PlaneTensor.element_xor]
    exact PlaneTensor.element_zero F
  · exact (element_ne_one_iff F 34).mpr (by decide)

/-- This rank-two involution is not fused to the distinguished transvection. -/
theorem planeSecondPoint_not_conjugate (h : F.LinearFusion) : ¬ IsConj z (planeSecondPoint F) := by
  change ¬ IsConj z (PlaneTensor.element F 34)
  rw [PlaneTensor.fusion_iff_pure F h]
  decide

/-- The second normalizer orbit is exactly the intersection of its ambient
conjugacy class with the original plane, without additional fusion assumptions. -/
theorem linear_plane_second_class (h : F.LinearFusion) (a : G) :
    a ∈ F.plane ∧ a ≠ 1 ∧ ¬ IsConj z a ↔
      a ∈ F.plane ∧ IsConj (planeSecondPoint F) a := by
  have ht : planeSecondPoint F ≠ 1 := by
    intro he
    have ho := planeSecondPoint_order F
    simp [he] at ho
  constructor
  · rintro ⟨ha, ha1, haz⟩
    obtain ⟨n, _, hn⟩ := linear_plane_nonpoint_transitive F h (planeSecondPoint_mem F) ha
      ht ha1 (planeSecondPoint_not_conjugate F h) haz
    exact ⟨ha, isConj_iff.mpr ⟨n, hn⟩⟩
  · rintro ⟨ha, hta⟩
    refine ⟨ha, fun he => ht ?_, fun hza => planeSecondPoint_not_conjugate F h (hza.trans hta.symm)⟩
    rw [he, isConj_one_left] at hta
    exact hta

/-- Every nonidentity plane element lies in one of these two distinct
ambient involution classes, as asserted in the local part of 40.3. -/
theorem linear_plane_two_classes (h : F.LinearFusion) {a : G} (ha : a ∈ F.plane) (ha1 : a ≠ 1) :
    IsConj z a ∨ IsConj (planeSecondPoint F) a := by
  by_cases hz : IsConj z a
  · exact Or.inl hz
  · exact Or.inr ((linear_plane_second_class F h a).mp ⟨ha, ha1, hz⟩).2

/-- The second plane orbit has exactly 42 elements, in the original ambient group. -/
theorem source_plane_nonpoint_card (h : F.LinearFusion) :
    {a : G | a ∈ F.plane ∧ a ≠ 1 ∧ ¬ IsConj z a}.ncard = 42 := by
  classical
  let s : Finset Code := Finset.univ.filter (fun x => x ≠ 0 ∧ pure x = false)
  have hcard : s.card = 42 := by decide
  have he : PlaneTensor.element F '' (s : Set Code) =
      {a : G | a ∈ F.plane ∧ a ≠ 1 ∧ ¬ IsConj z a} := by
    ext a
    constructor
    · rintro ⟨x, hx, rfl⟩
      have hx' : x ≠ 0 ∧ pure x = false := by simpa only [s, Finset.mem_coe,
        Finset.mem_filter, Finset.mem_univ, true_and] using hx
      refine ⟨PlaneTensor.element_mem F x, (element_ne_one_iff F x).mpr hx'.1, ?_⟩
      rw [PlaneTensor.fusion_iff_pure F h, hx'.2]
      decide
    · rintro ⟨ha, ha1, haz⟩
      obtain ⟨x, hx⟩ := (PlaneTensor.sourceEquiv F).surjective ⟨a, ha⟩
      have hxe : PlaneTensor.element F x = a := congrArg Subtype.val hx
      refine ⟨x, ?_, hxe⟩
      simp only [s, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨(element_ne_one_iff F x).mp (hxe.symm ▸ ha1), Bool.eq_false_iff.mpr ?_⟩
      exact fun hh => haz (hxe ▸ (PlaneTensor.fusion_iff_pure F h x).mpr hh)
  rw [← he, Set.ncard_image_of_injective _ (PlaneTensor.element_injective F),
    Set.ncard_coe_finset, hcard]

/-- The same count in the original second rectangle. -/
theorem source_threeSpace_nonpoint_card (h : F.LinearFusion) :
    {a : G | a ∈ F.threeSpace ∧ a ≠ 1 ∧ ¬ IsConj z a}.ncard = 42 := by
  have hh := source_plane_nonpoint_card (oppositeMarking F) (oppositeMarking_linearFusion F h)
  rw [oppositeMarking_plane F] at hh
  exact hh

/-- The induction subgroup already has both complete rectangle orbit counts,
without requiring its simplicity or a previously assumed classification. -/
theorem normalizerSpan_rectangle_nonpoint_counts (h : F.LinearFusion) :
    {a : normalizerSpan F | a ∈ (normalizerSpanMarking F).plane ∧ a ≠ 1 ∧
      ¬ IsConj (overgroupPoint (normalizerSpan F) (point_centralizer_le_normalizerSpan F)) a}.ncard = 42 ∧
    {a : normalizerSpan F | a ∈ (normalizerSpanMarking F).threeSpace ∧ a ≠ 1 ∧
      ¬ IsConj (overgroupPoint (normalizerSpan F) (point_centralizer_le_normalizerSpan F)) a}.ncard = 42 :=
  ⟨source_plane_nonpoint_card (normalizerSpanMarking F) (normalizerSpan_linearFusion F h),
    source_threeSpace_nonpoint_card (normalizerSpanMarking F) (normalizerSpan_linearFusion F h)⟩
end Theory.GroupTheory.TransvectionFive.UniquenessLinear
