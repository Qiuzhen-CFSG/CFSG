module
public import Theory.GroupTheory.Recognition.TransvectionFive.UniquenessLinearSourcePlaneCoordinates
public import Theory.GroupTheory.Recognition.TransvectionFive.UniquenessLinearSourceFusion
public import Theory.GroupTheory.Recognition.TransvectionFive.UniquenessLinearSourceIntersections
/-!
# The literal 21-element fusion sets are the rank-one rectangle loci

Conjugation by the five marked elementary matrices preserves the actual
plane fusion set. Source 39.6(3) makes its full normalizer transitive, so
the number of fused b with ab fused is independent of the fused element a.
Transport to six-bit coordinates and apply the checked orbit census: a
21-element invariant set with this pair-count property is exactly the
nonzero rank-one locus. The opposite marking gives the other rectangle.

In particular the row contains a distinct conjugate of z. Its relative
normality and order 16 place that conjugate in the literal two-core of
C_G(z). The normalizer-generated subgroup inherits both the 21/21 counts
and this nonweak closure, without any simplicity assumption on it.

This supplies the source fusion geometry used in Aschbacher, *Sporadic
Groups* (1994), 40.3, pp.217–218, and the inheritance step of 41.1, p.220.
The final source generation and local comparison remain separate proofs.
-/

public noncomputable section
open Subgroup BinaryLinear.TransvectionFiveLocal
namespace Theory.GroupTheory.TransvectionFive.UniquenessLinear
namespace PlaneTensor
open PlaneCensus (Code)
variable {G : Type*} [Group G] {z : G} (F : MarkedCentralizer z)

private def fusionCodes : Finset Code := by
  classical
  exact Finset.univ.filter (fun x => IsConj z (element F x))
private theorem mem_fusionCodes (x : Code) :
    x ∈ fusionCodes F ↔ IsConj z (element F x) := by
  classical
  simp [fusionCodes]

private theorem conjugate_fusion {a b : G} (hab : IsConj a b) : IsConj z a ↔ IsConj z b :=
  ⟨fun h => h.trans hab, fun h => h.trans hab.symm⟩

/-- Conjugation by the literal plane normalizer, in marked coordinates. -/
def normalizerAction (n : normalizer (F.plane : Set G)) : Equiv.Perm Code :=
  ((sourceEquiv F).trans (F.plane.normalizerMonoidHom n).toEquiv).trans (sourceEquiv F).symm

/-- The coordinate permutation retains the original ambient conjugation. -/
theorem normalizerAction_element (n : normalizer (F.plane : Set G)) (x : Code) :
    element F (normalizerAction F n x) = (n : G) * element F x * (n : G)⁻¹ := by
  change ((sourceEquiv F) ((sourceEquiv F).symm
    (F.plane.normalizerMonoidHom n (sourceEquiv F x))) : G) = _
  rw [Equiv.apply_symm_apply]
  exact normalizerMonoidHom_apply_apply_coe F.plane n _

/-- The normalizer permutation preserves the elementary group law. -/
theorem normalizerAction_xor (n : normalizer (F.plane : Set G)) (x y : Code) :
    normalizerAction F n (x ^^^ y) = normalizerAction F n x ^^^ normalizerAction F n y := by
  apply element_injective F
  rw [normalizerAction_element, element_xor, element_xor,
    normalizerAction_element, normalizerAction_element]
  group

private theorem normalizerAction_mem (n : normalizer (F.plane : Set G)) (x : Code) :
    normalizerAction F n x ∈ fusionCodes F ↔ x ∈ fusionCodes F := by
  rw [mem_fusionCodes, mem_fusionCodes]
  apply (conjugate_fusion (z := z) (show IsConj (element F x)
    (element F (normalizerAction F n x)) from ?_)).symm
  exact isConj_iff.mpr ⟨(n : G), (normalizerAction_element F n x).symm⟩

private theorem fusionCodes_card (hlinear : F.LinearFusion) : (fusionCodes F).card = 21 := by
  classical
  have he : element F '' (fusionCodes F : Set Code) = F.fusion F.plane := by
    ext a
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨element_mem F x, (mem_fusionCodes F x).mp hx⟩
    · rintro ⟨ha, hza⟩
      obtain ⟨x, hx⟩ := (sourceEquiv F).surjective ⟨a, ha⟩
      have hxe : element F x = a := congrArg Subtype.val hx
      refine ⟨x, (mem_fusionCodes F x).mpr (hxe.symm ▸ hza), hxe⟩
  have hc := congrArg Set.ncard he
  rw [Set.ncard_image_of_injective _ (element_injective F), Set.ncard_coe_finset] at hc
  exact hc.trans hlinear.1

private theorem fusionCodes_pairCount [Finite G] (a : Code) (ha : a ∈ fusionCodes F) :
    PlaneCensus.pairCount (fusionCodes F) a = PlaneCensus.pairCount (fusionCodes F) 4 := by
  classical
  obtain ⟨n, hn, hna⟩ := source_plane_fusion F (point_mem_plane F) (element_mem F a)
    ((mem_fusionCodes F a).mp ha)
  let f := normalizerAction F ⟨n, hn⟩
  have hf : f 4 = a := by
    apply element_injective F
    rw [normalizerAction_element, element_point]
    exact hna
  symm
  unfold PlaneCensus.pairCount
  apply Finset.card_bijective f f.bijective
  intro b
  simp only [Finset.mem_filter]
  rw [← hf, ← normalizerAction_xor F ⟨n, hn⟩,
    normalizerAction_mem, normalizerAction_mem]

/-- In the 21-element branch the actual fusion set, under its marked matrix
coordinates, is precisely the nonzero rank-one locus. -/
theorem fusion_iff_pure [Finite G] (hlinear : F.LinearFusion) (x : Code) :
    IsConj z (element F x) ↔ PlaneCensus.pure x = true := by
  classical
  rw [← mem_fusionCodes]
  apply PlaneCensus.eq_pure_of_twenty_one (fusionCodes F) ?_ ?_ (fusionCodes_card F hlinear) ?_
    (fusionCodes_pairCount F) x
  · intro h
    have he := (mem_fusionCodes F 0).mp h
    rw [element_zero, isConj_one_left] at he
    have ho := F.point_orderOf
    simp [he] at ho
  · rw [mem_fusionCodes, element_point]
  · intro k a
    rw [mem_fusionCodes, mem_fusionCodes]
    obtain ⟨n, _, hn⟩ := exists_shear_conjugator F k a
    exact (conjugate_fusion (z := z) (isConj_iff.mpr ⟨n, hn⟩)).symm

/-- The same assertion written directly in the marked two-by-three matrix
coordinates, with no family label or assumed ambient isomorphism. -/
theorem fusion_iff_rank_one [Finite G] (hlinear : F.LinearFusion) (x : Code) :
    IsConj z (element F x) ↔ decode x ≠ 0 ∧
      (decode x 0 = 0 ∨ decode x 1 = 0 ∨ decode x 0 = decode x 1) :=
  (fusion_iff_pure F hlinear x).trans (pure_iff_rank_one x)

/-- The entire literal plane fusion set is parametrized by its rank-one matrices. -/
theorem fusion_plane_image [Finite G] (hlinear : F.LinearFusion) :
    element F '' {x : Code | PlaneCensus.pure x = true} = F.fusion F.plane := by
  ext a
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨element_mem F x, (fusion_iff_pure F hlinear x).mpr hx⟩
  · rintro ⟨ha, hza⟩
    obtain ⟨x, hx⟩ := (sourceEquiv F).surjective ⟨a, ha⟩
    have he : element F x = a := congrArg Subtype.val hx
    exact ⟨x, (fusion_iff_pure F hlinear x).mp (he.symm ▸ hza), he⟩

/-- Opposite marked coordinates give the full original three-space fusion set. -/
theorem fusion_threeSpace_image [Finite G] (hlinear : F.LinearFusion) :
    element (oppositeMarking F) '' {x : Code | PlaneCensus.pure x = true} =
      F.fusion F.threeSpace := by
  simpa only [MarkedCentralizer.fusion, oppositeMarking_plane] using
    fusion_plane_image (oppositeMarking F) (oppositeMarking_linearFusion F hlinear)

end PlaneTensor

variable {G : Type*} [Group G] [Finite G] {z : G} (F : MarkedCentralizer z)

/-- The 21/21 hypothesis itself supplies nonweak closure in the original
point centralizer's literal two-core. This proof does not assume simplicity. -/
theorem linearFusion_pointCoreFusion (hlinear : F.LinearFusion) : PointCoreFusion z := by
  have hrow : F.row ≤ (Subgroup.centralizer ({z} : Set G)).pCoreIn 2 :=
    le_pCoreIn_of_normalizes
      (IsPGroup.of_card (p := 2) (n := 4) (by rw [row_card]; decide))
      (F.pullback_le _) (point_centralizer_le_row_normalizer F)
  have hf : IsConj z (PlaneTensor.element F 1) :=
    (PlaneTensor.fusion_iff_pure F hlinear 1).mpr (by decide)
  obtain ⟨g, hg⟩ := isConj_iff.mp hf
  refine ⟨g, ?_, ?_⟩
  · rw [hg]
    exact hrow (PlaneTensor.element_one_mem_row F)
  · rw [hg]
    exact PlaneTensor.element_one_ne_point F

/-- The actual generated subgroup in 41.1 inherits the nonweak-closure
hypothesis as well as its full marking and both fusion counts. No simplicity
of this subgroup is assumed. -/
theorem normalizerSpan_pointCoreFusion (hlinear : F.LinearFusion) :
    PointCoreFusion (overgroupPoint (normalizerSpan F) (point_centralizer_le_normalizerSpan F)) :=
  linearFusion_pointCoreFusion (normalizerSpanMarking F) (normalizerSpan_linearFusion F hlinear)

end Theory.GroupTheory.TransvectionFive.UniquenessLinear
