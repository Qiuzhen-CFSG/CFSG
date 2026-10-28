module
public import Theory.GroupTheory.Recognition.TransvectionFive.UniquenessMathieu.OctadGraph.Source.Involutions
public import Theory.GroupTheory.Recognition.TransvectionFive.UniquenessLinearSourceGenerationReduction
import all Theory.GroupTheory.Recognition.TransvectionFive.UniquenessLinearSourceGenerationReduction

/-!
# Ambient Mathieu generation reduced to the second involution centralizer

The proved involution fusion in the actual normalizer span and containment
of C_G(z) give the unique fixed coset for every returning z-conjugate.
This property restricts to C_G(t). Once the second class's full ambient
centralizer is also contained in the span, every involution has a unique
fixed coset. The two distinct involution classes then force the span to be G.
The complete native octad comparison supplies the resulting isomorphism.

The internal import reuses only the general fixed-coset, conjugacy, and
dihedral lemmas from the linear branch; no linear fusion assertion is used.
This proves the 7.3/7.5 reduction in Aschbacher, *Sporadic Groups* (1994),
41.1, pp.219–220. The second-centralizer containment in 41.2, pp.220–221,
remains explicit and must still be proved under the original hypotheses.
-/

public noncomputable section
open Subgroup Theory.GroupTheory.GraphUniquenessSystem.Cosets
namespace Theory.GroupTheory.TransvectionFive.UniquenessMathieu.OctadSource
open UniquenessLinear SourceNormalizer Sporadic.Mathieu
variable {G : Type*} [Group G] [Finite G] {z : G} (F : MarkedCentralizer z) (D : LocalData F)
include D

/-- The class of the marked point has no fusion outside the generated
subgroup when both endpoints lie in that subgroup. -/
theorem normalizerSpan_point_fusion
    (a : normalizerSpan F) (ha : IsConj z (a : G)) :
    IsConj (overgroupPoint (normalizerSpan F) (point_centralizer_le_normalizerSpan F)) a := by
  apply normalizerSpan_involution_fusion F D _ a
    (normalizerSpanMarking F).point_orderOf
  · obtain ⟨g, hg⟩ := isConj_iff.mp ha
    have ho : orderOf (a : G) = 2 := by
      rw [← hg]
      exact ((MulAut.conj g).orderOf_eq z).trans F.point_orderOf
    exact (Subgroup.orderOf_coe a).symm.trans ho
  · simpa only [overgroupPoint_val] using ha

/-- Every returning conjugate of the distinguished point has its full
ambient centralizer inside the actual normalizer-generated subgroup. -/
theorem normalizerSpan_point_centralizer_le
    (a : normalizerSpan F) (ha : IsConj z (a : G)) :
    centralizer ({(a : G)} : Set G) ≤ normalizerSpan F :=
  centralizer_le_of_subgroup_conj _ (normalizerSpan_point_fusion F D a ha)
    (by simpa only [overgroupPoint_val] using point_centralizer_le_normalizerSpan F)

/-- Source 7.3 applied to the first involution class in 41.1: the literal
identity coset in G/L is its unique fixed point. -/
theorem normalizerSpan_point_unique_fixed
    (a : normalizerSpan F) (ha : IsConj z (a : G))
    (v : G ⧸ normalizerSpan F) (hv : (a : G) • v = v) :
    v = vertex (normalizerSpan F) 1 := by
  apply unique_coset_of_fusion_centralizer _ a
    (normalizerSpan_point_centralizer_le F D a ha) ?_ v hv
  intro b hab
  exact (normalizerSpan_point_fusion F D a ha).symm.trans
    (normalizerSpan_point_fusion F D b (ha.trans hab))

/-- The same unique fixed coset survives restriction to the literal full
centralizer of an arbitrary element. For the second marked involution this
is precisely the action of M=C_G(t) on M/(L∩M) in source 41.1. -/
theorem normalizerSpan_point_unique_fixed_in_centralizer
    (t : G) (a : centralizer ({t} : Set G)) (haL : (a : G) ∈ normalizerSpan F)
    (ha : IsConj z (a : G))
    (v : centralizer ({t} : Set G) ⧸ (normalizerSpan F).subgroupOf (centralizer ({t} : Set G)))
    (hv : a • v = v) :
    v = vertex ((normalizerSpan F).subgroupOf (centralizer ({t} : Set G))) 1 := by
  apply unique_coset_restrict (normalizerSpan F) (centralizer ({t} : Set G)) a ?_ v hv
  intro w hw
  exact normalizerSpan_point_unique_fixed F D ⟨a, haL⟩ ha w hw

/-- Every involution has a unique fixed coset once the second class's full
ambient centralizer is contained. The first-class centralizer and both fusion
conditions have already been proved from the original marking and counts. -/
theorem normalizerSpan_all_involution_unique_fixed
    (hsecond : centralizer ({planeSecondPoint F} : Set G) ≤ normalizerSpan F)
    (x : G) (hx : orderOf x = 2) :
    ∃! v : G ⧸ normalizerSpan F, x • v = v := by
  let L := normalizerSpan F
  have hsecond' : centralizer ({((planeSecondPoint (normalizerSpanMarking F) : L) : G)} : Set G) ≤ L := by
    rw [normalizerSpan_secondPoint_val]
    exact hsecond
  have hcentral (a : L) (ha : orderOf a = 2) :
      centralizer ({(a : G)} : Set G) ≤ L := by
    rcases normalizerSpan_two_involution_classes F D a ha with hp | ht
    · exact centralizer_le_of_subgroup_conj L hp (by simpa only [overgroupPoint_val] using point_centralizer_le_normalizerSpan F)
    · exact centralizer_le_of_subgroup_conj L ht hsecond'
  have hbase (a : L) : (a : G) • vertex L 1 = vertex L 1 := by
    simpa only [smul_vertex, mul_one] using (vertex_eq_base L a).mpr a.property
  have hunique (a : L) (ha : orderOf a = 2) (v : G ⧸ L) (hv : (a : G) • v = v) :
      v = vertex L 1 := by
    apply unique_coset_of_fusion_centralizer L a (hcentral a ha) ?_ v hv
    intro b hab
    have hb : orderOf b = 2 := by
      obtain ⟨g, hg⟩ := isConj_iff.mp hab
      have ho := (MulAut.conj g).orderOf_eq (a : G)
      change orderOf (g * (a : G) * g⁻¹) = orderOf (a : G) at ho
      rw [hg, Subgroup.orderOf_coe, Subgroup.orderOf_coe, ha] at ho
      exact ho
    exact normalizerSpan_involution_fusion F D a b ha hb hab
  obtain ⟨a, ha⟩ := involution_conjugate_into_normalizerSpan F x hx
  obtain ⟨g, hg⟩ := isConj_iff.mp ha
  have hao : orderOf a = 2 := by
    have hh := (MulAut.conj g).orderOf_eq x
    change orderOf (g * x * g⁻¹) = orderOf x at hh
    rwa [hg, Subgroup.orderOf_coe, hx] at hh
  refine ⟨g⁻¹ • vertex L 1, ?_, ?_⟩
  · apply (MulAction.injective g)
    have hh := hbase a
    rw [← hg, mul_smul, mul_smul] at hh
    simpa only [smul_inv_smul] using hh
  · intro v hv
    have hav : (a : G) • (g • v) = g • v := by
      rw [← hg, mul_smul, mul_smul, inv_smul_smul, hv]
    exact (eq_inv_smul_iff).mpr (hunique a hao _ hav)

/-- The source generation argument now needs just the second involution's
full ambient centralizer. Two distinct involution classes rule out a proper
subgroup in which every involution has a unique fixed coset. -/
theorem normalizerSpan_eq_top_of_second_centralizer
    (hsecond : centralizer ({planeSecondPoint F} : Set G) ≤ normalizerSpan F) :
    normalizerSpan F = ⊤ := by
  apply top_of_two_classes_unique_fixed (normalizerSpan F)
    (overgroupPoint (normalizerSpan F) (point_centralizer_le_normalizerSpan F))
    (planeSecondPoint (normalizerSpanMarking F))
    (normalizerSpanMarking F).point_orderOf (planeSecondPoint_order _)
  · intro h
    apply secondPoint_not_fused F D
    simpa only [overgroupPoint_val, normalizerSpan_secondPoint_val] using h
  · exact normalizerSpan_all_involution_unique_fixed F D hsecond

/-- The original two full normalizers generate G once the second centralizer is contained. -/
theorem normalizer_generation_of_second_centralizer
    (hsecond : centralizer ({planeSecondPoint F} : Set G) ≤ normalizerSpan F) :
    threeSpaceNormalizer F ⊔ rowNormalizer F = ⊤ := by
  rw [← normalizerSpan_eq_pair F D]
  exact normalizerSpan_eq_top_of_second_centralizer F D hsecond

/-- Ambient Mathieu recognition, with only the explicit source 41.2 containment outstanding. -/
theorem equiv_of_second_centralizer
    (hsecond : centralizer ({planeSecondPoint F} : Set G) ≤ normalizerSpan F) :
    Nonempty (G ≃* M24) :=
  equiv_of_generation F D (normalizer_generation_of_second_centralizer F D hsecond)

omit D in
/-- Original-fusion assembly using precisely the producer's oriented marking.
Only the still-unproved source 41.2 centralizer containment is retained. -/
theorem oriented_equiv_of_second_centralizer (hfusion : F.MathieuFusion)
    (hsecond : let E := SourceData.ofFusion F hfusion
      centralizer ({planeSecondPoint E.oriented.marking} : Set G) ≤
        normalizerSpan E.oriented.marking) : Nonempty (G ≃* M24) :=
  let E := SourceData.ofFusion F hfusion
  equiv_of_second_centralizer E.oriented.marking E.localData hsecond

end Theory.GroupTheory.TransvectionFive.UniquenessMathieu.OctadSource
