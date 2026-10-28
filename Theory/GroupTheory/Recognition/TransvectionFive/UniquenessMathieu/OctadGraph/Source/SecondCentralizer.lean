module
public import Theory.GroupTheory.Recognition.TransvectionFive.UniquenessMathieu.OctadGraph.Source.SecondFour
import all Theory.GroupTheory.Recognition.TransvectionFive.UniquenessMathieu.OctadGraph.Source.SecondFour
import all Theory.GroupTheory.Recognition.TransvectionFive.UniquenessLinearSourceSecondCentralizer
import all Theory.GroupTheory.Recognition.TransvectionFive.UniquenessLinearSourceRectangleOrbits

/-!
# Ambient generation from the remaining local Mathieu calculations

Multiplication by t separates the two selected point classes represented by
codes 4 and 2 in C_G(t). Their unique fixed cosets are already proved. If
C_L(t) normalizes A₂, conjugates of both representatives lie in A₂. For
commuting representatives a,b, either ⟨t,ab⟩ contains a point involution,
whose centralizer is contained in L, or the six-line geometry identifies
⟨t,ab⟩ with the literal source B(t). The previously proved fixed-coset
argument in C_G(B)/B then supplies its centralizer containment.

This applies source 7.5 directly in C_G(t), avoiding another quotient by
⟨t⟩. It yields ambient generation and the native M₂₄ isomorphism from two
explicit remaining local calculations: C_L(t)≤N_G(A₂), and point-class
lifts for every involution of (L∩C_G(B))/B. The original-fusion consumer
retains precisely the same producer's oriented marking. These local
premises still need proofs; no unconditional source theorem is asserted.

The final alternative replaces the local centralizer placement by its
point-orbit calculation and applies the actual weak-closure transporter
lemmas from `PairCentralizer`.

Source: Aschbacher, *Sporadic Groups* (1994), 7.5 and 41.2, pp.20,220–221.
Internal imports reuse the existing coordinate and generic coset helpers;
no linear-fusion conclusion is used in the Mathieu argument.
-/

public noncomputable section
open Subgroup
namespace Theory.GroupTheory.TransvectionFive.UniquenessMathieu.OctadSource
open UniquenessLinear SourceNormalizer PlaneTensor PlaneCensus
variable {G : Type*} [Group G] [Finite G] {z : G} (F : MarkedCentralizer z) (D : LocalData F)

/-- Multiplication by the fixed second involution separates two point classes
in its full centralizer. -/
theorem secondCentralizer_two_point_classes (D : LocalData F) :
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
  have hpoint : IsConj z (element F 32) := (plane_fusion_iff_pure F D.orientation.1 _).mpr (by decide)
  have hnot : ¬ IsConj z (element F 38) := by
    rw [plane_fusion_iff_pure F D.orientation.1]
    decide
  exact hnot (hpoint.trans he.symm)

private theorem secondCode_unique (D : LocalData F) {c : Code}
    (hc : pure c = true) :
    ∃! q : secondCentralizer F ⧸ secondStabilizer F,
      (secondCode F c : secondCentralizer F) • q = q :=
  point_unique_in_subgroup F D (secondCentralizer F)
    (secondCode F c : secondCentralizer F) (secondCode F c).property
    ((plane_fusion_iff_pure F D.orientation.1 c).mpr hc)

/-- The first use of source 7.5 takes place in the literal full centralizer
of the second involution. Both selected classes and their unique fixed cosets
are proved from the original 21-point fusion set. -/
theorem second_centralizer_le_of_commuting_products (D : LocalData F)
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
    (secondCentralizer_two_point_classes F D)
  · intro x hx
    rcases hx with hx | hx
    · exact UniqueFixedCoset.unique_of_isConj (secondCode_unique F D (by decide : PlaneCensus.pure 4 = true)) hx
    · exact UniqueFixedCoset.unique_of_isConj (secondCode_unique F D (by decide : PlaneCensus.pure 2 = true)) hx
  · intro a b ha hb hab hcomm
    have ha' := UniqueFixedCoset.fusion_of_unique
      (secondCode_unique F D (by decide : PlaneCensus.pure 4 = true)) ha
    have hb' : IsConj (secondCentralizerPoint F) b ∨ IsConj (secondCentralizerOtherPoint F) b :=
      hb.imp (UniqueFixedCoset.fusion_of_unique (secondCode_unique F D (by decide : PlaneCensus.pure 4 = true)))
        (UniqueFixedCoset.fusion_of_unique (secondCode_unique F D (by decide : PlaneCensus.pure 2 = true)))
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


omit [Finite G] in
private theorem second_conjugate_point_mem_threeSpace
    (hlocal : normalizerSpan F ⊓ Subgroup.centralizer ({planeSecondPoint F} : Set G) ≤
      threeSpaceNormalizer F)
    (a : secondStabilizer F)
    (ha : IsConj (secondCentralizerPoint F) a ∨ IsConj (secondCentralizerOtherPoint F) a) :
    ((a : secondCentralizer F) : G) ∈ F.threeSpace := by
  have hz : ((secondCentralizerPoint F : secondCentralizer F) : G) ∈ F.threeSpace := by
    rw [secondCentralizerPoint_val]
    exact point_mem_threeSpace F
  have hz2 : ((secondCentralizerOtherPoint F : secondCentralizer F) : G) ∈ F.threeSpace :=
    (plane_element_mem_threeSpace_iff F 2).mpr (by decide)
  rcases ha with ha | ha <;> obtain ⟨g,hg⟩ := isConj_iff.mp ha
  all_goals
    have hn := hlocal ⟨g.property,g.val.property⟩
    have he := congrArg (fun x : secondStabilizer F => ((x : secondCentralizer F) : G)) hg
    rw [← he]
  · exact (mem_normalizer_iff.mp hn _).mp hz
  · exact (mem_normalizer_iff.mp hn _).mp hz2

private theorem card_join_zpowers_four {K : Type*} [Group K] [Finite K]
    (t v : K) (ht1 : t ≠ 1) (hv1 : v ≠ 1) (htv : t ≠ v) (ht2 : t * t = 1) :
    4 ≤ Nat.card (↥(zpowers t ⊔ zpowers v)) := by
  have ht : t ∈ (zpowers t ⊔ zpowers v : Subgroup K) := le_sup_left (α := Subgroup K) (mem_zpowers t)
  have hv : v ∈ (zpowers t ⊔ zpowers v : Subgroup K) := le_sup_right (α := Subgroup K) (mem_zpowers v)
  let f : Fin 4 → (zpowers t ⊔ zpowers v : Subgroup K) :=
    ![1, ⟨t,ht⟩, ⟨v,hv⟩, ⟨t*v,mul_mem_sup (mem_zpowers t) (mem_zpowers v)⟩]
  have htv1 : t*v ≠ 1 := fun h => htv (mul_left_cancel (ht2.trans h.symm))
  have hprod_t : t*v ≠ t := fun h => hv1 (mul_left_cancel (h.trans (mul_one t).symm))
  have hprod_v : t*v ≠ v := fun h => ht1 (mul_right_cancel (h.trans (one_mul v).symm))
  have hinj : Function.Injective f := by
    intro i j hij
    have hh := congrArg Subtype.val hij
    fin_cases i <;> fin_cases j <;>
      simp only [f] at hh ⊢
    all_goals first | rfl | exact False.elim (ht1 hh) | exact False.elim (ht1 hh.symm) |
      exact False.elim (hv1 hh) | exact False.elim (hv1 hh.symm) |
      exact False.elim (htv hh) | exact False.elim (htv hh.symm) |
      exact False.elim (htv1 hh) | exact False.elim (htv1 hh.symm) |
      exact False.elim (hprod_t hh) | exact False.elim (hprod_t hh.symm) |
      exact False.elim (hprod_v hh) | exact False.elim (hprod_v hh.symm)
  simpa only [Nat.card_fin] using Nat.card_le_card_of_injective f hinj

include D in
/-- For the two selected point classes, a point-free commuting product
spans exactly the source B(t). This uses the actual A₂ exceptional lines. -/
theorem second_pointfree_four_eq_of_local_placement
    (hlocal : normalizerSpan F ⊓ Subgroup.centralizer ({planeSecondPoint F} : Set G) ≤
      threeSpaceNormalizer F)
    (a b : secondStabilizer F) (ha : IsConj (secondCentralizerPoint F) a)
    (hb : IsConj (secondCentralizerPoint F) b ∨ IsConj (secondCentralizerOtherPoint F) b)
    (hab : a ≠ b)
    (hfree : ∀ x ∈ zpowers (planeSecondPoint F) ⊔
      zpowers (((a * b : secondStabilizer F) : secondCentralizer F) : G), ¬ IsConj z x) :
    zpowers (planeSecondPoint F) ⊔
      zpowers (((a * b : secondStabilizer F) : secondCentralizer F) : G) = sourceSecondFour F := by
  let t := planeSecondPoint F
  let v : G := (((a * b : secondStabilizer F) : secondCentralizer F) : G)
  have hpoint (c : secondStabilizer F)
      (hc : IsConj (secondCentralizerPoint F) c ∨ IsConj (secondCentralizerOtherPoint F) c) :
      IsConj z ((c : secondCentralizer F) : G) := by
    rcases hc with hc | hc
    · have hh := ((secondCentralizer F).subtype.comp (secondStabilizer F).subtype).map_isConj hc
      simpa only [MonoidHom.comp_apply, Subgroup.subtype_apply, secondCentralizerPoint_val] using hh
    · have hh := ((secondCentralizer F).subtype.comp (secondStabilizer F).subtype).map_isConj hc
      exact ((plane_fusion_iff_pure F D.orientation.1 2).mpr (by decide)).trans hh
  have ha2 : a * a = 1 := by
    obtain ⟨g,rfl⟩ := isConj_iff.mp ha
    have hs : secondCentralizerPoint F ^ 2 = 1 :=
      (secondCode_order F (by decide : (4 : Code) ≠ 0)) ▸ pow_orderOf_eq_one (secondCentralizerPoint F)
    change (MulAut.conj g) (secondCentralizerPoint F) *
      (MulAut.conj g) (secondCentralizerPoint F) = 1
    rw [← map_mul]
    have hs2 : secondCentralizerPoint F * secondCentralizerPoint F = 1 := by
      simpa only [pow_two] using hs
    rw [hs2, map_one]
  have ht1 : t ≠ 1 := (element_ne_one_iff F 34).mpr (by decide)
  have hv1 : v ≠ 1 := by
    intro he
    have he' : a * b = 1 := Subtype.ext (Subtype.ext he)
    exact hab (mul_left_cancel (ha2.trans he'.symm))
  have hvt : v ≠ t := by
    intro he
    have hprod : ((b : secondCentralizer F) : G) = t * ((a : secondCentralizer F) : G) := by
      have hh := congrArg (fun x : secondStabilizer F => ((x : secondCentralizer F) : G)) ha2
      have hc := mem_centralizer_singleton_iff.mp a.val.property
      change ((a : secondCentralizer F) : G) * ((a : secondCentralizer F) : G) = 1 at hh
      change ((a : secondCentralizer F) : G) * ((b : secondCentralizer F) : G) = t at he
      calc
        _ = ((a : secondCentralizer F) : G) * t := by rw [← he, ← mul_assoc, hh, one_mul]
        _ = _ := hc
    obtain ⟨g,hg⟩ := isConj_iff.mp ha
    have hez := congrArg (fun x : secondStabilizer F => ((x : secondCentralizer F) : G)) hg
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, secondCentralizerPoint_val] at hez
    have hgt : (g.val : G) * t * (g.val : G)⁻¹ = t := by
      rw [mem_centralizer_singleton_iff.mp g.val.property, mul_inv_cancel_right]
    have h38 : IsConj (element F 38) ((b : secondCentralizer F) : G) := by
      have hcode : element F 38 = t * z := by
        rw [show element F 38 = element F 34 * element F 4 from element_xor F 34 4,
          element_point]
        rfl
      rw [hcode,hprod]
      refine isConj_iff.mpr ⟨g.val,?_⟩
      calc
        _ = ((g.val : G) * t * (g.val : G)⁻¹) *
          ((g.val : G) * z * (g.val : G)⁻¹) := by group
        _ = _ := by rw [hgt]; exact congrArg (t * ·) hez
    have hf := (plane_fusion_iff_pure F D.orientation.1 38).mp
      ((hpoint b hb).trans h38.symm)
    exact (by decide : PlaneCensus.pure (38 : Code) ≠ true) hf
  have htv : t ≠ v := Ne.symm hvt
  have hm : v ∈ F.threeSpace := F.threeSpace.mul_mem
    (second_conjugate_point_mem_threeSpace F hlocal a (Or.inl ha))
    (second_conjugate_point_mem_threeSpace F hlocal b hb)
  let E := oppositeMarking F
  have htE : t ∈ E.plane := by
    rw [oppositeMarking_plane]
    exact secondPoint_mem_threeSpace F
  have hvE : v ∈ E.plane := by rwa [oppositeMarking_plane]
  have h45 : (E.fusion E.plane).ncard = 45 := by
    simpa only [E, MarkedCentralizer.fusion, oppositeMarking_plane] using D.orientation.2
  obtain ⟨i,hti,hvi⟩ := planeFour_of_nonpoint_pair E h45 t v htE hvE ht1 hv1 htv
    (secondPoint_not_fused F D)
    (hfree v ((show zpowers v ≤ zpowers t ⊔ zpowers v from le_sup_right) (mem_zpowers v)))
    (hfree (t * v) (mul_mem_sup (mem_zpowers t) (mem_zpowers v)))
  have hB : sourceSecondFour F = planeFour E i :=
    (secondFour_eq_involutionFour F D).trans
      (involutionFour_eq_of_mem_four F D.orientation t ht1 i hti)
  have hle : zpowers t ⊔ zpowers v ≤ sourceSecondFour F := by
    rw [hB]
    exact sup_le (zpowers_le.mpr hti) (zpowers_le.mpr hvi)
  have ht2 : t * t = 1 := by
    have hh : t ^ 2 = 1 := (orderOf_eq_prime_iff.mp (planeSecondPoint_order F)).1
    simpa only [pow_two] using hh
  have hcard := card_join_zpowers_four t v ht1 hv1 htv ht2

  exact eq_of_le_of_card_ge hle (by rw [sourceSecondFour_card]; exact hcard)

include D in
/-- The two fixed-coset steps yield the full ambient second-centralizer bound
from two finite local calculations. No generation or isomorphism is a premise. -/
theorem second_centralizer_le_of_local_placement_and_lifts
    (hlocal : normalizerSpan F ⊓ Subgroup.centralizer ({planeSecondPoint F} : Set G) ≤
      threeSpaceNormalizer F)
    (hlift : ∀ x : secondFourStabilizerImage F, orderOf x = 2 →
      ∃ y : secondFourStabilizer F,
        QuotientGroup.mk' (secondFourKernel F) y = (x : secondFourQuotient F) ∧
        IsConj z ((y : secondFourCentralizer F) : G)) :
    Subgroup.centralizer ({planeSecondPoint F} : Set G) ≤ normalizerSpan F := by
  have hfour := secondFour_centralizer_le_of_involution_lifts F D hlift
  apply second_centralizer_le_of_commuting_products F D
  intro a b ha hb hab hcomm
  let B : Subgroup G := zpowers (planeSecondPoint F) ⊔
    zpowers (((a * b : secondStabilizer F) : secondCentralizer F) : G)
  have hBL : B ≤ normalizerSpan F := sup_le
    (zpowers_le.mpr (plane_le_span F (planeSecondPoint_mem F)))
    (zpowers_le.mpr (a * b).property)
  have hBC : Subgroup.centralizer (B : Set G) ≤ normalizerSpan F := by
    by_cases hp : ∃ x ∈ B, IsConj z x
    · obtain ⟨x,hx,hpoint⟩ := hp
      exact (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hx)).trans
        (normalizerSpan_point_centralizer_le F D ⟨x,hBL hx⟩ hpoint)
    · have he : B = sourceSecondFour F :=
        second_pointfree_four_eq_of_local_placement F D hlocal a b ha hb hab
          (fun x hx hh => hp ⟨x,hx,hh⟩)
      rw [he]
      exact hfour
  have he : B = closure ({planeSecondPoint F,
      (((a * b : secondStabilizer F) : secondCentralizer F) : G)} : Set G) := by
    simp only [B, zpowers_eq_closure, ← Subgroup.closure_union, Set.singleton_union]
  rw [he, centralizer_closure] at hBC
  exact hBC

include D in
/-- Actual recognition consumer for the remaining local placement and quotient lifts. -/
theorem equiv_of_local_placement_and_lifts
    (hlocal : normalizerSpan F ⊓ Subgroup.centralizer ({planeSecondPoint F} : Set G) ≤
      threeSpaceNormalizer F)
    (hlift : ∀ x : secondFourStabilizerImage F, orderOf x = 2 →
      ∃ y : secondFourStabilizer F,
        QuotientGroup.mk' (secondFourKernel F) y = (x : secondFourQuotient F) ∧
        IsConj z ((y : secondFourCentralizer F) : G)) : Nonempty (G ≃* Sporadic.Mathieu.M24) :=
  equiv_of_second_centralizer F D
    (second_centralizer_le_of_local_placement_and_lifts F D hlocal hlift)

include D in
/-- The original full normalizers generate G when the two local calculations hold. -/
theorem normalizer_generation_of_local_placement_and_lifts
    (hlocal : normalizerSpan F ⊓ Subgroup.centralizer ({planeSecondPoint F} : Set G) ≤
      threeSpaceNormalizer F)
    (hlift : ∀ x : secondFourStabilizerImage F, orderOf x = 2 →
      ∃ y : secondFourStabilizer F,
        QuotientGroup.mk' (secondFourKernel F) y = (x : secondFourQuotient F) ∧
        IsConj z ((y : secondFourCentralizer F) : G)) :
    threeSpaceNormalizer F ⊔ rowNormalizer F = ⊤ :=
  normalizer_generation_of_second_centralizer F D
    (second_centralizer_le_of_local_placement_and_lifts F D hlocal hlift)

/-- Apply the complete reduction to exactly the producer's oriented marking.
The two local premises remain this source theorem owner's obligations. -/
theorem oriented_equiv_of_local_placement_and_lifts (hfusion : F.MathieuFusion)
    (hlocal : let E := SourceData.ofFusion F hfusion
      normalizerSpan E.oriented.marking ⊓
        Subgroup.centralizer ({planeSecondPoint E.oriented.marking} : Set G) ≤
          threeSpaceNormalizer E.oriented.marking)
    (hlift : let E := SourceData.ofFusion F hfusion
      ∀ x : secondFourStabilizerImage E.oriented.marking, orderOf x = 2 →
        ∃ y : secondFourStabilizer E.oriented.marking,
          QuotientGroup.mk' (secondFourKernel E.oriented.marking) y =
            (x : secondFourQuotient E.oriented.marking) ∧
          IsConj z ((y : secondFourCentralizer E.oriented.marking) : G)) :
    Nonempty (G ≃* Sporadic.Mathieu.M24) :=
  let E := SourceData.ofFusion F hfusion
  equiv_of_local_placement_and_lifts E.oriented.marking E.localData hlocal hlift

include D in
/-- The proved weak-closure transporter step turns the local point-orbit
calculation into the required placement of the span centralizer. -/
theorem normalizerSpan_second_centralizer_le_of_point_orbit
    (horbit : ∀ g ∈ normalizerSpan F,
      g * planeSecondPoint F * g⁻¹ = planeSecondPoint F →
      g * z * g⁻¹ ∈ F.plane ∨ g * z * g⁻¹ ∈ F.threeSpace) :
    normalizerSpan F ⊓ Subgroup.centralizer ({planeSecondPoint F} : Set G) ≤
      threeSpaceNormalizer F := by
  rintro g ⟨hg,hgt⟩
  have ht : g * planeSecondPoint F * g⁻¹ = planeSecondPoint F := by
    rw [mem_centralizer_singleton_iff.mp hgt, mul_inv_cancel_right]
  exact point_second_transporter_rectangles F D g ht (horbit g hg ht)

include D in
/-- Source recognition from the remaining local orbit and quotient-lift
calculations, applying the actual weak-closure and four-group arguments. -/
theorem equiv_of_local_point_orbit_and_lifts
    (horbit : ∀ g ∈ normalizerSpan F,
      g * planeSecondPoint F * g⁻¹ = planeSecondPoint F →
      g * z * g⁻¹ ∈ F.plane ∨ g * z * g⁻¹ ∈ F.threeSpace)
    (hlift : ∀ x : secondFourStabilizerImage F, orderOf x = 2 →
      ∃ y : secondFourStabilizer F,
        QuotientGroup.mk' (secondFourKernel F) y = (x : secondFourQuotient F) ∧
        IsConj z ((y : secondFourCentralizer F) : G)) : Nonempty (G ≃* Sporadic.Mathieu.M24) :=
  equiv_of_local_placement_and_lifts F D
    (normalizerSpan_second_centralizer_le_of_point_orbit F D horbit) hlift

end Theory.GroupTheory.TransvectionFive.UniquenessMathieu.OctadSource
