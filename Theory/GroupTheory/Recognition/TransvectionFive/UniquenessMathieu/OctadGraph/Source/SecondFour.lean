module
public import Theory.GroupTheory.Recognition.TransvectionFive.UniquenessMathieu.OctadGraph.Source.PairCentralizer
public import Theory.GroupTheory.Recognition.TransvectionFive.UniquenessLinearSourceSecondCentralizer
import all Theory.GroupTheory.Recognition.TransvectionFive.UniquenessLinearSourceSecondCentralizer
import all Theory.GroupTheory.Recognition.TransvectionFive.UniquenessLinearSourcePlaneCoordinates
import all Theory.GroupTheory.Recognition.TransvectionFive.UniquenessLinearSourceRectangleOrbits

/-!
# The literal residual four-group and its centralizer quotient

The marked codes 34 and 52 generate precisely B(t)=C_{A₂}(I^∞): their
three nonzero elements avoid the point class, so the six-line geometry
places them on the same exceptional line as t. Every nonzero coset in
A₂/B(t) has a point-class lift, giving a unique fixed coset under the
original map C_G(B) → C_G(B)/B. Two quotient classes are separated by
point-class lifts in the 21-point rectangle.

The first 7.5 application concludes C_G(B) ≤ L once the remaining local
involutions of (L∩C_G(B))/B have point-class lifts. Placement of C_L(t)
in G₃ then gives N_G(B) ≤ L by weak closure of the actual A₂. Both local
premises remain explicit; neither ambient generation nor recognition is
assumed by these deductions. The imported linear module supplies only
shared coordinate four-groups and generic fixed-coset lemmas.

Source: Aschbacher, *Sporadic Groups* (1994), 40.4(2) and 41.2,
printed pp.218, 220–221.
-/

public noncomputable section
open Subgroup
namespace Theory.GroupTheory.TransvectionFive.UniquenessMathieu.OctadSource
open UniquenessLinear SourceNormalizer PlaneTensor PlaneCensus
variable {G : Type*} [Group G] [Finite G] {z : G} (F : MarkedCentralizer z) (D : LocalData F)

include D in
/-- The literal marked four-group contains no point-class involution. -/
theorem secondFour_no_point {x : G} (hx : x ∈ sourceSecondFour F) : ¬ IsConj z x := by
  obtain ⟨c,hc,rfl⟩ := hx
  rw [plane_fusion_iff_pure F D.orientation.1, fourCodes_nonpure c hc]
  decide

private theorem planeFour_of_nonpoint_pair (E : MarkedCentralizer z)
    (hc : (E.fusion E.plane).ncard = 45) (a b : G)
    (ha : a ∈ E.plane) (hb : b ∈ E.plane) (ha1 : a ≠ 1) (hb1 : b ≠ 1)
    (hab : a ≠ b) (hza : ¬ IsConj z a) (hzb : ¬ IsConj z b)
    (hzab : ¬ IsConj z (a * b)) :
    ∃ i : Fin 6, a ∈ planeFour E i ∧ b ∈ planeFour E i := by
  obtain ⟨c,hc'⟩ := (sourceEquiv E).surjective ⟨a,ha⟩
  obtain ⟨d,hd'⟩ := (sourceEquiv E).surjective ⟨b,hb⟩
  have hec : element E c = a := congrArg Subtype.val hc'
  have hed : element E d = b := congrArg Subtype.val hd'
  have hexc : Sextet.exceptional c = true := (Sextet.exceptional_iff c).mpr
    ⟨fun h => ha1 (hec.symm.trans (h ▸ element_zero E)),
      Bool.eq_false_iff.mpr (fun h => hza (hec ▸ (plane_fusion_iff_fused E hc c).mpr h))⟩
  have hexd : Sextet.exceptional d = true := (Sextet.exceptional_iff d).mpr
    ⟨fun h => hb1 (hed.symm.trans (h ▸ element_zero E)),
      Bool.eq_false_iff.mpr (fun h => hzb (hed ▸ (plane_fusion_iff_fused E hc d).mpr h))⟩
  have hcd : c ≠ d := fun h => hab (hec.symm.trans ((congrArg (element E) h).trans hed))
  have heprod : element E (c ^^^ d) = a * b := by rw [element_xor, hec, hed]
  have hexe : Sextet.exceptional (c ^^^ d) = true := (Sextet.exceptional_iff _).mpr
    ⟨fun h => hcd (BitVec.xor_eq_zero_iff.mp h),
      Bool.eq_false_iff.mpr (fun h => hzab (heprod ▸ (plane_fusion_iff_fused E hc _).mpr h))⟩
  obtain ⟨i,hi⟩ := Sextet.exceptional_triple c d hcd hexc hexd hexe
  exact ⟨i, (mem_planeFour E i a).mpr ⟨c, hi ▸ (by simp), hec⟩,
    (mem_planeFour E i b).mpr ⟨d, hi ▸ (by simp), hed⟩⟩

include D in
/-- The coordinate four-group is exactly the actual residual-fixed B(t)
from source 40.4(2), not merely an abstract group of order four. -/
theorem secondFour_eq_involutionFour :
    sourceSecondFour F = involutionFour F (planeSecondPoint F) := by
  let E := oppositeMarking F
  have h45 : (E.fusion E.plane).ncard = 45 := by
    simpa only [E, MarkedCentralizer.fusion, oppositeMarking_plane] using D.orientation.2
  let t := planeSecondPoint F
  let b := element F 52
  have htB : t ∈ sourceSecondFour F := sourceSecondFour_second_mem F
  have hbB : b ∈ sourceSecondFour F := (element_mem_sourceSecondFour F 52).mpr (by decide)
  have ht1 : t ≠ 1 := (element_ne_one_iff F 34).mpr (by decide)
  have hb1 : b ≠ 1 := (element_ne_one_iff F 52).mpr (by decide)
  have htb : t ≠ b := fun h => (by decide : (34 : Code) ≠ 52) (element_injective F h)
  have hinc : sourceSecondFour F ≤ E.plane := by
    rw [show E.plane = F.threeSpace from oppositeMarking_plane F]
    exact sourceSecondFour_le_threeSpace F
  obtain ⟨i,hti,hbi⟩ := planeFour_of_nonpoint_pair E h45 t b (hinc htB) (hinc hbB)
    ht1 hb1 htb (secondFour_no_point F D htB) (secondFour_no_point F D hbB)
    (secondFour_no_point F D ((sourceSecondFour F).mul_mem htB hbB))
  have he : sourceSecondFour F = planeFour E i := by
    apply eq_of_le_of_card_ge
    · rw [sourceSecondFour_eq]
      exact sup_le (zpowers_le.mpr hti) (zpowers_le.mpr hbi)
    · rw [sourceSecondFour_card, planeFour_card]
  exact he.trans (involutionFour_eq_of_mem_four F D.orientation t ht1 i hti).symm

private theorem planeFour_point_lift (E : MarkedCentralizer z)
    (hc : (E.fusion E.plane).ncard = 45) (i : Fin 6)
    {a : G} (ha : a ∈ E.plane) (haB : a ∉ planeFour E i) :
    ∃ b : planeFour E i, IsConj z (a * (b : G)) := by
  obtain ⟨c,hc'⟩ := (sourceEquiv E).surjective ⟨a,ha⟩
  have he : element E c = a := congrArg Subtype.val hc'
  have hn : c ∉ Sextet.line i := fun h => haB ((mem_planeFour E i a).mpr ⟨c,h,he⟩)
  obtain ⟨d,hd,hp⟩ := (by decide : ∀ (i : Fin 6) (c : Code), c ∉ Sextet.line i →
    ∃ d ∈ Sextet.line i, Sextet.fused (c ^^^ d) = true) i c hn
  refine ⟨⟨element E d,(mem_planeFour E i _).mpr ⟨d,hd,rfl⟩⟩,?_⟩
  rw [← he, ← element_xor]
  exact (plane_fusion_iff_fused E hc _).mpr hp

include D in
/-- Every nonidentity coset of A₂/B(t) has an actual point-class lift. -/
theorem secondFour_threeSpace_point_lift {a : G} (ha : a ∈ F.threeSpace)
    (haB : a ∉ sourceSecondFour F) :
    ∃ b : sourceSecondFour F, IsConj z (a * (b : G)) := by
  have ht1 : planeSecondPoint F ≠ 1 := (element_ne_one_iff F 34).mpr (by decide)
  obtain ⟨i,hi,_⟩ := (oriented_threeSpace_fours F D.orientation).2.2 (planeSecondPoint F)
    (secondPoint_mem_threeSpace F) ht1 (secondPoint_not_fused F D)
  have he : sourceSecondFour F = planeFour (oppositeMarking F) i :=
    (secondFour_eq_involutionFour F D).trans
      (involutionFour_eq_of_mem_four F D.orientation _ ht1 i hi)
  rw [he] at haB ⊢
  apply planeFour_point_lift (oppositeMarking F) _ i
    (by simpa only [oppositeMarking_plane] using ha) haB
  simpa only [MarkedCentralizer.fusion, oppositeMarking_plane] using D.orientation.2

omit [Finite G] in
/-- A₂ centralizes the actual B(t), so the ensuing quotient has the source's denominator. -/
theorem threeSpace_le_secondFourCentralizer : F.threeSpace ≤ secondFourCentralizer F := by
  intro a ha
  apply mem_centralizer_iff.mpr
  intro b hb
  exact mem_centralizer_iff.mp ((threeSpace_centralizer_eq F).symm ▸ ha) b
    (sourceSecondFour_le_threeSpace F hb)

/-- The literal image of A₂ in (L∩C_G(B))/B, kept inside its quotient stabilizer. -/
abbrev secondFourThreeSpaceImage : Subgroup (secondFourStabilizerImage F) :=
  ((F.threeSpace.subgroupOf (secondFourCentralizer F)).map
    (QuotientGroup.mk' (secondFourKernel F))).subgroupOf (secondFourStabilizerImage F)

include D in
private theorem point_unique_in_subgroup (K : Subgroup G) (a : K)
    (haL : (a : G) ∈ normalizerSpan F) (ha : IsConj z (a : G)) :
    ∃! q : K ⧸ (normalizerSpan F).subgroupOf K, a • q = q := by
  apply UniqueFixedCoset.unique_of_transporter (show a ∈ (normalizerSpan F).subgroupOf K from haL)
  intro g hg
  have hu : ∃! q : G ⧸ normalizerSpan F, (a : G) • q = q := by
    refine ⟨GraphUniquenessSystem.Cosets.vertex (normalizerSpan F) 1, ?_, ?_⟩
    · simpa only [GraphUniquenessSystem.Cosets.smul_vertex, mul_one] using
        (GraphUniquenessSystem.Cosets.vertex_eq_base (normalizerSpan F) (a : G)).mpr haL
    · exact normalizerSpan_point_unique_fixed F D ⟨a,haL⟩ ha
  change (g : G) ∈ normalizerSpan F
  exact UniqueFixedCoset.transporter_mem (G := G) haL hu
    (show (g : G) * (a : G) * (g : G)⁻¹ ∈ normalizerSpan F from hg)

include D in
/-- Each nonzero element of the literal A₂/B(t) image is lifted through
exactly the original centralizer quotient map by a point involution. -/
theorem secondFourThreeSpaceImage_point_lifts (x : secondFourThreeSpaceImage F) (hx : x ≠ 1) :
    ∃ y : secondFourStabilizer F,
      QuotientGroup.mk' (secondFourKernel F) y =
        ((x : secondFourStabilizerImage F) : secondFourQuotient F) ∧
      IsConj z ((y : secondFourCentralizer F) : G) := by
  obtain ⟨a,ha,he⟩ := x.property
  have haB : (a : G) ∉ sourceSecondFour F := by
    intro hm
    have hzq : QuotientGroup.mk' (secondFourKernel F) a = 1 :=
      (QuotientGroup.eq_one_iff a).mpr hm
    exact hx (Subtype.ext (Subtype.ext (he.symm.trans hzq)))
  obtain ⟨b,hb⟩ := secondFour_threeSpace_point_lift F D ha haB
  let bK : secondFourCentralizer F :=
    ⟨b, threeSpace_le_secondFourCentralizer F (sourceSecondFour_le_threeSpace F b.property)⟩
  have hspan : F.threeSpace ≤ normalizerSpan F :=
    (F.pullback_le _).trans (point_centralizer_le_normalizerSpan F)
  let y : secondFourStabilizer F := ⟨a * bK,
    (normalizerSpan F).mul_mem (hspan ha) (hspan (sourceSecondFour_le_threeSpace F b.property))⟩
  refine ⟨y,?_,hb⟩
  change QuotientGroup.mk' (secondFourKernel F) (a * bK) = _
  rw [map_mul, show QuotientGroup.mk' (secondFourKernel F) bK = 1 from
    (QuotientGroup.eq_one_iff bK).mpr b.property, mul_one]
  exact he

include D in
/-- The first source quotient now has a unique fixed coset for every
nonidentity element of its literal A₂/B(t) subgroup. -/
theorem secondFourThreeSpaceImage_unique_fixed (x : secondFourThreeSpaceImage F) (hx : x ≠ 1) :
    ∃! q : secondFourQuotient F ⧸ secondFourStabilizerImage F,
      ((x : secondFourStabilizerImage F) : secondFourQuotient F) • q = q := by
  obtain ⟨y,hy,hpoint⟩ := secondFourThreeSpaceImage_point_lifts F D x hx
  rw [← hy]
  apply UniqueFixedCoset.unique_map_of_surjective _ (QuotientGroup.mk'_surjective _)
    (show (QuotientGroup.mk' (secondFourKernel F)).ker ≤ secondFourStabilizer F from ?_) y.property
  · exact point_unique_in_subgroup F D (secondFourCentralizer F) y y.property hpoint
  · intro a ha
    have hm : (a : G) ∈ sourceSecondFour F := (QuotientGroup.eq_one_iff a).mp ha
    exact (F.pullback_le _).trans (point_centralizer_le_normalizerSpan F)
      (sourceSecondFour_le_plane F hm)

private theorem secondFourPlaneCode_ne_one (D : LocalData F) {c : Code}
    (hc : pure c = true) : secondFourPlaneCode F c ≠ 1 := by
  intro he
  have hh : QuotientGroup.mk' (secondFourKernel F) (planeInFourCentralizer F c) = 1 :=
    congrArg (fun x : secondFourPlaneImage F =>
      ((x : secondFourStabilizerImage F) : secondFourQuotient F)) he
  have hm : element F c ∈ sourceSecondFour F := (QuotientGroup.eq_one_iff (N := secondFourKernel F) (planeInFourCentralizer F c)).mp hh
  exact secondFour_no_point F D hm ((plane_fusion_iff_pure F D.orientation.1 c).mpr hc)

private theorem secondFour_point_cosets_not_conj (D : LocalData F) :
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
    apply (plane_fusion_iff_pure F D.orientation.1 _).mp
    apply ((plane_fusion_iff_pure F D.orientation.1 4).mpr (by decide)).trans
    exact isConj_iff.mpr ⟨k, hconj.trans (element_xor F 1 c).symm⟩
  have hp2 : pure ((1 ^^^ c) ^^^ 22) = true := by
    apply (plane_fusion_iff_pure F D.orientation.1 _).mp
    exact ((plane_fusion_iff_pure F D.orientation.1 18).mpr (by decide)).trans
      (isConj_iff.mpr ⟨k,hconj2⟩)
  exact (by decide : ∀ c ∈ fourCodes,
    pure (1 ^^^ c) = true → pure ((1 ^^^ c) ^^^ 22) = true → False) c hc hp hp2

/-- Two classes in the literal centralizer quotient are separated by their
point-class lifts. The first coset has three such lifts, whereas the second has
only one; the proof uses two distinct lifts and the checked four-element table. -/
theorem secondFourPlaneImage_two_classes (D : LocalData F) :
    ∃ a b : secondFourPlaneImage F, a ≠ 1 ∧ b ≠ 1 ∧
      ¬ IsConj (a : secondFourStabilizerImage F) (b : secondFourStabilizerImage F) := by
  refine ⟨secondFourPlaneCode F 4, secondFourPlaneCode F 1,
    secondFourPlaneCode_ne_one F D (by decide : PlaneCensus.pure 4 = true),
    secondFourPlaneCode_ne_one F D (by decide : PlaneCensus.pure 1 = true), ?_⟩
  intro h
  exact secondFour_point_cosets_not_conj F D
    ((secondFourStabilizerImage F).subtype.map_isConj h)


private theorem eq_top_of_involution_fixed {K : Type*} [Group K] [Finite K]
    (H : Subgroup K) (a b : H) (ha : orderOf a = 2) (hb : orderOf b = 2)
    (hne : ¬ IsConj a b)
    (hu : ∀ x : H, orderOf x = 2 → ∃! q : K ⧸ H, (x : K) • q = q) : H = ⊤ := by
  have hc {x y : K} (h : IsConj x y) : orderOf y = orderOf x := by
    obtain ⟨g,rfl⟩ := isConj_iff.mp h
    exact (MulAut.conj g).orderOf_eq x
  have separate : ¬ IsConj (a : K) (b : K) :=
    fun h => hne (UniqueFixedCoset.fusion_of_unique (hu a ha) h)
  apply UniqueFixedCoset.eq_top_of_commuting_products H a b ha hb separate
  · intro x hx
    exact hx.elim (UniqueFixedCoset.unique_of_isConj (hu a ha))
      (UniqueFixedCoset.unique_of_isConj (hu b hb))
  · intro x y hx hy hxy hcomm
    have hxo : orderOf x = 2 := (Subgroup.orderOf_coe x).symm.trans
      ((hc hx).trans ((Subgroup.orderOf_coe a).trans ha))
    have hyo : orderOf y = 2 := (Subgroup.orderOf_coe y).symm.trans (hy.elim
      (fun h => (hc h).trans ((Subgroup.orderOf_coe a).trans ha))
      (fun h => (hc h).trans ((Subgroup.orderOf_coe b).trans hb)))
    have hx2 : x ^ 2 = 1 := hxo ▸ pow_orderOf_eq_one x
    have hy2 : y ^ 2 = 1 := hyo ▸ pow_orderOf_eq_one y
    have hp : orderOf (x * y) = 2 := by
      apply orderOf_eq_prime
      · rw [hcomm.mul_pow, hx2, hy2, one_mul]
      · intro he
        have hxx : x * x = 1 := by simpa only [pow_two] using hx2
        exact hxy (mul_left_cancel (hxx.trans he.symm))
    exact UniqueFixedCoset.centralizer_le_of_unique (x * y).property (hu (x * y) hp)

include D in
/-- The first 7.5 step is discharged as soon as the remaining local quotient
involutions have point-class lifts. All lifts, kernels and stabilizers are literal. -/
theorem secondFour_centralizer_le_of_involution_lifts
    (hlift : ∀ x : secondFourStabilizerImage F, orderOf x = 2 →
      ∃ y : secondFourStabilizer F,
        QuotientGroup.mk' (secondFourKernel F) y = (x : secondFourQuotient F) ∧
        IsConj z ((y : secondFourCentralizer F) : G)) :
    secondFourCentralizer F ≤ normalizerSpan F := by
  let q := QuotientGroup.mk' (secondFourKernel F)
  have hk : q.ker ≤ secondFourStabilizer F := by
    intro a ha
    have hm : (a : G) ∈ sourceSecondFour F := (QuotientGroup.eq_one_iff a).mp ha
    exact (F.pullback_le _).trans (point_centralizer_le_normalizerSpan F)
      (sourceSecondFour_le_plane F hm)
  have hu (x : secondFourStabilizerImage F) (hx : orderOf x = 2) :
      ∃! v : secondFourQuotient F ⧸ secondFourStabilizerImage F,
        (x : secondFourQuotient F) • v = v := by
    obtain ⟨y,hy,hp⟩ := hlift x hx
    rw [← hy]
    exact UniqueFixedCoset.unique_map_of_surjective q (QuotientGroup.mk'_surjective _) hk y.property
      (point_unique_in_subgroup F D (secondFourCentralizer F) y y.property hp)
  obtain ⟨a,b,ha,hb,hne⟩ := secondFourPlaneImage_two_classes F D
  have order (x : secondFourPlaneImage F) (hx : x ≠ 1) :
      orderOf (x : secondFourStabilizerImage F) = 2 :=
    (Subgroup.orderOf_coe x).trans (orderOf_eq_prime (secondFourPlaneImage_square F x) hx)
  have htop := eq_top_of_involution_fixed (secondFourStabilizerImage F)
    a b (order a ha) (order b hb) hne hu
  apply Subgroup.subgroupOf_eq_top.mp
  apply top_unique
  intro a _
  have hm : q a ∈ secondFourStabilizerImage F := htop ▸ mem_top _
  obtain ⟨b,hb,he⟩ := hm
  have hker : b⁻¹ * a ∈ q.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, he, inv_mul_cancel]
  simpa only [mul_inv_cancel_left] using (secondFourStabilizer F).mul_mem hb (hk hker)

include D in
/-- Once the local span centralizer lies in G₃, controlling C_G(B) controls
the full ambient normalizer of B as well. Weak closure is applied to A₂,
not to an abstract four-group or to a quotient with a changed denominator. -/
theorem secondFour_normalizer_le_of_local_placement
    (hlocal : normalizerSpan F ⊓ Subgroup.centralizer ({planeSecondPoint F} : Set G) ≤
      threeSpaceNormalizer F)
    (hfour : secondFourCentralizer F ≤ normalizerSpan F) :
    normalizer (sourceSecondFour F : Set G) ≤ normalizerSpan F := by
  have hC : secondFourCentralizer F ≤ threeSpaceNormalizer F := by
    intro g hg
    apply hlocal
    exact ⟨hfour hg, mem_centralizer_singleton_iff.mpr
      (mem_centralizer_iff.mp hg _ (sourceSecondFour_second_mem F)).symm⟩
  intro g hg
  have hnC := normalizer_le_normalizer_centralizer (sourceSecondFour F) hg
  have hn : g ∈ threeSpaceNormalizer F := by
    apply mem_normalizer_iff_map_conj_eq.mpr
    apply (sourceSylow F).conjugate_eq_of_le_normalizer_of_weakly_closed F.threeSpace
      (flag_le_sourceSylow F).2.2.2
      (fun n hn => mem_normalizer_iff_map_conj_eq.mp
        (threeSpace_weakly_closed F (Or.inl D.orientation) n hn))
    rintro _ ⟨a,ha,rfl⟩
    exact hC ((mem_normalizer_iff.mp hnC a).mp (threeSpace_le_secondFourCentralizer F ha))
  have hle : threeSpaceNormalizer F ≤ normalizerSpan F := by
    rw [normalizerSpan_eq]
    exact le_sup_right
  exact hle hn

include D in
/-- Actual normalizer control from the two outstanding local calculations:
placement of C_L(t) and point lifts for involutions of (L∩C_G(B))/B. -/
theorem secondFour_normalizer_le_of_involution_lifts
    (hlocal : normalizerSpan F ⊓ Subgroup.centralizer ({planeSecondPoint F} : Set G) ≤
      threeSpaceNormalizer F)
    (hlift : ∀ x : secondFourStabilizerImage F, orderOf x = 2 →
      ∃ y : secondFourStabilizer F,
        QuotientGroup.mk' (secondFourKernel F) y = (x : secondFourQuotient F) ∧
        IsConj z ((y : secondFourCentralizer F) : G)) :
    normalizer (sourceSecondFour F : Set G) ≤ normalizerSpan F :=
  secondFour_normalizer_le_of_local_placement F D hlocal
    (secondFour_centralizer_le_of_involution_lifts F D hlift)

end Theory.GroupTheory.TransvectionFive.UniquenessMathieu.OctadSource
