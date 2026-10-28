module

public import Stellmacher.SectionEight.GeneratedEightSixNextCoreStructure
public import Theory.GroupTheory.ElementaryEightPairQuaternionRecognition

namespace Stellmacher.SectionEight

open Later SectionsFiveToSeven
open scoped commutatorElement

universe u

public theorem eight_six_quaternion_product_of_native_factors
    {G : Type u} [Group G] [Finite G] (whole : Subgroup G)
    (left right : Subgroup whole)
    (hleft : Nonempty (left ≃* QuaternionGroup 2))
    (hright : Nonempty (right ≃* QuaternionGroup 2))
    (hgenerate : left ⊔ right = ⊤)
    (hintersection : Nat.card (left ⊓ right : Subgroup whole) = 2)
    (hcommute : ∀ first ∈ left, ∀ second ∈ right, first * second = second * first) :
    IsCentralProductQ8Q8 whole := by
  refine ⟨left.map whole.subtype, right.map whole.subtype, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨equiv⟩ := hleft
    exact ⟨(left.equivMapOfInjective whole.subtype whole.subtype_injective).symm.trans equiv⟩
  · obtain ⟨equiv⟩ := hright
    exact ⟨(right.equivMapOfInjective whole.subtype whole.subtype_injective).symm.trans equiv⟩
  · rw [← Subgroup.map_sup, hgenerate, ← MonoidHom.range_eq_map, whole.range_subtype]
  · rw [← Subgroup.map_inf _ _ _ whole.subtype_injective,
      Subgroup.card_map_of_injective whole.subtype_injective, hintersection]
  · rintro first ⟨nativeFirst, hfirst, rfl⟩ second ⟨nativeSecond, hsecond, rfl⟩
    exact congrArg Subtype.val (hcommute nativeFirst hfirst nativeSecond hsecond)
  · rw [← Subgroup.map_inf _ _ _ whole.subtype_injective]
    apply Subgroup.map_mono
    intro element helement
    apply Subgroup.mem_center_iff.mpr
    intro other
    have hcentral : left ⊔ right ≤ Subgroup.centralizer ({element} : Set whole) := by
      refine sup_le ?_ ?_
      · intro point hpoint
        exact Subgroup.mem_centralizer_singleton_iff.mpr
          (hcommute point hpoint element helement.2)
      · intro point hpoint
        exact Subgroup.mem_centralizer_singleton_iff.mpr
          (hcommute element helement.1 point hpoint).symm
    rw [hgenerate] at hcentral
    exact Subgroup.mem_centralizer_singleton_iff.mp (hcentral (Subgroup.mem_top other))

public theorem eight_six_quaternion_product_of_native_elementary_eights
    {G : Type u} [Group G] [Finite G] (whole : Subgroup G)
    (first second : Subgroup whole)
    (hfirst : IsElementaryAbelian 2 first)
    (hsecond : IsElementaryAbelian 2 second)
    (hfirstCard : Nat.card first = 8) (hsecondCard : Nat.card second = 8)
    (hgenerate : first ⊔ second = ⊤) (hnormal : second.Normal)
    (hcenter : Nat.card (Subgroup.center whole) = 2) :
    IsCentralProductQ8Q8 whole := by
  let := hnormal
  obtain ⟨left, right, hleft, hright, hjoin, hinter, hcomm⟩ :=
    exists_quaternion_factors_of_elementary_eights first second hfirst hsecond
      hfirstCard hsecondCard hgenerate (by rw [second.normalizer_eq_top]; exact le_top) hcenter
  exact eight_six_quaternion_product_of_native_factors whole left right
    hleft hright hjoin hinter hcomm

public theorem eight_six_elementary_subgroup_c2_c4_card_le
    {G : Type u} [Group G] [Finite G] (small whole : Subgroup G)
    (hle : small ≤ whole) (helementary : IsElementaryAbelian 2 small)
    (hmodel : IsModel whole (C2 × C4)) : Nat.card small ≤ 4 := by
  obtain ⟨equiv⟩ := hmodel
  let embedding : small → {point : C2 × C4 // point ^ 2 = 1} := fun point =>
    ⟨equiv ⟨point, hle point.property⟩, by
      rw [← map_pow]
      have hsquare : (⟨(point : G), hle point.property⟩ : whole) ^ 2 = 1 := by
        apply Subtype.ext
        exact congrArg (fun point : small => (point : G))
          (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp helementary.exponent_dvd_p point)
      rw [hsquare, map_one]⟩
  have hinjective : Function.Injective embedding := by
    intro first second hequal
    have hnative := equiv.injective (congrArg Subtype.val hequal)
    exact Subtype.ext (congrArg (fun point : whole => (point : G)) hnative)
  have hcard : Nat.card {point : C2 × C4 // point ^ 2 = 1} = 4 := by
    rw [Nat.card_eq_fintype_card]
    decide
  exact hcard ▸ Nat.card_le_card_of_injective embedding hinjective

public theorem eight_six_next_core_normal_elementary_eight
    {G : Type u} [Group G] [Finite G] {S P1 P2 : Subgroup G}
    (hyp : SectionSevenHypotheses G S P1 P2)
    (graph : CosetGraphContext G S P1 P2) (path : CriticalPath graph)
    (previous : graph.Vertex) (D L Q : Subgroup G)
    (hD : D = QAt graph previous ⊓ QAt graph path.firstStep)
    (helementary : IsElementaryAbelianSubgroup 2 D)
    (data : EightSixEquationOneData graph path previous D L Q)
    (orders : EightSixSmallIndexOrderData graph path D Q)
    (hquot : QuotientIsModel (GAt graph path.a) (QAt graph path.a) SL2Two)
    (hnext : QuotientIsModel (GAt graph path.firstStep) (QAt graph path.firstStep) SL2Two)
    (hlarge : Nat.card (QAt graph path.firstStep) = 32) :
    D ≤ QAt graph path.firstStep ∧ Nat.card D = 8 ∧
      IsElementaryAbelian 2 (D.subgroupOf (QAt graph path.firstStep)) ∧
      (D.subgroupOf (QAt graph path.firstStep)).Normal := by
  have hle : D ≤ QAt graph path.firstStep := hD.symm ▸ inf_le_right
  have hcard := eight_six_next_core_card_eq_four_intersection hyp graph path orders hquot hnext
  have hnormalizer : QAt graph path.firstStep ≤ Subgroup.normalizer (D : Set G) :=
    ((SevenSix.local_cores_le_edge_sylow hyp graph path).2.trans
      (SevenSix.edge_sylow_data hyp graph path).1.1).trans
      ((Subgroup.normal_subgroupOf_iff_le_normalizer data.intersection_normal.1).mp
        data.intersection_normal.2)
  let : IsElementaryAbelian 2 D := helementary
  exact ⟨hle, by omega, IsElementaryAbelian.subgroupOf hle,
    Subgroup.normal_subgroupOf_of_le_normalizer hnormalizer⟩

public theorem eight_six_next_core_intersection_with_v
    {G : Type u} [Group G] [Finite G] {S P1 P2 : Subgroup G}
    (hyp : SectionSevenHypotheses G S P1 P2)
    (graph : CosetGraphContext G S P1 P2) (path : CriticalPath graph)
    (previous : graph.Vertex) (D L Q : Subgroup G)
    (helementary : IsElementaryAbelianSubgroup 2 D)
    (data : EightSixEquationOneData graph path previous D L Q)
    (orders : EightSixSmallIndexOrderData graph path D Q)
    (hcard : Nat.card (ZAt graph path.a) = 4)
    (hi : IsModel (VAt graph path.firstStep ⊓ QAt graph path.a) (C2 × C4)) :
    D ⊓ VAt graph path.firstStep = ZAt graph path.a := by
  have hDQ : D ≤ Q := by rw [data.core_generation]; exact le_sup_right
  have hDinitial : D ≤ QAt graph path.a := orders.core_eq ▸ hDQ
  have hZaD : ZAt graph path.a ≤ D := orders.center_intersection.symm.le.trans inf_le_left
  have hZaV := (lemma_seven_four hyp graph path).first_containment.1
  have hZa : ZAt graph path.a ≤ D ⊓ VAt graph path.firstStep := le_inf hZaD hZaV
  let : IsElementaryAbelian 2 D := helementary
  have helem : IsElementaryAbelian 2 (D ⊓ VAt graph path.firstStep : Subgroup G) := {
    toIsMulCommutative := ⟨⟨fun first second => Subtype.ext
      (setLike_mul_comm (s := D) first.property.1 second.property.1)⟩⟩
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
      (fun point => Subtype.ext
        (elemPow_eq_one_of_isElementaryAbelian (p := 2) (point : G) point.property.1)) }
  have hbound := eight_six_elementary_subgroup_c2_c4_card_le
    (D ⊓ VAt graph path.firstStep) (VAt graph path.firstStep ⊓ QAt graph path.a)
    (le_inf inf_le_right (inf_le_left.trans hDinitial)) helem hi
  exact (Subgroup.eq_of_le_of_card_ge hZa (by omega)).symm

public theorem eight_six_next_core_eq_intersection_sup_v
    {G : Type u} [Group G] [Finite G] {S P1 P2 : Subgroup G}
    (hyp : SectionSevenHypotheses G S P1 P2)
    (graph : CosetGraphContext G S P1 P2) (path : CriticalPath graph)
    (previous : graph.Vertex) (D L Q : Subgroup G)
    (hD : D = QAt graph previous ⊓ QAt graph path.firstStep)
    (helementary : IsElementaryAbelianSubgroup 2 D)
    (data : EightSixEquationOneData graph path previous D L Q)
    (orders : EightSixSmallIndexOrderData graph path D Q)
    (hquot : QuotientIsModel (GAt graph path.a) (QAt graph path.a) SL2Two)
    (hnext : QuotientIsModel (GAt graph path.firstStep) (QAt graph path.firstStep) SL2Two)
    (hlength : path.length = 2) (hcard : Nat.card (ZAt graph path.a) = 4)
    (hv : IsCentralProductModel (VAt graph path.firstStep) C4 Q8)
    (hi : IsModel (VAt graph path.firstStep ⊓ QAt graph path.a) (C2 × C4))
    (hlarge : Nat.card (QAt graph path.firstStep) = 32) :
    QAt graph path.firstStep = D ⊔ VAt graph path.firstStep := by
  obtain ⟨hDle, hDcard, _, hDnormal⟩ := eight_six_next_core_normal_elementary_eight
    hyp graph path previous D L Q hD helementary data orders hquot hnext hlarge
  have hVle : VAt graph path.firstStep ≤ QAt graph path.firstStep :=
    SevenSix.neighbor_join_le_core_of_length_gt_one graph path (by omega) path.firstStep
  have hinter := eight_six_next_core_intersection_with_v hyp graph path previous D L Q
    helementary data orders hcard hi
  have hnormalize : VAt graph path.firstStep ≤ Subgroup.normalizer (D : Set G) :=
    hVle.trans ((Subgroup.normal_subgroupOf_iff_le_normalizer hDle).mp hDnormal)
  have hcount := Subgroup.card_mul_eq_card_inf_mul_card_sup_of_normalizes
    D (VAt graph path.firstStep) hnormalize
  rw [hDcard, eight_six_c4_quaternion_card hv, hinter, hcard] at hcount
  exact (Subgroup.eq_of_le_of_card_ge (sup_le hDle hVle) (by omega)).symm

public theorem eight_six_derived_le_of_elementary_supplement
    {G : Type u} [Group G] (whole elementary part line : Subgroup G)
    (hgenerate : whole = elementary ⊔ part)
    (helementary : IsElementaryAbelian 2 elementary)
    (hnormal : whole ≤ Subgroup.normalizer (elementary : Set G))
    (hline : whole ≤ Subgroup.normalizer (line : Set G))
    (hcommutator : ⁅part, whole⁆ ≤ line) : ⁅whole, whole⁆ ≤ line := by
  let := helementary
  have helementaryLe : elementary ≤ whole := hgenerate ▸ le_sup_left
  have hpartLe : part ≤ whole := hgenerate ▸ le_sup_right
  have hdecompose : ∀ point ∈ whole,
      ∃ first ∈ part, ∃ second ∈ elementary, first * second = point := by
    intro point hpoint
    rw [hgenerate, sup_comm] at hpoint
    change point ∈ (↑(part ⊔ elementary) : Set G) at hpoint
    rwa [Subgroup.coe_mul_of_left_le_normalizer_right part elementary
      (hpartLe.trans hnormal)] at hpoint
  apply Subgroup.commutator_le.mpr
  intro first hfirst second hsecond
  obtain ⟨firstPart, hfirstPart, firstElementary, hfirstElementary, rfl⟩ :=
    hdecompose first hfirst
  have hinner : ⁅firstElementary, second⁆ ∈ line := by
    obtain ⟨secondPart, hsecondPart, secondElementary, hsecondElementary, rfl⟩ :=
      hdecompose second hsecond
    have hab := commutatorElement_eq_one_iff_mul_comm.mpr
      (setLike_mul_comm (s := elementary) hfirstElementary hsecondElementary)
    rw [commutatorElement_mul_right_eq_mul_conj, hab, mul_one, mul_inv_cancel_right,
      ← commutatorElement_inv]
    exact line.inv_mem (Subgroup.commutator_le.mp hcommutator secondPart hsecondPart
      firstElementary (helementaryLe hfirstElementary))
  rw [commutatorElement_mul_left_eq_conj_mul]
  exact line.mul_mem
    (Subgroup.le_normalizer_iff.mp hline firstPart (hpartLe hfirstPart) _ hinner)
    (Subgroup.commutator_le.mp hcommutator firstPart hfirstPart second hsecond)

public theorem eight_six_next_core_derived_eq_line
    {G : Type u} [Group G] [Finite G] {S P1 P2 : Subgroup G}
    (ctx : SectionEightLocalContext G S P1 P2)
    (hcenter : ZAt ctx.Γ ctx.criticalPath.firstStep ≤
      CenterAmbient (GAt ctx.Γ ctx.criticalPath.firstStep))
    (hlength : ctx.criticalPath.length = 2)
    (hcard : Nat.card (ZAt ctx.Γ ctx.criticalPath.a) = 4)
    (D : Subgroup G) (helementary : IsElementaryAbelianSubgroup 2 D)
    (hDle : D ≤ QAt ctx.Γ ctx.criticalPath.firstStep)
    (hDnormal : (D.subgroupOf (QAt ctx.Γ ctx.criticalPath.firstStep)).Normal)
    (hgenerate : QAt ctx.Γ ctx.criticalPath.firstStep =
      D ⊔ VAt ctx.Γ ctx.criticalPath.firstStep)
    (hcommutator : ⁅VAt ctx.Γ ctx.criticalPath.firstStep,
      QAt ctx.Γ ctx.criticalPath.firstStep⁆ = ZAt ctx.Γ ctx.criticalPath.firstStep) :
    ⁅QAt ctx.Γ ctx.criticalPath.firstStep, QAt ctx.Γ ctx.criticalPath.firstStep⁆ =
      ZAt ctx.Γ ctx.criticalPath.firstStep := by
  have hcoreLe : QAt ctx.Γ ctx.criticalPath.firstStep ≤
      GAt ctx.Γ ctx.criticalPath.firstStep := by
    change ctx.Γ.twoCoreAt ctx.criticalPath.firstStep ≤ _
    rw [ctx.Γ.twoCoreAt_def]
    exact SevenSix.twoCoreIn_le _
  have hupper := eight_six_derived_le_of_elementary_supplement
    (QAt ctx.Γ ctx.criticalPath.firstStep) D (VAt ctx.Γ ctx.criticalPath.firstStep)
    (ZAt ctx.Γ ctx.criticalPath.firstStep) hgenerate helementary
    ((Subgroup.normal_subgroupOf_iff_le_normalizer hDle).mp hDnormal)
    (hcoreLe.trans (stabilizer_le_normalizer_z
      ctx.Γ ctx.criticalPath.firstStep)) hcommutator.le
  have hVle : VAt ctx.Γ ctx.criticalPath.firstStep ≤ QAt ctx.Γ ctx.criticalPath.firstStep :=
    hgenerate ▸ le_sup_right
  have hderived := eight_six_next_v_derived_eq_line_local ctx hcenter hlength hcard hcommutator
  exact le_antisymm hupper (hderived.symm.le.trans (Subgroup.commutator_mono hVle hVle))

end Stellmacher.SectionEight
