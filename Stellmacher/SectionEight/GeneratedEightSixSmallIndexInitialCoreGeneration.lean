module

public import Stellmacher.SectionEight.GeneratedEightSixSmallIndexInitialCoreBounds
public import Stellmacher.SectionThree.PrimitiveDihedralExtraction
public import Stellmacher.TwoResidualSylowSupplement
public import Theory.GroupTheory.CenterFreeOddImageCore
public import Theory.GroupTheory.CentralS3InvolutionComplement
public import Theory.GroupTheory.NormalCenterQuotient

/-!
# SmallIndexInitialCoreGeneration in the small-index branch of (8.6)

The two neighboring intersections generate the two-core of the initial residual in the
small-index branch. Their span is a normal abelian group of order sixteen; the initial
quotient is SL2(2), and the initial stabilizer has trivial center. Coprime central
action forces the span into the residual, while the small quotient excludes any larger
residual core.

The graph-local form takes `SectionEightLocalContext`; the original generated-context
theorem remains a wrapper with its statement and name unchanged.

Source: Stellmacher (8.6), Journal of Algebra 190 (1997), printed p.42, paragraph ending in (6).
-/

namespace Stellmacher.SectionEight

open Later SectionsFiveToSeven CosetGraphContext

universe u

private theorem initial_generation_odd_residual_of_small_central_kernel
    {G : Type u} [Group G] [Finite G]
    (kernel : Subgroup G) [kernel.Normal]
    (hsmall : Nat.card kernel ≤ 2)
    (hcard : Nat.card G = 6 * Nat.card kernel) :
    Odd (Nat.card (twoResidualAmbient (⊤ : Subgroup G))) := by
  classical
  have hcentral : kernel ≤ Subgroup.center G := by
    have hpos : 0 < Nat.card kernel := Nat.card_pos
    have hcases : Nat.card kernel = 1 ∨ Nat.card kernel = 2 := by omega
    rcases hcases with hone | htwo
    · rw [Subgroup.card_eq_one.mp hone]
      exact bot_le
    · exact Subgroup.central_of_normal_card_two kernel htwo
  let sylow : Sylow 3 G := default
  obtain ⟨hsylowCard, hsylowNormal⟩ :=
    central_small_sylow_three_normal kernel hcentral hsmall hcard sylow
  let _ : (sylow : Subgroup G).Normal := hsylowNormal
  have hquot : IsPGroup 2 (G ⧸ (sylow : Subgroup G)) := by
    have hcount := (sylow : Subgroup G).card_mul_index
    rw [hsylowCard, hcard, Subgroup.index_eq_card] at hcount
    have hpos : 0 < Nat.card kernel := Nat.card_pos
    have hcases : Nat.card kernel = 1 ∨ Nat.card kernel = 2 := by omega
    rcases hcases with hone | htwo
    · exact IsPGroup.of_card (n := 1) (by rw [hone] at hcount; norm_num; omega)
    · exact IsPGroup.of_card (n := 2) (by rw [htwo] at hcount; norm_num; omega)
  have hle : twoResidualAmbient (⊤ : Subgroup G) ≤ (sylow : Subgroup G) := by
    rw [SectionThree.twoResidualAmbient_top_eq_hktPResidual]
    exact BenderSuzuki.External.hktPResidual_le _ hsylowNormal hquot
  exact (show Odd (Nat.card (sylow : Subgroup G)) by rw [hsylowCard]; decide).of_dvd_nat
    (Subgroup.card_dvd_of_le hle)

private theorem initial_generation_odd_image
    {G : Type u} [Group G] [Finite G]
    (core span : Subgroup G) [core.Normal] [span.Normal]
    (hle : span ≤ core) (hspanCard : Nat.card span = 16)
    (hcoreCard : Nat.card core = 16 ∨ Nat.card core = 32)
    (hcard : Nat.card G = 6 * Nat.card core) :
    Odd (Nat.card ((twoResidualAmbient (⊤ : Subgroup G)).map
      (QuotientGroup.mk' span))) := by
  let projection := QuotientGroup.mk' span
  let kernel := core.map projection
  have hkernelNormal : kernel.Normal :=
    Subgroup.Normal.map inferInstance projection (QuotientGroup.mk'_surjective span)
  let _ : kernel.Normal := hkernelNormal
  have hkernelCount : Nat.card kernel * 16 = Nat.card core := by
    have hcount := (span.subgroupOf core).index_mul_card
    rw [Subgroup.index_eq_card, ← natCard_map_mk'_eq core span,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv, hspanCard] at hcount
    exact hcount
  have hsmall : Nat.card kernel ≤ 2 := by
    rcases hcoreCard with hsmall | hlarge <;> omega
  have hquotCard : Nat.card (G ⧸ span) = 6 * Nat.card kernel := by
    have hcount := span.index_mul_card
    rw [Subgroup.index_eq_card, hspanCard, hcard] at hcount
    omega
  rw [map_twoResidualAmbient_of_subgroup_image ⊤ projection ⊤
    (Subgroup.map_top_of_surjective projection (QuotientGroup.mk'_surjective span))]
  exact initial_generation_odd_residual_of_small_central_kernel kernel hsmall hquotCard

private theorem initial_generation_core_eq_span
    {G : Type u} [Group G] [Finite G]
    (core span : Subgroup G) [core.Normal] [span.Normal]
    (hle : span ≤ core) (hspanCard : Nat.card span = 16)
    (hcoreCard : Nat.card core = 16 ∨ Nat.card core = 32)
    (hcard : Nat.card G = 6 * Nat.card core)
    (hcenter : Subgroup.center G = ⊥)
    (hab : IsMulCommutative span) :
    twoResidualAmbient (⊤ : Subgroup G) ⊓ core = span := by
  classical
  let residual := twoResidualAmbient (⊤ : Subgroup G)
  let _ : residual.Normal := by
    dsimp only [residual]
    rw [SectionThree.twoResidualAmbient_top_eq_hktPResidual]
    exact BenderSuzuki.External.hktPResidual_normal
  have hodd := initial_generation_odd_image core span hle hspanCard hcoreCard hcard
  have hspanTwo : IsPGroup 2 span := IsPGroup.of_card (n := 4) hspanCard
  have hcoreTwo : IsPGroup 2 core := by
    rcases hcoreCard with hsmall | hlarge
    · exact IsPGroup.of_card (n := 4) hsmall
    · exact IsPGroup.of_card (n := 5) hlarge
  have hcentral : span ≤ Subgroup.centralizer (span : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp
      (Subgroup.commutator_self_eq_bot_iff.mpr hab)
  have hcomm : ⁅span, residual⁆ ≤ span ⊓ residual :=
    le_inf (Subgroup.commutator_le_left _ _) (Subgroup.commutator_le_right _ _)
  have hspanResidual : span ≤ residual :=
    (Subgroup.le_of_centerfree_odd_image_commutator_le
      (default : Sylow 2 G) residual span (span ⊓ residual)
      (twoResidualAmbient_top_sup_sylow _) hspanTwo hodd hcenter
      (inf_le_left.trans hcentral) hcomm).trans inf_le_right
  apply le_antisymm ?_ (le_inf hspanResidual hle)
  let projection := QuotientGroup.mk' span
  have hdisjoint : Disjoint (residual.map projection) (core.map projection) := by
    apply Subgroup.disjoint_of_coprime_natCard
    obtain ⟨exponent, hexponent⟩ := (hcoreTwo.map projection).exists_card_eq
    rw [hexponent]
    exact hodd.coprime_two_right.pow_right exponent
  intro element helement
  have htrivial : projection element = 1 :=
    (disjoint_iff_inf_le.mp hdisjoint)
      ⟨Subgroup.mem_map_of_mem projection helement.1,
        Subgroup.mem_map_of_mem projection helement.2⟩
  exact (QuotientGroup.eq_one_iff (N := span) element).mp htrivial

set_option linter.unusedVariables false in
public theorem eight_six_small_index_initial_core_generation_local
{G : Type u} [Group G] [Finite G]
{S P1 P2 : Subgroup G}
(ctx : Later.SectionEightLocalContext G S P1 P2)
(hcenter : ZAt ctx.Γ ctx.criticalPath.firstStep ≤
  CenterAmbient (GAt ctx.Γ ctx.criticalPath.firstStep))
(hquot : QuotientIsModel (GAt ctx.Γ ctx.criticalPath.a)
  (QAt ctx.Γ ctx.criticalPath.a) SL2Two)
(hlength : ctx.criticalPath.length = 2)
(hcard : Nat.card (ZAt ctx.Γ ctx.criticalPath.a) = 4)
(previous : ctx.Γ.Vertex)
(D L Q T : Subgroup G)
(hprev : previous ∈ Later.Neighborhood ctx.Γ ctx.criticalPath.a ∧
  previous ≠ ctx.criticalPath.firstStep)
(hdefs : D = QAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.firstStep ∧
  L = conjugateClosure (QAt ctx.Γ previous) (GAt ctx.Γ ctx.criticalPath.a) ∧
  Q = twoCoreIn L ∧ IsSylowIn 3 T (GAt ctx.Γ ctx.criticalPath.a))
(hbase : ⁅D,L⁆ = ZAt ctx.Γ ctx.criticalPath.a ∧
  QuotientIsElementaryAbelian Q D 2 ∧ IsElementaryAbelianSubgroup 2 D)
(hindex : QuotientCardEq (VAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.a)
  ((VAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.a) ⊓ D) 2)
(data : SectionEight.EightSixEquationOneData ctx.Γ ctx.criticalPath previous D L Q)
(orders : SectionEight.EightSixSmallIndexOrderData ctx.Γ ctx.criticalPath D Q)
(next : EightSixSmallIndexNextData ctx.Γ ctx.criticalPath)
(hspanModel : IsModel ((VAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.a) ⊔
  (VAt ctx.Γ ctx.criticalPath.firstStep ⊓ QAt ctx.Γ ctx.criticalPath.a)) (C4 × C4)) :
twoCoreIn (EAt ctx.Γ ctx.criticalPath.a) =
  (VAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.a) ⊔
  (VAt ctx.Γ ctx.criticalPath.firstStep ⊓ QAt ctx.Γ ctx.criticalPath.a) := by
  let graph := ctx.Γ
  let path := ctx.criticalPath
  let initial := GAt graph path.a
  let span := (VAt graph previous ⊓ QAt graph path.a) ⊔
    (VAt graph path.firstStep ⊓ QAt graph path.a)
  have geometry := eight_six_initial_pair_geometry_local ctx
    hquot hlength hcard previous hprev D L Q hdefs.1 data hbase.1 hbase.2.2 hindex next
  have hspanInitial : span ≤ initial := geometry.1.1
  have hspanQ : span ≤ Q := by
    rw [orders.core_eq]
    exact sup_le inf_le_right inf_le_right
  have hQInitial : Q ≤ initial := by
    rw [orders.core_eq]
    change graph.twoCoreAt path.a ≤ graph.vertexStabilizer path.a
    rw [graph.twoCoreAt_def]
    exact Subgroup.map_subtype_le _
  let core := Q.subgroupOf initial
  let nativeSpan := span.subgroupOf initial
  have hcoreMap : core.map initial.subtype = Q :=
    Subgroup.map_subgroupOf_eq_of_le hQInitial
  have hspanMap : nativeSpan.map initial.subtype = span :=
    Subgroup.map_subgroupOf_eq_of_le hspanInitial
  let _ : core.Normal := by
    dsimp only [core]
    rw [orders.core_eq]
    change ((graph.twoCoreAt path.a).subgroupOf initial).Normal
    rw [graph.twoCoreAt_def]
    exact SevenSix.twoCoreIn_normal initial
  let _ : nativeSpan.Normal := geometry.1.2
  have hnativeLe : nativeSpan ≤ core := by
    intro element helement
    exact hspanQ helement
  have hspanCard : Nat.card nativeSpan = 16 :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hspanInitial).toEquiv).trans
      geometry.2.2.2.2
  have hcoreCard : Nat.card core = 16 ∨ Nat.card core = 32 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQInitial).toEquiv]
    exact (eight_six_initial_order_cases graph path orders hcard).imp And.right And.right
  have hlocalCard : Nat.card initial = 6 * Nat.card core := by
    obtain ⟨projection, hsurjective, hkernel⟩ := hquot
    rw [← orders.core_eq] at hkernel
    have hcount := projection.ker.index_mul_card
    rw [Subgroup.index_ker, projection.range_eq_top_of_surjective hsurjective,
      Subgroup.card_top, hkernel] at hcount
    have hmodelCard : Nat.card SL2Two = 6 :=
      SectionOne.RankOneThreeGroupAssembly.isSL2Two_card ⟨MulEquiv.refl _⟩
    rw [hmodelCard] at hcount
    exact hcount.symm
  have hcenterTrivial : Subgroup.center initial = ⊥ := by
    apply le_bot_iff.mp
    apply (Subgroup.map_le_map_iff_of_injective initial.subtype_injective).mp
    rw [Subgroup.map_bot]
    exact le_of_eq (eight_six_initial_center_trivial_local ctx hcenter)
  have hab : IsMulCommutative nativeSpan := by
    obtain ⟨model⟩ := hspanModel
    let equivalence := (Subgroup.subgroupOfEquivOfLe hspanInitial).trans model
    apply isMulCommutative_iff.mpr
    intro first second
    apply equivalence.injective
    simp only [map_mul]
    exact mul_comm _ _
  have hgeneration := initial_generation_core_eq_span core nativeSpan hnativeLe
    hspanCard hcoreCard hlocalCard hcenterTrivial hab
  have hresidualMap : (twoResidualAmbient (⊤ : Subgroup initial)).map initial.subtype =
      EAt graph path.a := by
    have hmap := map_twoResidualAmbient_of_subgroup_image (⊤ : Subgroup initial)
      initial.subtype initial
      (by rw [← MonoidHom.range_eq_map, Subgroup.range_subtype])
    exact hmap.trans (graph.twoResidualAt_def path.a).symm
  have hambient := congrArg (Subgroup.map initial.subtype) hgeneration
  rw [Subgroup.map_inf _ _ _ initial.subtype_injective, hresidualMap,
    hcoreMap, hspanMap] at hambient
  rw [eight_six_initial_residual_core_eq graph path orders]
  exact hambient

public theorem generated_eight_six_small_index_initial_core_generation
{H : Type u} [Group H] [Finite H]
{S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
(ctx : Later.GeneratedSectionEightContext H S0 S P1 P2)
(hcenter : ZAt ctx.Γ ctx.criticalPath.firstStep ≤
  CenterAmbient (GAt ctx.Γ ctx.criticalPath.firstStep))
(hquot : QuotientIsModel (GAt ctx.Γ ctx.criticalPath.a)
  (QAt ctx.Γ ctx.criticalPath.a) SL2Two)
(hlength : ctx.criticalPath.length = 2)
(hcard : Nat.card (ZAt ctx.Γ ctx.criticalPath.a) = 4)
(previous : ctx.Γ.Vertex)
(D L Q T : Subgroup (P1 ⊔ P2 : Subgroup H))
(hprev : previous ∈ Later.Neighborhood ctx.Γ ctx.criticalPath.a ∧
  previous ≠ ctx.criticalPath.firstStep)
(hdefs : D = QAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.firstStep ∧
  L = conjugateClosure (QAt ctx.Γ previous) (GAt ctx.Γ ctx.criticalPath.a) ∧
  Q = twoCoreIn L ∧ IsSylowIn 3 T (GAt ctx.Γ ctx.criticalPath.a))
(hbase : ⁅D,L⁆ = ZAt ctx.Γ ctx.criticalPath.a ∧
  QuotientIsElementaryAbelian Q D 2 ∧ IsElementaryAbelianSubgroup 2 D)
(hindex : QuotientCardEq (VAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.a)
  ((VAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.a) ⊓ D) 2)
(data : SectionEight.EightSixEquationOneData ctx.Γ ctx.criticalPath previous D L Q)
(orders : SectionEight.EightSixSmallIndexOrderData ctx.Γ ctx.criticalPath D Q)
(next : EightSixSmallIndexNextData ctx.Γ ctx.criticalPath)
(hspanModel : IsModel ((VAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.a) ⊔
  (VAt ctx.Γ ctx.criticalPath.firstStep ⊓ QAt ctx.Γ ctx.criticalPath.a)) (C4 × C4)) :
twoCoreIn (EAt ctx.Γ ctx.criticalPath.a) =
  (VAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.a) ⊔
  (VAt ctx.Γ ctx.criticalPath.firstStep ⊓ QAt ctx.Γ ctx.criticalPath.a) := by
  exact eight_six_small_index_initial_core_generation_local ctx.toLocalContext
    hcenter hquot hlength hcard previous D L Q T hprev hdefs hbase hindex data orders next hspanModel

end Stellmacher.SectionEight
