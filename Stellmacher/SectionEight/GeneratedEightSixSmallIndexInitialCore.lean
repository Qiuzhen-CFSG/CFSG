module

public import Stellmacher.SectionEight.GeneratedEightSixSmallIndexInitialCoreGeneration
public import Theory.GroupTheory.NormalSixteenC4SquareRecognition

/-!
# SmallIndexInitialCore in the small-index branch of (8.6)

The initial residual two-core in the small-index branch is C4 × C4. Local pair geometry
gives a normal span of order sixteen, containing the initial center and a C2 × C4 seed.
The center-free normal-sixteen recognition identifies the span, and the generation
calculation identifies it with the residual core.

The graph-local form takes `SectionEightLocalContext`; the original generated-context
theorem remains a wrapper with its statement and name unchanged.

Source: Stellmacher (8.6), Journal of Algebra 190 (1997), printed p.42, paragraph ending in (6).
-/

namespace Stellmacher.SectionEight

open Later SectionsFiveToSeven

universe u

set_option linter.unusedVariables false in
public theorem eight_six_small_index_initial_core_local
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
    (next : EightSixSmallIndexNextData ctx.Γ ctx.criticalPath) :
    IsModel (twoCoreIn (EAt ctx.Γ ctx.criticalPath.a)) (C4 × C4) := by
  let whole := (VAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.a) ⊔
    (VAt ctx.Γ ctx.criticalPath.firstStep ⊓ QAt ctx.Γ ctx.criticalPath.a)
  have hgeometry := eight_six_initial_pair_geometry_local ctx
    hquot hlength hcard previous hprev D L Q hdefs.1 data hbase.1 hbase.2.2 hindex next
  have hseed := eight_six_predecessor_intersection_model ctx.sectionSeven
    ctx.Γ ctx.criticalPath previous hprev.1 next
  have hcenterBound : 4 ≤ Nat.card (CenterAmbient whole) := by
    rw [← hcard]
    exact Subgroup.card_le_of_le hgeometry.2.2.2.1
  have hinputs := eight_six_native_normal_sixteen_inputs
    (GAt ctx.Γ ctx.criticalPath.a) whole
    (VAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.a)
    hgeometry.1 le_sup_left hseed hgeometry.2.2.2.2 hcenterBound
  have hcenterInitial : Subgroup.center (GAt ctx.Γ ctx.criticalPath.a) = ⊥ := by
    apply (Subgroup.map_eq_bot_iff_of_injective _
      (GAt ctx.Γ ctx.criticalPath.a).subtype_injective).mp
    exact data.initial_center_trivial
  let _ : (whole.subgroupOf (GAt ctx.Γ ctx.criticalPath.a)).Normal := hinputs.1
  obtain ⟨nativeModel⟩ := nonempty_mulEquiv_c4_square_of_normal_order_sixteen
    (whole.subgroupOf (GAt ctx.Γ ctx.criticalPath.a)) hcenterInitial
    hinputs.2.1 hinputs.2.2.1 hinputs.2.2.2
  have hspanModel : IsModel whole (C4 × C4) :=
    ⟨(Subgroup.subgroupOfEquivOfLe hgeometry.1.1).symm.trans nativeModel⟩
  rw [eight_six_small_index_initial_core_generation_local ctx hcenter hquot
    hlength hcard previous D L Q T hprev hdefs hbase hindex data orders next hspanModel]
  exact hspanModel

public theorem generated_eight_six_small_index_initial_core
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
    (next : EightSixSmallIndexNextData ctx.Γ ctx.criticalPath) :
    IsModel (twoCoreIn (EAt ctx.Γ ctx.criticalPath.a)) (C4 × C4) := by
  exact eight_six_small_index_initial_core_local ctx.toLocalContext
    hcenter hquot hlength hcard previous D L Q T hprev hdefs hbase hindex data orders next

end Stellmacher.SectionEight
