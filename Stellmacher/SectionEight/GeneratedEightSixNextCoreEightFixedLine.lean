module

public import Stellmacher.SectionEight.GeneratedEightSixNextCoreEightReduction
public import Stellmacher.SectionEight.GeneratedEightSixIntersectionCentralizer
public import Stellmacher.SectionEight.GeneratedEightSixRigidityLastCenter
public import Stellmacher.SectionEight.GeneratedEightSixSmallIndexCenter

namespace Stellmacher.SectionEight

open Later SectionsFiveToSeven

universe u

public theorem eight_six_next_core_intersection_centralizer_from_orders
    {G : Type u} [Group G] [Finite G] {S P1 P2 : Subgroup G}
    (ctx : SectionEightLocalContext G S P1 P2)
    (hcenter : ZAt ctx.Γ ctx.criticalPath.firstStep ≤
      CenterAmbient (GAt ctx.Γ ctx.criticalPath.firstStep))
    (hlength : ctx.criticalPath.length = 2)
    (hcard : Nat.card (ZAt ctx.Γ ctx.criticalPath.a) = 4)
    (previous : ctx.Γ.Vertex) (D L Q : Subgroup G)
    (hD : D = QAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.firstStep)
    (hL : L = conjugateClosure (QAt ctx.Γ previous)
      (GAt ctx.Γ ctx.criticalPath.a))
    (hQ : Q = twoCoreIn L)
    (data : EightSixEquationOneData ctx.Γ ctx.criticalPath previous D L Q)
    (orders : EightSixSmallIndexOrderData ctx.Γ ctx.criticalPath D Q) :
    D ⊓ Subgroup.centralizer (VAt ctx.Γ ctx.criticalPath.firstStep : Set G) =
      ZAt ctx.Γ ctx.criticalPath.firstStep := by
  apply eight_six_intersection_centralizer_of_rigidity ctx.sectionSeven ctx.Γ
    ctx.criticalPath hcenter previous D L Q hD data
  intro U hU hUS
  have hcentral := eight_six_rigidity_sup_centralizes_core ctx.sectionSeven ctx.Γ
    ctx.criticalPath hcenter previous D L Q hD hL hQ data U
    (hU.trans inf_le_left) hUS
  have hUZ : U ≤ ZAt ctx.Γ ctx.criticalPath.a := by
    rw [← orders.center_intersection, eight_six_centerAmbient_eq_inf_centralizer]
    exact le_inf (hU.trans inf_le_left) (le_sup_left.trans hcentral)
  exact eight_six_rigidity_le_first_center_of_le_initial ctx hcenter hlength hcard
    previous D L Q data U hUZ (hU.trans inf_le_right)

public theorem eight_six_next_core_intersection_center_eq_line
    {G : Type u} [Group G] [Finite G] {S P1 P2 : Subgroup G}
    (ctx : SectionEightLocalContext G S P1 P2)
    (hcenter : ZAt ctx.Γ ctx.criticalPath.firstStep ≤
      CenterAmbient (GAt ctx.Γ ctx.criticalPath.firstStep))
    (hlength : ctx.criticalPath.length = 2)
    (hcard : Nat.card (ZAt ctx.Γ ctx.criticalPath.a) = 4)
    (previous : ctx.Γ.Vertex) (D L Q : Subgroup G)
    (hD : D = QAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.firstStep)
    (hL : L = conjugateClosure (QAt ctx.Γ previous)
      (GAt ctx.Γ ctx.criticalPath.a))
    (hQ : Q = twoCoreIn L)
    (data : EightSixEquationOneData ctx.Γ ctx.criticalPath previous D L Q)
    (orders : EightSixSmallIndexOrderData ctx.Γ ctx.criticalPath D Q) :
    D ⊓ CenterAmbient (QAt ctx.Γ ctx.criticalPath.firstStep) =
      ZAt ctx.Γ ctx.criticalPath.firstStep := by
  have hfull := eight_six_next_core_intersection_centralizer_from_orders ctx hcenter
    hlength hcard previous D L Q hD hL hQ data orders
  have hVle : VAt ctx.Γ ctx.criticalPath.firstStep ≤
      QAt ctx.Γ ctx.criticalPath.firstStep :=
    SevenSix.neighbor_join_le_core_of_length_gt_one ctx.Γ ctx.criticalPath
      (by omega) ctx.criticalPath.firstStep
  have hcoreLe : QAt ctx.Γ ctx.criticalPath.firstStep ≤
      GAt ctx.Γ ctx.criticalPath.firstStep := by
    change ctx.Γ.twoCoreAt ctx.criticalPath.firstStep ≤ _
    rw [ctx.Γ.twoCoreAt_def]
    exact SevenSix.twoCoreIn_le _
  apply le_antisymm
  · exact (inf_le_inf_left D ((SevenSix.centerAmbient_le_centralizer _).trans
      (Subgroup.centralizer_le hVle))).trans hfull.le
  · have hlineD := hfull.symm.le.trans inf_le_left
    rw [eight_six_centerAmbient_eq_inf_centralizer]
    exact le_inf hlineD (le_inf (hlineD.trans (hD.symm ▸ inf_le_right))
      ((hcenter.trans (SevenSix.centerAmbient_le_centralizer _)).trans
        (Subgroup.centralizer_le hcoreLe)))

public theorem eight_six_native_central_commutator_fixed_line
    {G : Type u} [Group G] [Finite G]
    (whole D line : Subgroup G) (hDle : D ≤ whole)
    (hfixed : D ⊓ CenterAmbient whole = line)
    (hderived : ⁅whole, whole⁆ = line)
    (hcard : Nat.card line = 2) :
    commutator whole ≤ D.subgroupOf whole ⊓ Subgroup.center whole ∧
      Nat.card (D.subgroupOf whole ⊓ Subgroup.center whole : Subgroup whole) = 2 := by
  have hmap : (D.subgroupOf whole ⊓ Subgroup.center whole).map whole.subtype = line := by
    rw [Subgroup.map_inf _ _ _ whole.subtype_injective,
      Subgroup.map_subgroupOf_eq_of_le hDle]
    exact hfixed
  constructor
  · apply (Subgroup.map_le_map_iff_of_injective whole.subtype_injective).mp
    rw [Subgroup.map_subtype_commutator, hderived, hmap]
  · rw [← Subgroup.card_map_of_injective whole.subtype_injective, hmap, hcard]

public theorem eight_six_next_core_native_eight_inputs
    {G : Type u} [Group G] [Finite G] {S P1 P2 : Subgroup G}
    (ctx : SectionEightLocalContext G S P1 P2)
    (hcenter : ZAt ctx.Γ ctx.criticalPath.firstStep ≤
      CenterAmbient (GAt ctx.Γ ctx.criticalPath.firstStep))
    (hquot : QuotientIsModel (GAt ctx.Γ ctx.criticalPath.a)
      (QAt ctx.Γ ctx.criticalPath.a) SL2Two)
    (hlength : ctx.criticalPath.length = 2)
    (hcard : Nat.card (ZAt ctx.Γ ctx.criticalPath.a) = 4)
    (previous : ctx.Γ.Vertex) (D L Q : Subgroup G)
    (hD : D = QAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.firstStep)
    (hL : L = conjugateClosure (QAt ctx.Γ previous)
      (GAt ctx.Γ ctx.criticalPath.a))
    (hQ : Q = twoCoreIn L)
    (helementary : IsElementaryAbelianSubgroup 2 D)
    (data : EightSixEquationOneData ctx.Γ ctx.criticalPath previous D L Q)
    (orders : EightSixSmallIndexOrderData ctx.Γ ctx.criticalPath D Q)
    (hnext : QuotientIsModel (GAt ctx.Γ ctx.criticalPath.firstStep)
      (QAt ctx.Γ ctx.criticalPath.firstStep) SL2Two)
    (hv : IsCentralProductModel (VAt ctx.Γ ctx.criticalPath.firstStep) C4 Q8)
    (hi : IsModel (VAt ctx.Γ ctx.criticalPath.firstStep ⊓ QAt ctx.Γ ctx.criticalPath.a)
      (C2 × C4))
    (hlarge : Nat.card (QAt ctx.Γ ctx.criticalPath.firstStep) = 32) :
    let whole := QAt ctx.Γ ctx.criticalPath.firstStep
    let native := D.subgroupOf whole
    native.Normal ∧ IsElementaryAbelian 2 native ∧ Nat.card native = 8 ∧
      commutator whole ≤ native ⊓ Subgroup.center whole ∧
      Nat.card (native ⊓ Subgroup.center whole : Subgroup whole) = 2 := by
  obtain ⟨hDle, hDcard, hDelem, hDnormal⟩ := eight_six_next_core_normal_elementary_eight
    ctx.sectionSeven ctx.Γ ctx.criticalPath previous D L Q hD helementary
    data orders hquot hnext hlarge
  have hgenerate := eight_six_next_core_eq_intersection_sup_v ctx.sectionSeven ctx.Γ
    ctx.criticalPath previous D L Q hD helementary data orders hquot hnext hlength
    hcard hv hi hlarge
  have hderived := eight_six_next_core_derived_eq_line ctx hcenter hlength hcard D
    helementary hDle hDnormal hgenerate data.first_commutator
  have hfixed := eight_six_next_core_intersection_center_eq_line ctx hcenter hlength
    hcard previous D L Q hD hL hQ data orders
  have hline := eight_six_first_step_fixed_line_local ctx hcenter hcard
  have hnative := eight_six_native_central_commutator_fixed_line
    (QAt ctx.Γ ctx.criticalPath.firstStep) D (ZAt ctx.Γ ctx.criticalPath.firstStep)
    hDle hfixed hderived hline.1
  exact ⟨hDnormal, hDelem,
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDle).toEquiv).trans hDcard,
    hnative⟩

end Stellmacher.SectionEight
