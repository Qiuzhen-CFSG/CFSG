module

public import Stellmacher.SectionEight.GeneratedEightSixSmallIndexInitialCoreTransport
public import Stellmacher.SectionEight.GeneratedEightSixCoreGenerationTools
public import Stellmacher.SectionEight.GeneratedEightSixNeighborGeneration
public import Theory.GroupTheory.AbelianExponentFourRecognition

namespace Stellmacher.SectionEight

open Later SectionsFiveToSeven CosetGraphContext
open scoped IsMulCommutative

universe u

public theorem eight_six_predecessor_intersection_with_D_eq_initial_center
    {G : Type u} [Group G] [Finite G] {S P1 P2 : Subgroup G}
    (hyp : SectionSevenHypotheses G S P1 P2)
    (graph : CosetGraphContext G S P1 P2) (path : CriticalPath graph)
    (hcard : Nat.card (ZAt graph path.a) = 4)
    (previous : graph.Vertex)
    (hprevious : previous ∈ Later.Neighborhood graph path.a)
    (D L Q : Subgroup G)
    (data : EightSixEquationOneData graph path previous D L Q)
    (hcommutator : ⁅D, L⁆ = ZAt graph path.a)
    (helementary : IsElementaryAbelianSubgroup 2 D)
    (hindex : QuotientCardEq (VAt graph previous ⊓ QAt graph path.a)
      ((VAt graph previous ⊓ QAt graph path.a) ⊓ D) 2)
    (next : EightSixSmallIndexNextData graph path) :
    (VAt graph previous ⊓ QAt graph path.a) ⊓ D = ZAt graph path.a := by
  have hcenterD := (eight_six_initial_center_le_core_center_intersection
    hyp graph path previous D L Q data hcommutator helementary).trans inf_le_left
  have hcenterCore : ZAt graph path.a ≤ QAt graph path.a :=
    hcenterD.trans ((eight_six_equation_one_core_containments
      graph path previous D L Q data helementary).1.trans
      (eight_six_equation_one_core_containments
        graph path previous D L Q data helementary).2.2)
  have hcenterV : ZAt graph path.a ≤ VAt graph previous := by
    have hback : path.a ∈ neighborhood graph previous :=
      (SevenSix.mem_neighborhood_iff_adjacent graph).mpr
        (graph.adjacent_symm ((SevenSix.mem_neighborhood_iff_adjacent graph).mp hprevious))
    rw [VAt, v, graph.vAt_def]
    exact le_sSup ⟨path.a, hback, rfl⟩
  have hsmall := (eight_six_initial_intersection_cards
    hyp graph path previous hprevious D hindex next).2.2
  exact (Subgroup.eq_of_le_of_card_ge (le_inf (le_inf hcenterV hcenterCore) hcenterD)
    (by omega)).symm

public theorem eight_six_initial_core_model_of_structure
    {G : Type u} [Group G] [Finite G] {S P1 P2 : Subgroup G}
    (graph : CosetGraphContext G S P1 P2) (path : CriticalPath graph)
    (hcommutative : IsMulCommutative (twoCoreIn (EAt graph path.a)))
    (hcard : Nat.card (twoCoreIn (EAt graph path.a)) = 16)
    (hexponent : ∀ element : twoCoreIn (EAt graph path.a), element ^ 4 = 1)
    (hinvolutions : Nat.card {element : twoCoreIn (EAt graph path.a) //
      element ^ 2 = 1} = 4) :
    IsModel (twoCoreIn (EAt graph path.a)) (C4 × C4) := by
  let _ := hcommutative
  exact nonempty_mulEquiv_c4_square_of_card_involutions hcard hexponent hinvolutions

public theorem eight_six_native_normal_sixteen_inputs
    {G : Type u} [Group G] [Finite G]
    (container whole seed : Subgroup G)
    (hnormal : NormalIn whole container)
    (hseed : seed ≤ whole) (hmodel : IsModel seed (C2 × C4))
    (hcard : Nat.card whole = 16)
    (hcenter : 4 ≤ Nat.card (CenterAmbient whole)) :
    (whole.subgroupOf container).Normal ∧
      Nat.card (whole.subgroupOf container) = 16 ∧
      4 ≤ Nat.card (Subgroup.center (whole.subgroupOf container)) ∧
      ∃ element : whole.subgroupOf container, orderOf element = 4 := by
  let equiv := Subgroup.subgroupOfEquivOfLe hnormal.1
  have hcenterCard : Nat.card (CenterAmbient whole) =
      Nat.card (Subgroup.center whole) := by
    exact Subgroup.card_map_of_injective whole.subtype_injective
  have hcenterNative := Nat.card_congr (Subgroup.centerCongr equiv).toEquiv
  refine ⟨hnormal.2, (Nat.card_congr equiv.toEquiv).trans hcard,
    by omega, ?_⟩
  obtain ⟨model⟩ := hmodel
  let seedElement : seed := model.symm (1, Multiplicative.ofAdd (1 : ZMod 4))
  have hfour : seedElement ^ 4 = 1 := by
    apply model.injective
    simp only [map_pow, map_one, seedElement, MulEquiv.apply_symm_apply]
    decide
  have htwo : seedElement ^ 2 ≠ 1 := by
    intro hequal
    have himage := congrArg model hequal
    simp only [map_pow, map_one, seedElement, MulEquiv.apply_symm_apply] at himage
    exact (by decide : ((1, Multiplicative.ofAdd (1 : ZMod 4)) : C2 × C4) ^ 2 ≠ 1) himage
  let wholeElement := Subgroup.inclusion hseed seedElement
  refine ⟨equiv.symm wholeElement, ?_⟩
  rw [← orderOf_injective equiv.toMonoidHom equiv.injective]
  change orderOf (equiv (equiv.symm wholeElement)) = 4
  rw [MulEquiv.apply_symm_apply]
  change orderOf (Subgroup.inclusion hseed seedElement) = 4
  rw [orderOf_injective _ (Subgroup.inclusion_injective hseed)]
  exact orderOf_eq_four_of_fourth_power hfour htwo

public theorem eight_six_initial_pair_geometry_local
    {G : Type u} [Group G] [Finite G] {S P1 P2 : Subgroup G}
    (ctx : SectionEightLocalContext G S P1 P2)
    (hquot : QuotientIsModel (GAt ctx.Γ ctx.criticalPath.a)
      (QAt ctx.Γ ctx.criticalPath.a) SL2Two)
    (hlength : ctx.criticalPath.length = 2)
    (hcard : Nat.card (ZAt ctx.Γ ctx.criticalPath.a) = 4)
    (previous : ctx.Γ.Vertex)
    (hprev : previous ∈ Later.Neighborhood ctx.Γ ctx.criticalPath.a ∧
      previous ≠ ctx.criticalPath.firstStep)
    (D L Q : Subgroup G)
    (hD : D = QAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.firstStep)
    (data : EightSixEquationOneData ctx.Γ ctx.criticalPath previous D L Q)
    (hcommutator : ⁅D, L⁆ = ZAt ctx.Γ ctx.criticalPath.a)
    (helementary : IsElementaryAbelianSubgroup 2 D)
    (hindex : QuotientCardEq (VAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.a)
      ((VAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.a) ⊓ D) 2)
    (next : EightSixSmallIndexNextData ctx.Γ ctx.criticalPath) :
    let left := VAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.a
    let right := VAt ctx.Γ ctx.criticalPath.firstStep ⊓ QAt ctx.Γ ctx.criticalPath.a
    NormalIn (left ⊔ right) (GAt ctx.Γ ctx.criticalPath.a) ∧
      left ⊓ right = ZAt ctx.Γ ctx.criticalPath.a ∧
      ⁅left, right⁆ ≤ ZAt ctx.Γ ctx.criticalPath.a ∧
      ZAt ctx.Γ ctx.criticalPath.a ≤ CenterAmbient (left ⊔ right) ∧
      Nat.card (left ⊔ right : Subgroup G) = 16 := by
  let graph := ctx.Γ
  let path := ctx.criticalPath
  let left := VAt graph previous ⊓ QAt graph path.a
  let right := VAt graph path.firstStep ⊓ QAt graph path.a
  let whole := left ⊔ right
  have hlong : 1 < path.length := by dsimp [path]; omega
  have hfirst : path.firstStep ∈ neighborhood graph path.a :=
    (SevenSix.mem_neighborhood_iff_adjacent graph).mpr path.firstStep_adj
  have hpreviousAction := eight_six_generation_neighbor_action
    ctx.sectionSeven graph path hlong previous hprev.1
  have hfirstAction := eight_six_generation_neighbor_action
    ctx.sectionSeven graph path hlong path.firstStep hfirst
  have hwholeCore : whole ≤ QAt graph path.a := sup_le inf_le_right inf_le_right
  have hwholeQ : whole ≤ Q := by
    rw [data.core_generation]
    exact le_sup_left
  have hcoreInitial : QAt graph path.a ≤ GAt graph path.a := by
    rw [QAt, q, graph.twoCoreAt_def]
    exact SevenSix.twoCoreIn_le _
  have hwholeNormal : GAt graph path.a ≤ Subgroup.normalizer (whole : Set G) := by
    have hgen := eight_six_neighbor_generation_local ctx hquot hlength previous hprev
    rw [← hgen]
    refine sup_le (sup_le ?_ ?_) ?_
    · exact (le_inf hpreviousAction.1 hfirstAction.1).trans
        (Subgroup.normalizer_inf_normalizer_le_normalizer_sup _ _)
    · apply Subgroup.le_normalizer_iff_commutator_le_left.mpr
      exact (Subgroup.commutator_mono hwholeCore le_rfl).trans
        (hfirstAction.2.trans le_sup_right)
    · apply Subgroup.le_normalizer_iff_commutator_le_left.mpr
      exact (Subgroup.commutator_mono hwholeCore le_rfl).trans
        (hpreviousAction.2.trans le_sup_left)
  have hleftD := eight_six_predecessor_intersection_with_D_eq_initial_center
    ctx.sectionSeven graph path hcard previous hprev.1 D L Q data hcommutator
    helementary hindex next
  have hcenterLeft : ZAt graph path.a ≤ left := hleftD ▸ inf_le_left
  have hcenterRight : ZAt graph path.a ≤ right :=
    le_inf (lemma_seven_four ctx.sectionSeven graph path).first_containment.1
      (hcenterLeft.trans inf_le_right)
  have hinterD : left ⊓ right ≤ D := by
    rw [hD]
    exact le_inf
      ((inf_le_left.trans inf_le_left).trans
        (SevenSix.neighbor_join_le_core_of_length_gt_one graph path hlong previous))
      ((inf_le_right.trans inf_le_left).trans
        (SevenSix.neighbor_join_le_core_of_length_gt_one graph path hlong path.firstStep))
  have hinter : left ⊓ right = ZAt graph path.a := by
    apply le_antisymm
    · exact (le_inf inf_le_left hinterD).trans (le_of_eq hleftD)
    · exact le_inf hcenterLeft hcenterRight
  have hcomm : ⁅left, right⁆ ≤ ZAt graph path.a := by
    rw [← hinter]
    exact le_inf
      (Subgroup.le_normalizer_iff_commutator_le_left.mp
        (inf_le_right.trans hpreviousAction.1))
      (Subgroup.le_normalizer_iff_commutator_le_right.mp
        (inf_le_right.trans hfirstAction.1))
  have hcenterWhole : ZAt graph path.a ≤ CenterAmbient whole := by
    have hcenterQ := (eight_six_initial_center_le_core_center_intersection
      ctx.sectionSeven graph path previous D L Q data hcommutator helementary).trans
      inf_le_right
    rw [eight_six_centerAmbient_eq_inf_centralizer] at hcenterQ ⊢
    exact le_inf (hcenterLeft.trans le_sup_left)
      ((hcenterQ.trans inf_le_right).trans (Subgroup.centralizer_le hwholeQ))
  have hcards := eight_six_initial_intersection_cards
    ctx.sectionSeven graph path previous hprev.1 D hindex next
  have hproduct := Subgroup.card_mul_eq_card_inf_mul_card_sup_of_normalizes
    left right (inf_le_right.trans hpreviousAction.1)
  rw [hinter, hcard, hcards.1, hcards.2.1] at hproduct
  exact ⟨⟨hwholeCore.trans hcoreInitial,
    (Subgroup.normal_subgroupOf_iff_le_normalizer (hwholeCore.trans hcoreInitial)).mpr
      hwholeNormal⟩, hinter, hcomm, hcenterWhole, by nlinarith⟩

end Stellmacher.SectionEight
