module

public import Stellmacher.SectionEight.GeneratedEightSixBaseSetup
public import Stellmacher.SectionEight.GeneratedEightSixSmallIndexSetup

namespace Stellmacher.SectionEight

open Later SectionsFiveToSeven CosetGraphContext

universe u

public theorem eight_six_centerAmbient_eq_inf_centralizer
    {G : Type u} [Group G] (Q : Subgroup G) :
    CenterAmbient Q = Q ⊓ Subgroup.centralizer (Q : Set G) := by
  apply le_antisymm
  · exact le_inf (Subgroup.map_subtype_le _)
      (SevenSix.centerAmbient_le_centralizer Q)
  · intro element helement
    refine Subgroup.mem_map.mpr ⟨⟨element, helement.1⟩, ?_, rfl⟩
    apply Subgroup.mem_center_iff.mpr
    intro other
    apply Subtype.ext
    exact Subgroup.mem_centralizer_iff.mp helement.2 other other.property

public theorem eight_six_equation_one_core_containments
    {G : Type u} [Group G] [Finite G]
    {S P1 P2 : Subgroup G}
    (graph : CosetGraphContext G S P1 P2) (path : CriticalPath graph)
    (previous : graph.Vertex) (D L Q : Subgroup G)
    (data : EightSixEquationOneData graph path previous D L Q)
    (helementary : IsElementaryAbelianSubgroup 2 D) :
    D ≤ Q ∧ (VAt graph previous ⊓ QAt graph path.a) ≤ Q ∧
      Q ≤ QAt graph path.a := by
  have hDcore : D ≤ QAt graph path.a := by
    let _ : IsElementaryAbelian 2 D := helementary
    have hDp : IsPGroup 2 D := IsElementaryAbelian.isPGroup 2 D
    have hDnative : IsPGroup 2 (D.subgroupOf (GAt graph path.a)) :=
      hDp.of_equiv (Subgroup.subgroupOfEquivOfLe data.intersection_normal.1).symm
    have hle : D.subgroupOf (GAt graph path.a) ≤ pCore 2 (GAt graph path.a) :=
      le_sSup ⟨data.intersection_normal.2, hDnative⟩
    change D ≤ graph.twoCoreAt path.a
    rw [graph.twoCoreAt_def]
    calc
      D = (D.subgroupOf (GAt graph path.a)).map (GAt graph path.a).subtype :=
        (Subgroup.map_subgroupOf_eq_of_le data.intersection_normal.1).symm
      _ ≤ _ := Subgroup.map_mono hle
  rw [data.core_generation]
  exact ⟨le_sup_right, le_sup_left.trans le_sup_left,
    sup_le (sup_le inf_le_right inf_le_right) hDcore⟩

public theorem eight_six_initial_center_le_core_center_intersection
    {G : Type u} [Group G] [Finite G]
    {S P1 P2 : Subgroup G}
    (hyp : SectionSevenHypotheses G S P1 P2)
    (graph : CosetGraphContext G S P1 P2) (path : CriticalPath graph)
    (previous : graph.Vertex) (D L Q : Subgroup G)
    (data : EightSixEquationOneData graph path previous D L Q)
    (hcommutator : ⁅D, L⁆ = ZAt graph path.a)
    (helementary : IsElementaryAbelianSubgroup 2 D) :
    ZAt graph path.a ≤ D ⊓ CenterAmbient Q := by
  have hcores := eight_six_equation_one_core_containments
    graph path previous D L Q data helementary
  have hZD : ZAt graph path.a ≤ D := by
    rw [← hcommutator]
    exact Subgroup.le_normalizer_iff_commutator_le_left.mp
      (data.closure_le.trans
        ((Subgroup.normal_subgroupOf_iff_le_normalizer data.intersection_normal.1).mp
          data.intersection_normal.2))
  have hZcentral : ZAt graph path.a ≤ Subgroup.centralizer (QAt graph path.a : Set G) :=
    ((lemma_seven_three hyp graph).center_core path.a path.firstStep
      ((SevenSix.mem_neighborhood_iff_adjacent graph).mpr path.firstStep_adj)).trans
        ((SevenSix.omegaOneCenter_le_centerAmbient _).trans
          (SevenSix.centerAmbient_le_centralizer _))
  rw [eight_six_centerAmbient_eq_inf_centralizer]
  exact le_inf hZD (le_inf (hZD.trans hcores.1)
    (hZcentral.trans (Subgroup.centralizer_le hcores.2.2)))

public theorem eight_six_core_center_intersection_of_predecessor_centralizer
    {G : Type u} [Group G] [Finite G]
    {S P1 P2 : Subgroup G}
    (hyp : SectionSevenHypotheses G S P1 P2)
    (graph : CosetGraphContext G S P1 P2) (path : CriticalPath graph)
    (previous : graph.Vertex) (D L Q : Subgroup G)
    (data : EightSixEquationOneData graph path previous D L Q)
    (hcommutator : ⁅D, L⁆ = ZAt graph path.a)
    (helementary : IsElementaryAbelianSubgroup 2 D)
    (hcentralizer : D ⊓ Subgroup.centralizer
      (VAt graph previous ⊓ QAt graph path.a : Set G) = ZAt graph path.a) :
    D ⊓ CenterAmbient Q = ZAt graph path.a := by
  apply le_antisymm
  · rw [← hcentralizer]
    exact inf_le_inf_left D ((SevenSix.centerAmbient_le_centralizer Q).trans
      (Subgroup.centralizer_le (eight_six_equation_one_core_containments
        graph path previous D L Q data helementary).2.1))
  · exact eight_six_initial_center_le_core_center_intersection
      hyp graph path previous D L Q data hcommutator helementary

public theorem eight_six_small_index_orders_of_predecessor_centralizer
    {G : Type u} [Group G] [Finite G]
    {S P1 P2 : Subgroup G}
    (hyp : SectionSevenHypotheses G S P1 P2)
    (graph : CosetGraphContext G S P1 P2) (path : CriticalPath graph)
    (previous : graph.Vertex) (D L Q : Subgroup G)
    (data : EightSixEquationOneData graph path previous D L Q)
    (hcommutator : ⁅D, L⁆ = ZAt graph path.a)
    (helementary : IsElementaryAbelianSubgroup 2 D)
    (hcentralizer : D ⊓ Subgroup.centralizer
      (VAt graph previous ⊓ QAt graph path.a : Set G) = ZAt graph path.a)
    (hquotient : QuotientCardEq Q D 4)
    (hindex : QuotientCardEq D (ZAt graph path.a) 1 ∨
      QuotientCardEq D (ZAt graph path.a) 2)
    (hcore : Q = QAt graph path.a) :
    EightSixSmallIndexOrderData graph path D Q := by
  exact {
    quotient_card := hquotient
    center_intersection := eight_six_core_center_intersection_of_predecessor_centralizer
      hyp graph path previous D L Q data hcommutator helementary hcentralizer
    center_index := hindex
    core_eq := hcore }

end Stellmacher.SectionEight
