module

public import Stellmacher.SectionEight.GeneratedEightSixNextSmallStructure
public import Stellmacher.SectionFiveToSeven.Result7_6.CoreFacts

namespace Stellmacher.SectionEight

open Later SectionsFiveToSeven CosetGraphContext

universe u

private theorem edge_sylow_card_eq_twice_core
    {G : Type u} [Group G] [Finite G]
    (actors core edge : Subgroup G) (hle : core ≤ actors) (hedge : core ≤ edge)
    (hsylow : IsSylowIn 2 edge actors)
    (hquotient : QuotientIsModel actors core SL2Two) :
    Nat.card edge = 2 * Nat.card core := by
  obtain ⟨sylow, hsylow⟩ := hsylow
  have hnative : core.subgroupOf actors ≤ sylow := by
    apply (Subgroup.map_le_map_iff_of_injective actors.subtype_injective).mp
    rw [Subgroup.map_subgroupOf_eq_of_le hle, hsylow]
    exact hedge
  have hratio := eight_six_sylow_card_eq_twice_core actors core sylow hle hnative hquotient
  have hcard : Nat.card edge = Nat.card sylow := by
    rw [← hsylow, Subgroup.card_map_of_injective actors.subtype_injective]
  omega

public theorem eight_six_next_core_card_eq_four_intersection
    {G : Type u} [Group G] [Finite G] {S P1 P2 : Subgroup G}
    (hyp : SectionSevenHypotheses G S P1 P2)
    (graph : CosetGraphContext G S P1 P2) (path : CriticalPath graph)
    {D Q : Subgroup G} (orders : EightSixSmallIndexOrderData graph path D Q)
    (hquot : QuotientIsModel (GAt graph path.a) (QAt graph path.a) SL2Two)
    (hnext : QuotientIsModel (GAt graph path.firstStep)
      (QAt graph path.firstStep) SL2Two) :
    Nat.card (QAt graph path.firstStep) = 4 * Nat.card D := by
  have hle (vertex : graph.Vertex) : QAt graph vertex ≤ GAt graph vertex := by
    change graph.twoCoreAt vertex ≤ graph.vertexStabilizer vertex
    rw [graph.twoCoreAt_def]
    exact SevenSix.twoCoreIn_le _
  have hsylows := SevenSix.edge_sylow_data hyp graph path
  have hcores := SevenSix.local_cores_le_edge_sylow hyp graph path
  have hinitial := edge_sylow_card_eq_twice_core _ _ S (hle path.a)
    hcores.1 hsylows.1.2 hquot
  have hfirst := edge_sylow_card_eq_twice_core _ _ S (hle path.firstStep)
    hcores.2 hsylows.2.2 hnext
  have hratio := orders.quotient_card
  change Nat.card Q = 4 * Nat.card D at hratio
  rw [orders.core_eq] at hratio
  omega

public theorem eight_six_next_core_eq_v_of_card_sixteen
    {G : Type u} [Group G] [Finite G] {S P1 P2 : Subgroup G}
    (graph : CosetGraphContext G S P1 P2) (path : CriticalPath graph)
    (hlength : path.length = 2)
    (hv : IsCentralProductModel (VAt graph path.firstStep) C4 Q8)
    (hcore : Nat.card (QAt graph path.firstStep) = 16) :
    QAt graph path.firstStep = VAt graph path.firstStep := by
  have hle : VAt graph path.firstStep ≤ QAt graph path.firstStep :=
    SevenSix.neighbor_join_le_core_of_length_gt_one graph path
    (by omega) path.firstStep
  have hcard := eight_six_c4_quaternion_card hv
  exact (Subgroup.eq_of_le_of_card_ge hle (by omega)).symm

public theorem eight_six_next_core_small_model_or_large_intersection
    {G : Type u} [Group G] [Finite G] {S P1 P2 : Subgroup G}
    (hyp : SectionSevenHypotheses G S P1 P2)
    (graph : CosetGraphContext G S P1 P2) (path : CriticalPath graph)
    {D Q : Subgroup G} (orders : EightSixSmallIndexOrderData graph path D Q)
    (hquot : QuotientIsModel (GAt graph path.a) (QAt graph path.a) SL2Two)
    (hcard : Nat.card (ZAt graph path.a) = 4)
    (hnext : QuotientIsModel (GAt graph path.firstStep)
      (QAt graph path.firstStep) SL2Two)
    (hlength : path.length = 2)
    (hv : IsCentralProductModel (VAt graph path.firstStep) C4 Q8) :
    (QAt graph path.firstStep = VAt graph path.firstStep ∧
      IsCentralProductModel (QAt graph path.firstStep) C4 Q8 ∧ Nat.card D = 4) ∨
    (Nat.card (QAt graph path.firstStep) = 32 ∧ Nat.card D = 8) := by
  have hratio := eight_six_next_core_card_eq_four_intersection
    hyp graph path orders hquot hnext
  rcases eight_six_next_core_card_local hyp graph path orders hquot hcard hnext with
    hsmall | hlarge
  · have hequal := eight_six_next_core_eq_v_of_card_sixteen graph path hlength hv hsmall
    exact Or.inl ⟨hequal, hequal.symm ▸ hv, by omega⟩
  · exact Or.inr ⟨hlarge, by omega⟩

public theorem eight_six_next_residual_intersection_eq_core
    {G : Type u} [Group G] [Finite G] {S P1 P2 : Subgroup G}
    (graph : CosetGraphContext G S P1 P2) (vertex : graph.Vertex) :
    QAt graph vertex ⊓ EAt graph vertex = twoCoreIn (EAt graph vertex) := by
  change graph.twoCoreAt vertex ⊓ graph.twoResidualAt vertex =
    twoCoreIn (graph.twoResidualAt vertex)
  rw [graph.twoCoreAt_def, graph.twoResidualAt_def,
    SevenSix.residual_core_eq_inter_core, inf_comm]

end Stellmacher.SectionEight
