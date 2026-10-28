module

public import Stellmacher.SectionEight.GeneratedEightSixBaseSetup
public import Theory.Frattini.PGroupMap

namespace Stellmacher.SectionEight

open Later SectionsFiveToSeven CosetGraphContext
open scoped commutatorElement IsMulCommutative

universe u

public theorem eight_six_frattini_centralizes_of_central_elementary_commutator
    {G : Type u} [Group G] [Finite G]
    (D V Z : Subgroup G) (hD : IsPGroup 2 D)
    (hZ : IsElementaryAbelian 2 Z)
    (hcentral : Z ≤ Subgroup.centralizer (D : Set G))
    (hcommutator : ⁅D, V⁆ ≤ Z) :
    FrattiniAmbient D ≤ Subgroup.centralizer (V : Set G) := by
  let _ : Fact (IsPGroup 2 D) := ⟨hD⟩
  let _ : IsElementaryAbelian 2 Z := hZ
  let _ : Fact (IsPGroup 2 Z) := ⟨IsElementaryAbelian.isPGroup 2 Z⟩
  rintro element ⟨representative, hrepresentative, rfl⟩
  rw [Subgroup.mem_centralizer_iff]
  intro actor hactor
  let actionCommutator : D →* Z := {
    toFun := fun member => ⟨⁅(member : G), actor⁆,
      hcommutator (Subgroup.commutator_mem_commutator member.property hactor)⟩
    map_one' := by apply Subtype.ext; simp
    map_mul' := by
      intro first second
      apply Subtype.ext
      change ⁅(first : G) * (second : G), actor⁆ =
        ⁅(first : G), actor⁆ * ⁅(second : G), actor⁆
      rw [commutatorElement_mul_left_eq_conj_mul]
      have hsecond := Subgroup.mem_centralizer_iff.mp
        (hcentral (hcommutator
          (Subgroup.commutator_mem_commutator second.property hactor)))
        first first.property
      rw [hsecond, mul_inv_cancel_right]
      exact congrArg Subtype.val (mul_comm
        (⟨⁅(second : G), actor⁆, hcommutator
          (Subgroup.commutator_mem_commutator second.property hactor)⟩ : Z)
        (⟨⁅(first : G), actor⁆, hcommutator
          (Subgroup.commutator_mem_commutator first.property hactor)⟩ : Z)) }
  have hmem := frattini_map_le_of_isPGroup (p := 2) actionCommutator
    (Subgroup.mem_map_of_mem actionCommutator hrepresentative)
  rw [frattini_eq_bot_of_isElementaryAbelian (p := 2)] at hmem
  have hone : actionCommutator representative = 1 := hmem
  exact (commutatorElement_eq_one_iff_mul_comm.mp
    (congrArg Subtype.val hone)).symm

public theorem eight_six_intersection_frattini_centralizes
    {G : Type u} [Group G] [Finite G]
    {S P1 P2 : Subgroup G}
    (hyp : SectionSevenHypotheses G S P1 P2)
    (graph : CosetGraphContext G S P1 P2) (path : CriticalPath graph)
    (hcenter : ZAt graph path.firstStep ≤ CenterAmbient (GAt graph path.firstStep))
    (previous : graph.Vertex) (D L Q : Subgroup G)
    (hD : D = QAt graph previous ⊓ QAt graph path.firstStep)
    (data : EightSixEquationOneData graph path previous D L Q) :
    FrattiniAmbient D ≤ Subgroup.centralizer (VAt graph path.firstStep : Set G) := by
  have hDQ : D ≤ QAt graph path.firstStep := hD ▸ inf_le_right
  have hQG : QAt graph path.firstStep ≤ GAt graph path.firstStep := by
    change graph.twoCoreAt path.firstStep ≤ _
    rw [graph.twoCoreAt_def]
    exact Subgroup.map_subtype_le _
  have hDp : IsPGroup 2 D := by
    have hcore : IsPGroup 2 (QAt graph path.firstStep) := by
      change IsPGroup 2 (graph.twoCoreAt path.firstStep)
      rw [graph.twoCoreAt_def]
      exact (pCore_isPGroup (p := 2) (G := GAt graph path.firstStep)).map
        (GAt graph path.firstStep).subtype
    exact hcore.of_injective (Subgroup.inclusion hDQ) (Subgroup.inclusion_injective hDQ)
  apply eight_six_frattini_centralizes_of_central_elementary_commutator D
    (VAt graph path.firstStep) (ZAt graph path.firstStep) hDp
  · exact SevenSix.z_isElementaryAbelian_of_neighbor hyp graph
      ((SevenSix.mem_neighborhood_iff_adjacent graph).mpr
        (graph.adjacent_symm path.firstStep_adj))
  · exact (hcenter.trans (SevenSix.centerAmbient_le_centralizer _)).trans
      (Subgroup.centralizer_le (hDQ.trans hQG))
  · rw [Subgroup.commutator_comm]
    exact (Subgroup.commutator_mono le_rfl hDQ).trans_eq data.first_commutator

public theorem eight_six_intersection_frattini_eq_bot_of_centralizer
    {G : Type u} [Group G] [Finite G]
    {S P1 P2 : Subgroup G}
    (hyp : SectionSevenHypotheses G S P1 P2)
    (graph : CosetGraphContext G S P1 P2) (path : CriticalPath graph)
    (hcenter : ZAt graph path.firstStep ≤ CenterAmbient (GAt graph path.firstStep))
    (previous : graph.Vertex) (D L Q : Subgroup G)
    (hD : D = QAt graph previous ⊓ QAt graph path.firstStep)
    (data : EightSixEquationOneData graph path previous D L Q)
    (hcentralizer : D ⊓ Subgroup.centralizer (VAt graph path.firstStep : Set G) =
      ZAt graph path.firstStep) :
    FrattiniAmbient D = ⊥ := by
  have hPhiZ : FrattiniAmbient D ≤ ZAt graph path.firstStep := by
    rw [← hcentralizer]
    exact le_inf (Subgroup.map_subtype_le _) (eight_six_intersection_frattini_centralizes
      hyp graph path hcenter previous D L Q hD data)
  have hfirst : GAt graph path.firstStep ≤
      Subgroup.normalizer (FrattiniAmbient D : Set G) :=
    (Subgroup.le_centralizer_iff.mp ((hPhiZ.trans hcenter).trans
      (SevenSix.centerAmbient_le_centralizer _))).trans
        (Subgroup.centralizer_le_normalizer _)
  have hinitial : GAt graph path.a ≤ Subgroup.normalizer (FrattiniAmbient D : Set G) :=
    ((Subgroup.normal_subgroupOf_iff_le_normalizer data.intersection_normal.1).mp
      data.intersection_normal.2).trans
        (BenderSuzuki.External.hkt_normalizer_le_normalizer_map_subtype_of_characteristic
          D (frattini D))
  have hgen : GAt graph path.a ⊔ GAt graph path.firstStep = ⊤ := by
    rcases path.edge_stabilizers_are_P with hedge | hedge
    · exact (congrArg₂ (· ⊔ ·) hedge.1 hedge.2).trans hyp.generated
    · exact (congrArg₂ (· ⊔ ·) hedge.1 hedge.2).trans (sup_comm P2 P1 |>.trans hyp.generated)
  have hnormal : (FrattiniAmbient D).Normal := Subgroup.normalizer_eq_top_iff.mp
    (top_unique (hgen ▸ sup_le hinitial hfirst))
  have hZp : IsPGroup 2 (ZAt graph path.firstStep) := by
    let _ := SevenSix.z_isElementaryAbelian_of_neighbor hyp graph
      ((SevenSix.mem_neighborhood_iff_adjacent graph).mpr
        (graph.adjacent_symm path.firstStep_adj))
    exact IsElementaryAbelian.isPGroup 2 _
  have hPhip : IsPGroup 2 (FrattiniAmbient D) := hZp.of_injective
    (Subgroup.inclusion hPhiZ) (Subgroup.inclusion_injective hPhiZ)
  exact le_bot_iff.mp ((show FrattiniAmbient D ≤ pCore 2 G from
    le_sSup ⟨hnormal, hPhip⟩).trans_eq hyp.twoCore_eq_bot)

end Stellmacher.SectionEight
