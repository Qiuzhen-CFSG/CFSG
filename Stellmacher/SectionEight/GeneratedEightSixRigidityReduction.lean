module

public import Stellmacher.SectionEight.GeneratedEightSixEquationOneSetup
public import Stellmacher.SectionEight.GeneratedEightSixIntersectionCommutator

namespace Stellmacher.SectionEight

open Later SectionsFiveToSeven CosetGraphContext
open scoped commutatorElement
open scoped Pointwise

universe u

private theorem normalizes_sup_of_commutator_le
    {G : Type u} [Group G] (actors seed center : Subgroup G)
    (hnormal : actors ≤ Subgroup.normalizer (center : Set G))
    (hcomm : ⁅seed, actors⁆ ≤ center) :
    actors ≤ Subgroup.normalizer ((seed ⊔ center : Subgroup G) : Set G) := by
  apply Subgroup.le_normalizer_iff.mpr
  intro actor hactor member hmember
  have hmap : (seed ⊔ center).map (MulAut.conj actor).toMonoidHom ≤ seed ⊔ center := by
    rw [Subgroup.map_sup]
    apply sup_le
    · rintro element ⟨generator, hgenerator, rfl⟩
      have hcomm' : ⁅actor, generator⁆ ∈ center := by
        rw [← commutatorElement_inv]
        exact center.inv_mem
          (hcomm (Subgroup.commutator_mem_commutator hgenerator hactor))
      have hproduct := (seed ⊔ center).mul_mem
        ((show center ≤ seed ⊔ center from le_sup_right) hcomm')
        ((show seed ≤ seed ⊔ center from le_sup_left) hgenerator)
      simpa [commutatorElement_def, mul_assoc] using hproduct
    · rintro element ⟨generator, hgenerator, rfl⟩
      exact (show center ≤ seed ⊔ center from le_sup_right)
        (Subgroup.le_normalizer_iff.mp hnormal actor hactor generator hgenerator)
  exact hmap (Subgroup.mem_map_of_mem _ hmember)

private theorem normalizes_commutator
    {G : Type u} [Group G] (actors first second : Subgroup G)
    (hfirst : actors ≤ Subgroup.normalizer (first : Set G))
    (hsecond : actors ≤ Subgroup.normalizer (second : Set G)) :
    actors ≤ Subgroup.normalizer ((⁅first, second⁆ : Subgroup G) : Set G) := by
  intro actor hactor
  apply Subgroup.mem_normalizer_iff_map_conj_eq.mpr
  rw [Subgroup.map_commutator,
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (hfirst hactor),
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (hsecond hactor)]

public theorem eight_six_normal_initial_subgroup_le_first_center_eq_bot
    {G : Type u} [Group G] [Finite G] {S P1 P2 : Subgroup G}
    (hyp : SectionSevenHypotheses G S P1 P2)
    (graph : CosetGraphContext G S P1 P2) (path : CriticalPath graph)
    (hcenter : ZAt graph path.firstStep ≤ CenterAmbient (GAt graph path.firstStep))
    (subgroup : Subgroup G)
    (hnormal : GAt graph path.a ≤ Subgroup.normalizer (subgroup : Set G))
    (hle : subgroup ≤ ZAt graph path.firstStep) : subgroup = ⊥ := by
  have hfirst : GAt graph path.firstStep ≤ Subgroup.normalizer (subgroup : Set G) :=
    (Subgroup.le_centralizer_iff.mp ((hle.trans hcenter).trans
      (SevenSix.centerAmbient_le_centralizer _))).trans
        (Subgroup.centralizer_le_normalizer _)
  have hgen : GAt graph path.a ⊔ GAt graph path.firstStep = ⊤ := by
    rcases path.edge_stabilizers_are_P with hedge | hedge
    · exact (congrArg₂ (· ⊔ ·) hedge.1 hedge.2).trans hyp.generated
    · exact (congrArg₂ (· ⊔ ·) hedge.1 hedge.2).trans
        ((sup_comm P2 P1).trans hyp.generated)
  have hN : subgroup.Normal := Subgroup.normalizer_eq_top_iff.mp
    (top_unique (hgen ▸ sup_le hnormal hfirst))
  have hp : IsPGroup 2 subgroup := by
    let _ := SevenSix.z_isElementaryAbelian_of_neighbor hyp graph
      ((SevenSix.mem_neighborhood_iff_adjacent graph).mpr
        (graph.adjacent_symm path.firstStep_adj))
    exact (IsElementaryAbelian.isPGroup 2 (ZAt graph path.firstStep)).to_le hle
  exact le_bot_iff.mp ((show subgroup ≤ pCore 2 G from
    le_sSup ⟨hN, hp⟩).trans_eq hyp.twoCore_eq_bot)

public theorem eight_six_rigidity_core_containments
    {G : Type u} [Group G] [Finite G] {S P1 P2 : Subgroup G}
    (hyp : SectionSevenHypotheses G S P1 P2)
    (graph : CosetGraphContext G S P1 P2) (path : CriticalPath graph)
    (previous : graph.Vertex) (D L Q : Subgroup G)
    (hD : D = QAt graph previous ⊓ QAt graph path.firstStep)
    (data : EightSixEquationOneData graph path previous D L Q) :
    D ≤ Q ∧ Q ≤ QAt graph path.a ∧ ZAt graph path.a ≤ D ∧
      ZAt graph path.a ≤ Subgroup.centralizer (Q : Set G) := by
  have hDp : IsPGroup 2 D := by
    have hp : IsPGroup 2 (QAt graph path.firstStep) := by
      change IsPGroup 2 (graph.twoCoreAt path.firstStep)
      rw [graph.twoCoreAt_def]
      exact (pCore_isPGroup (p := 2)).map _
    exact hp.to_le (hD ▸ inf_le_right)
  have hDQa : D ≤ QAt graph path.a := by
    have hnative : IsPGroup 2 (D.subgroupOf (GAt graph path.a)) :=
      hDp.of_equiv (Subgroup.subgroupOfEquivOfLe data.intersection_normal.1).symm
    have hle : D.subgroupOf (GAt graph path.a) ≤ pCore 2 (GAt graph path.a) :=
      le_sSup ⟨data.intersection_normal.2, hnative⟩
    change D ≤ graph.twoCoreAt path.a
    rw [graph.twoCoreAt_def]
    calc
      D = (D.subgroupOf (GAt graph path.a)).map (GAt graph path.a).subtype :=
        (Subgroup.map_subgroupOf_eq_of_le data.intersection_normal.1).symm
      _ ≤ _ := Subgroup.map_mono hle
  have hDQ : D ≤ Q := by rw [data.core_generation]; exact le_sup_right
  have hQQa : Q ≤ QAt graph path.a := by
    rw [data.core_generation]
    exact sup_le (sup_le inf_le_right inf_le_right) hDQa
  have hZD : ZAt graph path.a ≤ D := by
    rw [← data.residual_commutator]
    exact Subgroup.le_normalizer_iff_commutator_le_left.mp
      (((SevenSix.twoResidualIn_le L).trans data.closure_le).trans
        ((Subgroup.normal_subgroupOf_iff_le_normalizer data.intersection_normal.1).mp
          data.intersection_normal.2))
  have hZQ : ZAt graph path.a ≤ Subgroup.centralizer (Q : Set G) :=
    (((lemma_seven_three hyp graph).center_core path.a path.firstStep
      ((SevenSix.mem_neighborhood_iff_adjacent graph).mpr path.firstStep_adj)).trans
        ((SevenSix.omegaOneCenter_le_centerAmbient _).trans
          (SevenSix.centerAmbient_le_centralizer _))).trans
            (Subgroup.centralizer_le hQQa)
  exact ⟨hDQ, hQQa, hZD, hZQ⟩

public theorem eight_six_rigidity_sup_normal
    {G : Type u} [Group G] [Finite G] {S P1 P2 : Subgroup G}
    (hyp : SectionSevenHypotheses G S P1 P2)
    (graph : CosetGraphContext G S P1 P2) (path : CriticalPath graph)
    (hcenter : ZAt graph path.firstStep ≤ CenterAmbient (GAt graph path.firstStep))
    (previous : graph.Vertex) (D L Q : Subgroup G)
    (data : EightSixEquationOneData graph path previous D L Q)
    (U : Subgroup G) (hUD : U ≤ D)
    (hUS : ⁅U, S⁆ ≤ ZAt graph path.firstStep) :
    NormalIn (U ⊔ ZAt graph path.a) (GAt graph path.a) := by
  let initial := GAt graph path.a
  let center := ZAt graph path.a
  have hZnormal : initial ≤ Subgroup.normalizer (center : Set G) :=
    stabilizer_le_normalizer_z graph path.a
  have hRnormal : twoResidualIn L ≤ Subgroup.normalizer ((U ⊔ center : Subgroup G) : Set G) :=
    normalizes_sup_of_commutator_le _ _ _
      (((SevenSix.twoResidualIn_le L).trans data.closure_le).trans hZnormal)
      ((Subgroup.commutator_mono hUD le_rfl).trans_eq data.residual_commutator)
  have hSnormal : S ≤ Subgroup.normalizer ((U ⊔ center : Subgroup G) : Set G) :=
    normalizes_sup_of_commutator_le _ _ _
      ((SevenSix.edge_sylow_data hyp graph path).1.1.trans hZnormal)
      (hUS.trans (eight_six_first_center_le_initial hyp graph path hcenter))
  have hLS : L ⊔ S = initial := by
    apply le_antisymm
      (sup_le data.closure_le (SevenSix.edge_sylow_data hyp graph path).1.1)
    change graph.stabilizer path.a ≤ _
    rw [← SevenSix.twoResidualIn_sup_sylow
      (SevenSix.edge_sylow_data hyp graph path).1]
    exact sup_le_sup ((graph.twoResidualAt_def path.a).symm.le.trans data.residual_le)
      le_rfl
  have hSylowL : IsSylowTwoIn (L ⊓ S) L :=
    eight_six_sylow_intersection_of_residual_le initial L S data.closure_le
      (SevenSix.edge_sylow_data hyp graph path).1
      ((graph.twoResidualAt_def path.a).symm.le.trans data.residual_le)
  have hgen : twoResidualIn L ⊔ S = initial := by
    calc
      twoResidualIn L ⊔ S = (twoResidualIn L ⊔ (L ⊓ S)) ⊔ S := by
        rw [sup_assoc, sup_eq_right.mpr (inf_le_right : L ⊓ S ≤ S)]
      _ = L ⊔ S := congrArg (· ⊔ S) (SevenSix.twoResidualIn_sup_sylow hSylowL)
      _ = initial := hLS
  have hZle : center ≤ initial :=
    (((lemma_seven_three hyp graph).center_core path.a path.firstStep
      ((SevenSix.mem_neighborhood_iff_adjacent graph).mpr path.firstStep_adj)).trans
        (Subgroup.map_subtype_le _)).trans
          (show QAt graph path.a ≤ initial from
            (graph.twoCoreAt_def path.a).le.trans (Subgroup.map_subtype_le _))
  have hle : U ⊔ center ≤ initial :=
    sup_le (hUD.trans data.intersection_normal.1) hZle
  exact ⟨hle, (Subgroup.normal_subgroupOf_iff_le_normalizer hle).mpr
    (hgen ▸ sup_le hRnormal hSnormal)⟩

public theorem eight_six_rigidity_sup_centralizes_core
    {G : Type u} [Group G] [Finite G] {S P1 P2 : Subgroup G}
    (hyp : SectionSevenHypotheses G S P1 P2)
    (graph : CosetGraphContext G S P1 P2) (path : CriticalPath graph)
    (hcenter : ZAt graph path.firstStep ≤ CenterAmbient (GAt graph path.firstStep))
    (previous : graph.Vertex) (D L Q : Subgroup G)
    (hD : D = QAt graph previous ⊓ QAt graph path.firstStep)
    (hL : L = conjugateClosure (QAt graph previous) (GAt graph path.a))
    (hQ : Q = twoCoreIn L)
    (data : EightSixEquationOneData graph path previous D L Q)
    (U : Subgroup G) (hUD : U ≤ D)
    (hUS : ⁅U, S⁆ ≤ ZAt graph path.firstStep) :
    U ⊔ ZAt graph path.a ≤ Q ⊓ Subgroup.centralizer (Q : Set G) := by
  let center := ZAt graph path.a
  let subgroup := U ⊔ center
  have hcores := eight_six_rigidity_core_containments hyp graph path previous D L Q hD data
  have hUQ : U ≤ Q := hUD.trans hcores.1
  have hZQ : center ≤ Q := hcores.2.2.1.trans hcores.1
  have hZC : center ≤ Subgroup.centralizer (Q : Set G) := hcores.2.2.2
  have hQS : Q ≤ S :=
    (le_sup_right.trans data.sylow_intersection.symm.le).trans inf_le_right
  have hMN := eight_six_rigidity_sup_normal hyp graph path hcenter previous D L Q data U hUD hUS
  have hQN : GAt graph path.a ≤ Subgroup.normalizer (Q : Set G) := by
    rw [hQ, twoCoreIn]
    apply (eight_six_conjugate_closure_normalizer (QAt graph previous)
      (GAt graph path.a)).trans
    rw [← hL]
    exact BenderSuzuki.External.hkt_normalizer_le_normalizer_map_subtype_of_characteristic
      L (pCore 2 L)
  have hcomm : ⁅subgroup, Q⁆ ≤ ZAt graph path.firstStep := by
    apply Subgroup.commutator_le.mpr
    intro member hmember other hother
    have hUnorm : U ≤ Subgroup.normalizer (center : Set G) :=
      (hUQ.trans (Subgroup.le_centralizer_iff.mp hZC)).trans
        (Subgroup.centralizer_le_normalizer _)
    have hproduct : member ∈ (U : Set G) * (center : Set G) := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right U center hUnorm]
      exact hmember
    obtain ⟨first, hfirst, second, hsecond, rfl⟩ := hproduct
    have hsecondComm : ⁅second, other⁆ = 1 :=
      commutatorElement_eq_one_iff_mul_comm.mpr
        ((Subgroup.mem_centralizer_iff.mp (hZC hsecond) other hother).symm)
    rw [commutatorElement_mul_left_eq_conj_mul, hsecondComm]
    simpa using hUS (Subgroup.commutator_mem_commutator hfirst (hQS hother))
  have hzero : ⁅subgroup, Q⁆ = ⊥ :=
    eight_six_normal_initial_subgroup_le_first_center_eq_bot hyp graph path hcenter _
      (normalizes_commutator _ _ _
        ((Subgroup.normal_subgroupOf_iff_le_normalizer hMN.1).mp hMN.2) hQN) hcomm
  exact le_inf (sup_le hUQ hZQ)
    (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hzero)

end Stellmacher.SectionEight
