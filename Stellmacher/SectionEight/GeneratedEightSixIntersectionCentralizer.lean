module

public import Stellmacher.SectionEight.GeneratedEightSixCentralizerLifting
public import Stellmacher.SectionEight.GeneratedEightSixCorePartCentralizers
public import Stellmacher.SectionEight.GeneratedEightSixCentralizerRigidity

namespace Stellmacher.SectionEight

open Later SectionsFiveToSeven CosetGraphContext

universe u

public theorem eight_six_first_center_le_intersection_centralizer
    {G : Type u} [Group G] [Finite G] {S P1 P2 : Subgroup G}
    (hyp : SectionSevenHypotheses G S P1 P2)
    (graph : CosetGraphContext G S P1 P2) (path : CriticalPath graph)
    (hcenter : ZAt graph path.firstStep ≤ CenterAmbient (GAt graph path.firstStep))
    (previous : graph.Vertex) (D L Q : Subgroup G)
    (data : EightSixEquationOneData graph path previous D L Q) :
    ZAt graph path.firstStep ≤ D ⊓
      Subgroup.centralizer (VAt graph path.firstStep : Set G) := by
  have hDN : GAt graph path.a ≤ Subgroup.normalizer (D : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer data.intersection_normal.1).mp
      data.intersection_normal.2
  have hZaD : ZAt graph path.a ≤ D := by
    rw [← data.residual_commutator]
    exact Subgroup.le_normalizer_iff_commutator_le_left.mp
      (((SevenSix.twoResidualIn_le L).trans data.closure_le).trans hDN)
  have hVS : VAt graph path.firstStep ≤ S :=
    (le_sup_left.trans data.sylow_intersection.symm.le).trans inf_le_right
  exact le_inf
    ((eight_six_first_center_le_initial hyp graph path hcenter).trans hZaD)
    ((hcenter.trans (SevenSix.centerAmbient_le_centralizer _)).trans
      (Subgroup.centralizer_le (hVS.trans (SevenSix.edge_sylow_data hyp graph path).2.1)))

public theorem eight_six_sylow_normalizes_intersection_centralizer
    {G : Type u} [Group G] [Finite G] {S P1 P2 : Subgroup G}
    (hyp : SectionSevenHypotheses G S P1 P2)
    (graph : CosetGraphContext G S P1 P2) (path : CriticalPath graph)
    (previous : graph.Vertex) (D L Q : Subgroup G)
    (data : EightSixEquationOneData graph path previous D L Q) :
    S ≤ Subgroup.normalizer
      (D ⊓ Subgroup.centralizer (VAt graph path.firstStep : Set G) : Set G) := by
  have hsylow := SevenSix.edge_sylow_data hyp graph path
  have hDN : GAt graph path.a ≤ Subgroup.normalizer (D : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer data.intersection_normal.1).mp
      data.intersection_normal.2
  have hVC : Subgroup.normalizer (VAt graph path.firstStep : Set G) ≤
      Subgroup.normalizer
        (Subgroup.centralizer (VAt graph path.firstStep : Set G) : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer
      (Subgroup.centralizer_le_normalizer (VAt graph path.firstStep : Set G))).mp
        (Subgroup.normal_subgroupOf_centralizer_normalizer _)
  exact (le_inf (hsylow.1.1.trans hDN)
    ((hsylow.2.1.trans (stabilizer_le_normalizer_v graph path.firstStep)).trans hVC)).trans
      Subgroup.inf_normalizer_le_normalizer_inf

public theorem eight_six_intersection_centralizer_of_rigidity
    {G : Type u} [Group G] [Finite G] {S P1 P2 : Subgroup G}
    (hyp : SectionSevenHypotheses G S P1 P2)
    (graph : CosetGraphContext G S P1 P2) (path : CriticalPath graph)
    (hcenter : ZAt graph path.firstStep ≤ CenterAmbient (GAt graph path.firstStep))
    (previous : graph.Vertex) (D L Q : Subgroup G)
    (hD : D = QAt graph previous ⊓ QAt graph path.firstStep)
    (data : EightSixEquationOneData graph path previous D L Q)
    (hrigidity : ∀ U : Subgroup G,
      U ≤ D ⊓ Subgroup.centralizer (VAt graph path.firstStep : Set G) →
      ⁅U, S⁆ ≤ ZAt graph path.firstStep → U ≤ ZAt graph path.firstStep) :
    D ⊓ Subgroup.centralizer (VAt graph path.firstStep : Set G) =
      ZAt graph path.firstStep := by
  apply le_antisymm
  · have hS : IsPGroup 2 S := by
      obtain ⟨_, sylow, hsylow⟩ := (SevenSix.edge_sylow_data hyp graph path).1
      rw [← hsylow]
      exact sylow.isPGroup'.map _
    apply eight_six_two_subgroup_le_of_commutator_test S _ _ hS
    · exact inf_le_left.trans ((hD ▸ inf_le_right).trans
        (SevenSix.local_cores_le_edge_sylow hyp graph path).2)
    · exact eight_six_sylow_normalizes_intersection_centralizer hyp graph path
        previous D L Q data
    · exact hrigidity
  · exact eight_six_first_center_le_intersection_centralizer hyp graph path hcenter
      previous D L Q data

end Stellmacher.SectionEight

namespace Stellmacher.SectionEight

open Later SectionsFiveToSeven CosetGraphContext

universe u

public theorem generated_eight_six_intersection_centralizer
    {H : Type u} [Group H] [Finite H]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    (ctx : GeneratedSectionEightContext H S0 S P1 P2)
    (hcenter : ZAt ctx.Γ ctx.criticalPath.firstStep ≤
      CenterAmbient (GAt ctx.Γ ctx.criticalPath.firstStep))
    (hquot : QuotientIsModel (GAt ctx.Γ ctx.criticalPath.a)
      (QAt ctx.Γ ctx.criticalPath.a) SL2Two)
    (hlength : ctx.criticalPath.length = 2)
    (hcard : Nat.card (ZAt ctx.Γ ctx.criticalPath.a) = 4)
    (previous : ctx.Γ.Vertex)
    (hprev : previous ∈ Later.Neighborhood ctx.Γ ctx.criticalPath.a ∧
      previous ≠ ctx.criticalPath.firstStep)
    (D L Q : Subgroup (P1 ⊔ P2 : Subgroup H))
    (hD : D = QAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.firstStep)
    (hL : L = SectionsFiveToSeven.conjugateClosure
      (QAt ctx.Γ previous) (GAt ctx.Γ ctx.criticalPath.a))
    (hQ : Q = twoCoreIn L)
    (data : EightSixEquationOneData ctx.Γ ctx.criticalPath previous D L Q) :
    D ⊓ Subgroup.centralizer
      (VAt ctx.Γ ctx.criticalPath.firstStep : Set (P1 ⊔ P2 : Subgroup H)) =
      ZAt ctx.Γ ctx.criticalPath.firstStep := by
  apply eight_six_intersection_centralizer_of_rigidity ctx.sectionSeven ctx.Γ
    ctx.criticalPath hcenter previous D L Q hD data
  intro U hU hUS
  exact generated_eight_six_centralizer_rigidity ctx hcenter hquot hlength hcard
    previous hprev D L Q hD hL hQ data U hU hUS

public theorem generated_eight_six_core_part_centralizer
    {H : Type u} [Group H] [Finite H]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    (ctx : GeneratedSectionEightContext H S0 S P1 P2)
    (hcenter : ZAt ctx.Γ ctx.criticalPath.firstStep ≤
      CenterAmbient (GAt ctx.Γ ctx.criticalPath.firstStep))
    (hquot : QuotientIsModel (GAt ctx.Γ ctx.criticalPath.a)
      (QAt ctx.Γ ctx.criticalPath.a) SL2Two)
    (hlength : ctx.criticalPath.length = 2)
    (hcard : Nat.card (ZAt ctx.Γ ctx.criticalPath.a) = 4)
    (previous : ctx.Γ.Vertex)
    (hprev : previous ∈ Later.Neighborhood ctx.Γ ctx.criticalPath.a ∧
      previous ≠ ctx.criticalPath.firstStep)
    (D L Q : Subgroup (P1 ⊔ P2 : Subgroup H))
    (hD : D = QAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.firstStep)
    (hL : L = SectionsFiveToSeven.conjugateClosure
      (QAt ctx.Γ previous) (GAt ctx.Γ ctx.criticalPath.a))
    (hQ : Q = twoCoreIn L)
    (data : EightSixEquationOneData ctx.Γ ctx.criticalPath previous D L Q) :
    D ⊓ Subgroup.centralizer
      (VAt ctx.Γ ctx.criticalPath.firstStep ⊓ QAt ctx.Γ ctx.criticalPath.a :
        Set (P1 ⊔ P2 : Subgroup H)) = ZAt ctx.Γ ctx.criticalPath.a := by
  exact eight_six_first_core_part_centralizer_of_intersection_centralizer
    ctx.sectionSeven ctx.Γ ctx.criticalPath hcenter hquot hcard previous D L Q hD data
      (generated_eight_six_intersection_centralizer ctx hcenter hquot
        hlength hcard previous hprev D L Q hD hL hQ data)

public theorem generated_eight_six_predecessor_core_part_centralizer
    {H : Type u} [Group H] [Finite H]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    (ctx : GeneratedSectionEightContext H S0 S P1 P2)
    (previous : ctx.Γ.Vertex)
    (hprev : previous ∈ Later.Neighborhood ctx.Γ ctx.criticalPath.a ∧
      previous ≠ ctx.criticalPath.firstStep)
    (D L Q : Subgroup (P1 ⊔ P2 : Subgroup H))
    (_hD : D = QAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.firstStep)
    (_hL : L = SectionsFiveToSeven.conjugateClosure
      (QAt ctx.Γ previous) (GAt ctx.Γ ctx.criticalPath.a))
    (_hQ : Q = twoCoreIn L)
    (data : EightSixEquationOneData ctx.Γ ctx.criticalPath previous D L Q)
    (hfirst : D ⊓ Subgroup.centralizer
      (VAt ctx.Γ ctx.criticalPath.firstStep ⊓ QAt ctx.Γ ctx.criticalPath.a :
        Set (P1 ⊔ P2 : Subgroup H)) = ZAt ctx.Γ ctx.criticalPath.a) :
    D ⊓ Subgroup.centralizer
      (VAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.a :
        Set (P1 ⊔ P2 : Subgroup H)) = ZAt ctx.Γ ctx.criticalPath.a := by
  exact eight_six_predecessor_core_part_centralizer_of_first_core_part
    ctx.sectionSeven ctx.Γ ctx.criticalPath previous hprev.1 D L Q data hfirst

end Stellmacher.SectionEight
