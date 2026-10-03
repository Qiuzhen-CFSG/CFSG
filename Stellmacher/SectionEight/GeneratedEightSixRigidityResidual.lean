module

public import Stellmacher.SectionEight.GeneratedEightSixRigidityReduction
public import Stellmacher.SectionFiveToSeven.ResidualTwoExtension

namespace Stellmacher.SectionEight

open Later SectionsFiveToSeven CosetGraphContext
open scoped Pointwise commutatorElement

universe u

public theorem eight_six_equation_one_residual_eq_initial
    {G : Type u} [Group G] [Finite G] {S P1 P2 : Subgroup G}
    (hyp : SectionSevenHypotheses G S P1 P2)
    (graph : CosetGraphContext G S P1 P2) (path : CriticalPath graph)
    (previous : graph.Vertex) (D L Q : Subgroup G)
    (hL : L = conjugateClosure (QAt graph previous) (GAt graph path.a))
    (data : EightSixEquationOneData graph path previous D L Q) :
    twoResidualIn L = EAt graph path.a := by
  have hSylow := (SevenSix.edge_sylow_data hyp graph path).1
  have hEp : twoResidualIn (GAt graph path.a) ≤ L :=
    (graph.twoResidualAt_def path.a).symm.le.trans data.residual_le
  have hLS : L ⊔ S = GAt graph path.a := by
    apply le_antisymm (sup_le data.closure_le hSylow.1)
    change graph.stabilizer path.a ≤ _
    rw [← SevenSix.twoResidualIn_sup_sylow hSylow]
    exact sup_le_sup hEp le_rfl
  have hSylowL := eight_six_sylow_intersection_of_residual_le
    (GAt graph path.a) L S data.closure_le hSylow hEp
  have hgen : twoResidualIn L ⊔ S = GAt graph path.a := by
    calc
      twoResidualIn L ⊔ S = (twoResidualIn L ⊔ (L ⊓ S)) ⊔ S := by
        rw [sup_assoc, sup_eq_right.mpr (inf_le_right : L ⊓ S ≤ S)]
      _ = L ⊔ S := congrArg (· ⊔ S) (SevenSix.twoResidualIn_sup_sylow hSylowL)
      _ = GAt graph path.a := hLS
  have hLN : GAt graph path.a ≤ Subgroup.normalizer (L : Set G) := by
    rw [hL]
    exact eight_six_conjugate_closure_normalizer _ _
  have hRN : S ≤ Subgroup.normalizer (twoResidualIn L : Set G) := by
    intro actor hactor
    apply Subgroup.mem_normalizer_iff_map_conj_eq.mpr
    exact map_twoResidualAmbient_of_subgroup_image L (MulAut.conj actor).toMonoidHom L
      (Subgroup.mem_normalizer_iff_map_conj_eq.mp (hLN (hSylow.1 hactor)))
  have hSp : IsPGroup 2 S := by
    obtain ⟨_, sylow, hsylow⟩ := hSylow
    rw [← hsylow]
    exact sylow.isPGroup'.map _
  calc
    twoResidualIn L = twoResidualIn (twoResidualIn L ⊔ S) :=
      (twoResidualIn_sup_twoGroup_eq L S hSp hRN).symm
    _ = twoResidualIn (GAt graph path.a) := congrArg twoResidualIn hgen
    _ = EAt graph path.a := (graph.twoResidualAt_def path.a).symm

public theorem eight_six_rigidity_sup_centralizes_initial_core
    {G : Type u} [Group G] [Finite G] {S P1 P2 : Subgroup G}
    (hyp : SectionSevenHypotheses G S P1 P2)
    (graph : CosetGraphContext G S P1 P2) (path : CriticalPath graph)
    (hcenter : ZAt graph path.firstStep ≤ CenterAmbient (GAt graph path.firstStep))
    (previous : graph.Vertex) (D L Q : Subgroup G)
    (hD : D = QAt graph previous ⊓ QAt graph path.firstStep)
    (data : EightSixEquationOneData graph path previous D L Q)
    (U : Subgroup G) (hUD : U ≤ D)
    (hUS : ⁅U, S⁆ ≤ ZAt graph path.firstStep) :
    U ⊔ ZAt graph path.a ≤ QAt graph path.a ⊓
      Subgroup.centralizer (QAt graph path.a : Set G) := by
  let center := ZAt graph path.a
  let core := QAt graph path.a
  let subgroup := U ⊔ center
  have hcores := eight_six_rigidity_core_containments hyp graph path previous D L Q hD data
  have hUcore : U ≤ core := hUD.trans (hcores.1.trans hcores.2.1)
  have hZcore : center ≤ core := hcores.2.2.1.trans (hcores.1.trans hcores.2.1)
  have hZC : center ≤ Subgroup.centralizer (core : Set G) :=
    ((lemma_seven_three hyp graph).center_core path.a path.firstStep
      ((SevenSix.mem_neighborhood_iff_adjacent graph).mpr path.firstStep_adj)).trans
        ((SevenSix.omegaOneCenter_le_centerAmbient _).trans
          (SevenSix.centerAmbient_le_centralizer _))
  have hcoreS : core ≤ S := (SevenSix.local_cores_le_edge_sylow hyp graph path).1
  have hMN := eight_six_rigidity_sup_normal hyp graph path hcenter previous D L Q data U hUD hUS
  have hcoreN : GAt graph path.a ≤ Subgroup.normalizer (core : Set G) :=
    SevenSix.stabilizer_le_normalizer_q graph path.a
  have hcomm : ⁅subgroup, core⁆ ≤ ZAt graph path.firstStep := by
    apply Subgroup.commutator_le.mpr
    intro member hmember other hother
    have hUnorm : U ≤ Subgroup.normalizer (center : Set G) :=
      (hUcore.trans (Subgroup.le_centralizer_iff.mp hZC)).trans
        (Subgroup.centralizer_le_normalizer _)
    have hproduct : member ∈ (U : Set G) * (center : Set G) := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right U center hUnorm]
      exact hmember
    obtain ⟨first, hfirst, second, hsecond, rfl⟩ := hproduct
    have hsecondComm : ⁅second, other⁆ = 1 :=
      commutatorElement_eq_one_iff_mul_comm.mpr
        ((Subgroup.mem_centralizer_iff.mp (hZC hsecond) other hother).symm)
    rw [commutatorElement_mul_left_eq_conj_mul, hsecondComm]
    simpa using hUS (Subgroup.commutator_mem_commutator hfirst (hcoreS hother))
  have hnormal : GAt graph path.a ≤
      Subgroup.normalizer ((⁅subgroup, core⁆ : Subgroup G) : Set G) := by
    intro actor hactor
    apply Subgroup.mem_normalizer_iff_map_conj_eq.mpr
    rw [Subgroup.map_commutator,
      Subgroup.mem_normalizer_iff_map_conj_eq.mp
        (((Subgroup.normal_subgroupOf_iff_le_normalizer hMN.1).mp hMN.2) hactor),
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (hcoreN hactor)]
  have hzero : ⁅subgroup, core⁆ = ⊥ :=
    eight_six_normal_initial_subgroup_le_first_center_eq_bot hyp graph path hcenter _
      hnormal hcomm
  exact le_inf (sup_le hUcore hZcore)
    (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hzero)

public theorem eight_six_rigidity_sup_residual_commutator_le
    {G : Type u} [Group G] [Finite G] {S P1 P2 : Subgroup G}
    (hyp : SectionSevenHypotheses G S P1 P2)
    (graph : CosetGraphContext G S P1 P2) (path : CriticalPath graph)
    (previous : graph.Vertex) (D L Q : Subgroup G)
    (hD : D = QAt graph previous ⊓ QAt graph path.firstStep)
    (hL : L = conjugateClosure (QAt graph previous) (GAt graph path.a))
    (data : EightSixEquationOneData graph path previous D L Q)
    (U : Subgroup G) (hUD : U ≤ D) :
    ⁅U ⊔ ZAt graph path.a, EAt graph path.a⁆ ≤ ZAt graph path.a := by
  rw [← eight_six_equation_one_residual_eq_initial hyp graph path previous D L Q hL data]
  exact (Subgroup.commutator_mono (sup_le hUD
    (eight_six_rigidity_core_containments hyp graph path previous D L Q hD data).2.2.1)
      le_rfl).trans_eq data.residual_commutator

end Stellmacher.SectionEight
