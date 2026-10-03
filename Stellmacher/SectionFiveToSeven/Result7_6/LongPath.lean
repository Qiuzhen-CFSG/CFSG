module

public import Stellmacher.SectionFiveToSeven.Result7_6.GraphFacts
public import Stellmacher.SectionFiveToSeven.Result7_6.LocalFacts
public import Stellmacher.SectionThree.LemmaThreeFiveOmega
public import Stellmacher.SectionThree.ResidualCoreTransfer

/-!
# Stellmacher (7.6): non-normality for a longer critical path

Assume the first core intersection is normal. Transitivity and critical
minimality put every neighbor center in the intersection, where their join
centralizes it. Endpoint alignment from (7.5) ensures the initial core is not
contained in the next core. The residual-core transfer from (3.4) then places
the next residual 2-core in this intersection. The omega-center refinement
of (3.5), together with the center equality from (7.5), forces the next
residual to centralize the neighbor-center join. Thus the initial vertex
center is normalized by both generating local groups and becomes a normal
2-subgroup of the ambient group, contradicting its trivial 2-core and
criticality. This proves the longer-path branch of (7.6)(a). The retained
longer-path and first-edge normality hypotheses also expose the Thompson
noncontainment needed by the local Section Eight interface: those hypotheses
are contradictory by (7.6), so the noncontainment follows without ambient
Hypothesis Two data.

Source: B. Stellmacher, Journal of Algebra 190 (1997), Lemma (7.6),
pp. 35–36; `refs/latex/stellmacher-n-group.tex`.
-/

open scoped Pointwise

namespace Stellmacher.SectionsFiveToSeven.SevenSix

open CosetGraphContext

universe u v

private theorem v_le_core_intersection_of_length_gt_one
    {G : Type u} [Group G] [Finite G]
    {S P1 P2 : Subgroup G}
    (h : SectionSevenHypotheses G S P1 P2)
    (Gamma : CosetGraphContext G S P1 P2) (cp : CriticalPath Gamma)
    (hlen : 1 < cp.length)
    (hnormal : IsNormalIn (q Gamma cp.a ⊓ q Gamma cp.firstStep)
      (stabilizer Gamma cp.firstStep)) :
    v Gamma cp.firstStep ≤ q Gamma cp.a ⊓ q Gamma cp.firstStep := by
  rw [v, Gamma.vAt_def]
  refine sSup_le fun Z hZ ↦ ?_
  rcases hZ with ⟨m, hm, rfl⟩
  have hm' : cp.firstStep ∈ neighborhood Gamma m :=
    (mem_neighborhood_iff_adjacent Gamma).2
      (Gamma.adjacent_symm ((mem_neighborhood_iff_adjacent Gamma).1 hm))
  have hzmQm : z Gamma m ≤ q Gamma m :=
    ((lemma_seven_three h Gamma).center_core m cp.firstStep hm').trans
      ((omegaOneCenter_le_centerAmbient (q Gamma m)).trans
        (Subgroup.map_subtype_le (Subgroup.center (q Gamma m))))
  have hzmQ : z Gamma m ≤ q Gamma cp.firstStep := by
    apply critical_minimality Gamma cp
    have hdist : Gamma.distance m cp.firstStep = 1 := by
      exact (adjacent_iff_distance_eq_one Gamma).mp
        ((mem_neighborhood_iff_adjacent Gamma).1 hm')
    omega
  have hEq := core_intersection_eq_neighbor_intersection_of_normal
    h Gamma cp hnormal m hm
  exact (le_inf hzmQm hzmQ).trans_eq hEq

private theorem v_centralizes_core_intersection_of_normal
    {G : Type u} [Group G] [Finite G]
    {S P1 P2 : Subgroup G}
    (h : SectionSevenHypotheses G S P1 P2)
    (Gamma : CosetGraphContext G S P1 P2) (cp : CriticalPath Gamma)
    (hnormal : IsNormalIn (q Gamma cp.a ⊓ q Gamma cp.firstStep)
      (stabilizer Gamma cp.firstStep)) :
    ⁅v Gamma cp.firstStep, q Gamma cp.a ⊓ q Gamma cp.firstStep⁆ = ⊥ := by
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer, v,
    Gamma.vAt_def]
  refine sSup_le fun Z hZ ↦ ?_
  rcases hZ with ⟨m, hm, rfl⟩
  have hm' : cp.firstStep ∈ neighborhood Gamma m :=
    (mem_neighborhood_iff_adjacent Gamma).2
      (Gamma.adjacent_symm ((mem_neighborhood_iff_adjacent Gamma).1 hm))
  have hzmCentralQm : z Gamma m ≤
      Subgroup.centralizer (q Gamma m : Set G) :=
    ((lemma_seven_three h Gamma).center_core m cp.firstStep hm').trans
      ((omegaOneCenter_le_centerAmbient (q Gamma m)).trans
        (centerAmbient_le_centralizer (q Gamma m)))
  have hEq := core_intersection_eq_neighbor_intersection_of_normal
    h Gamma cp hnormal m hm
  have hNleQm : q Gamma cp.a ⊓ q Gamma cp.firstStep ≤ q Gamma m := by
    rw [← hEq]
    exact inf_le_left
  intro z0 hz0
  rw [Subgroup.mem_centralizer_iff]
  intro n hn
  exact (Subgroup.mem_centralizer_iff.mp (hzmCentralQm hz0)) n
    (hNleQm hn)

private theorem longer_endpoint_comm_and_core_noncontainment
    {G : Type u} [Group G] [Finite G]
    {S P1 P2 : Subgroup G}
    (h : SectionSevenHypotheses G S P1 P2)
    (Gamma : CosetGraphContext G S P1 P2) (cp : CriticalPath Gamma)
    (hlen : 1 < cp.length)
    (hnormal : IsNormalIn (q Gamma cp.a ⊓ q Gamma cp.firstStep)
      (stabilizer Gamma cp.firstStep)) :
    ⁅z Gamma cp.a, z Gamma cp.a'⁆ = ⊥ ∧
      ¬ q Gamma cp.a ≤ q Gamma cp.firstStep := by
  let second : Gamma.Vertex := cp.path ⟨2, by omega⟩
  have hsecondAdj : Gamma.adjacent cp.firstStep second := by
    have hp := cp.path_adj ⟨1, by omega⟩
    simpa [second, cp.path_first] using hp
  have hsecondMem : second ∈ neighborhood Gamma cp.firstStep :=
    (mem_neighborhood_iff_adjacent Gamma).2 hsecondAdj
  have hzEndFirst : z Gamma cp.a' ≤ q Gamma cp.firstStep := by
    apply critical_minimality Gamma cp
    rw [Gamma.distance_symm]
    have hp := path_distance_le Gamma cp 1 cp.length (by omega) le_rfl
    rw [cp.path_first, cp.path_end] at hp
    omega
  have hzEndSecond : z Gamma cp.a' ≤ q Gamma second := by
    apply critical_minimality Gamma cp
    rw [Gamma.distance_symm]
    have hp := path_distance_le Gamma cp 2 cp.length (by omega) le_rfl
    have hend : cp.path ⟨cp.length, Nat.lt_succ_self _⟩ = cp.a' :=
      cp.path_end
    dsimp [second]
    rw [← hend]
    exact hp.trans_lt (by omega)
  have hEq := core_intersection_eq_neighbor_intersection_of_normal
    h Gamma cp hnormal second hsecondMem
  have hzEndA : z Gamma cp.a' ≤ q Gamma cp.a := by
    exact ((le_inf hzEndSecond hzEndFirst).trans_eq hEq).trans inf_le_left
  have haMem : cp.firstStep ∈ neighborhood Gamma cp.a :=
    (mem_neighborhood_iff_adjacent Gamma).2 cp.firstStep_adj
  have hZaCentralA : z Gamma cp.a ≤
      Subgroup.centralizer (q Gamma cp.a : Set G) :=
    ((lemma_seven_three h Gamma).center_core cp.a cp.firstStep haMem).trans
      ((omegaOneCenter_le_centerAmbient (q Gamma cp.a)).trans
        (centerAmbient_le_centralizer (q Gamma cp.a)))
  have hcommZaA : ⁅z Gamma cp.a, q Gamma cp.a⁆ = ⊥ :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hZaCentralA
  have hcomm : ⁅z Gamma cp.a, z Gamma cp.a'⁆ = ⊥ := by
    apply le_antisymm
    · exact (Subgroup.commutator_mono le_rfl hzEndA).trans
        (le_of_eq hcommZaA)
    · exact bot_le
  refine ⟨hcomm, ?_⟩
  let penult : Gamma.Vertex := cp.path ⟨cp.length - 1, by omega⟩
  have hZaPenult : z Gamma cp.a ≤ q Gamma penult := by
    apply critical_minimality Gamma cp
    have hp := path_distance_le Gamma cp 0 (cp.length - 1)
      (by omega) (by omega)
    have hstart : cp.path ⟨0, by omega⟩ = cp.a := by
      simpa using cp.path_start
    dsimp [penult]
    rw [← hstart]
    exact hp.trans_lt (by omega)
  obtain ⟨g, hga, hgfirst⟩ :=
    lemma_seven_five_endpoint_alignment h Gamma cp hcomm
  intro hAQ
  have hmap : q Gamma penult ≤ q Gamma cp.a' := by
    calc
      q Gamma penult = q Gamma (Gamma.act g cp.a) :=
        congrArg (q Gamma) hga.symm
      _ =
          (q Gamma cp.a).map (MulAut.conj g⁻¹).toMonoidHom := by
        exact q_act Gamma g cp.a
      _ ≤ (q Gamma cp.firstStep).map
          (MulAut.conj g⁻¹).toMonoidHom := Subgroup.map_mono hAQ
      _ = q Gamma (Gamma.act g cp.firstStep) :=
        (q_act Gamma g cp.firstStep).symm
      _ = q Gamma cp.a' := congrArg (q Gamma) hgfirst
  exact cp.critical.2 (hZaPenult.trans hmap)

public theorem core_intersection_not_normal_of_length_gt_one
    {G : Type u} [Group G] [Finite G]
    {S P1 P2 : Subgroup G}
    (h : SectionSevenHypotheses G S P1 P2)
    (Gamma : CosetGraphContext G S P1 P2) (cp : CriticalPath Gamma)
    (hlen : 1 < cp.length) :
    ¬ IsNormalIn (q Gamma cp.a ⊓ q Gamma cp.firstStep)
      (stabilizer Gamma cp.firstStep) := by
  let Ga := stabilizer Gamma cp.a
  let P := stabilizer Gamma cp.firstStep
  let A := q Gamma cp.a
  let Q := q Gamma cp.firstStep
  let Za := z Gamma cp.a
  let E := e Gamma cp.firstStep
  let R := twoCoreIn E
  let N := A ⊓ Q
  let V := v Gamma cp.firstStep
  intro hnormal
  obtain ⟨hcomm, hAnotQ⟩ :=
    longer_endpoint_comm_and_core_noncontainment h Gamma cp hlen hnormal
  have h75 := lemma_seven_five h Gamma cp hcomm
  have hQeq : Q = twoCoreAmbient P := by
    dsimp [Q, P, q, stabilizer]
    rw [Gamma.twoCoreAt_def]
    rfl
  have hEeq : E = twoResidualAmbient P := by
    dsimp [E, P, CosetGraphContext.e, stabilizer]
    rw [Gamma.twoResidualAt_def]
    rfl
  have hRleN : R ≤ N := by
    have hAS : A ≤ S := (local_cores_le_edge_sylow h Gamma cp).1
    have hAnormalS : (A.subgroupOf S).Normal := by
      rw [Subgroup.normal_subgroupOf_iff_le_normalizer hAS]
      exact (edge_sylow_data h Gamma cp).1.1.trans
        (stabilizer_le_normalizer_q Gamma cp.a)
    have hNnormal : ((A ⊓ twoCoreAmbient P).subgroupOf P).Normal := by
      rw [← hQeq]
      exact hnormal.2
    have hAnot : ¬ A ≤ twoCoreAmbient P := by
      rw [← hQeq]
      exact hAnotQ
    have htransfer := Stellmacher.SectionThree.residual_core_transfer S
      (sectionThreeHypotheses h) P
      ((pFamily_iff_pSet (⊤ : Subgroup G) S P).mp (edge_local_data h Gamma cp).2.1)
      A ⟨hAS, hAnormalS⟩ (edge_local_data h Gamma cp).2.2
      (edge_characteristic_data h Gamma cp).2 hNnormal hAnot
    change twoCoreAmbient E ≤ A ⊓ Q
    rw [hEeq, hQeq]
    exact htransfer
  have hVleN : V ≤ N :=
    v_le_core_intersection_of_length_gt_one h Gamma cp hlen hnormal
  have hQleP : Q ≤ P := by
    dsimp [Q, P, q]
    rw [Gamma.twoCoreAt_def]
    exact twoCoreIn_le _
  have hVleP : V ≤ P := hVleN.trans (inf_le_right.trans hQleP)
  have hVnormal : IsNormalIn V P := by
    refine ⟨hVleP, ?_⟩
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hVleP]
    exact stabilizer_le_normalizer_v Gamma cp.firstStep
  have hVN : ⁅V, N⁆ = ⊥ :=
    v_centralizes_core_intersection_of_normal h Gamma cp hnormal
  have hVR : ⁅V, R⁆ = ⊥ := by
    apply le_antisymm
    · exact (Subgroup.commutator_mono le_rfl hRleN).trans (le_of_eq hVN)
    · exact bot_le
  have hReq : R = E ⊓ Q := by
    dsimp [R, E, Q, CosetGraphContext.e, q]
    rw [Gamma.twoResidualAt_def, Gamma.twoCoreAt_def,
      residual_core_eq_inter_core]
  have hVQE : ⁅V, Q ⊓ E⁆ = ⊥ := by
    rw [inf_comm, ← hReq]
    exact hVR
  have hOmegaEq : omegaOneCenter S = omegaOneCenter P :=
    h75.next_center.1.symm.trans h75.next_center.2
  have hOmegaPComm : ⁅omegaOneCenter P, P⁆ = ⊥ := by
    apply Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
    exact (omegaOneCenter_le_centerAmbient P).trans
      (centerAmbient_le_centralizer P)
  have hEleP : E ≤ P := by
    dsimp [E, P, CosetGraphContext.e]
    rw [Gamma.twoResidualAt_def]
    exact twoResidualIn_le _
  have hOmegaComm : ⁅omegaOneCenter S, E⁆ = ⊥ := by
    rw [hOmegaEq]
    apply le_antisymm
    · exact (Subgroup.commutator_mono le_rfl hEleP).trans
        (le_of_eq hOmegaPComm)
    · exact bot_le
  have hVE : ⁅V, E⁆ = ⊥ := by
    have hVcore : V ≤ twoCoreAmbient P := by
      rw [← hQeq]
      exact hVleN.trans inf_le_right
    have hcentral : ⁅V, twoCoreAmbient P ⊓ twoResidualAmbient P⁆ = ⊥ := by
      rw [← hQeq, ← hEeq]
      exact hVQE
    have hOmega := Stellmacher.SectionThree.lemma_three_five_omega S
      (sectionThreeHypotheses h) P
      ((pFamily_iff_pSet (⊤ : Subgroup G) S P).mp (edge_local_data h Gamma cp).2.1)
      V ⟨hVnormal.1, hVcore, hVnormal.2⟩
      (edge_local_data h Gamma cp).2.2 hcentral
    have hOmega' : ⁅omegaOneCenter S, E⁆ ≠ ⊥ ∨ ⁅V, E⁆ = ⊥ := by
      simpa [P, E, CosetGraphContext.e, Gamma.twoResidualAt_def,
        twoResidualIn, omegaOneCenter, omegaOneCenterAmbient, stabilizer] using hOmega
    rcases hOmega' with hne | hzero
    · exact (hne hOmegaComm).elim
    · exact hzero
  have hZaV : Za ≤ V := (lemma_seven_four h Gamma cp).first_containment.1
  have hZaE : ⁅Za, E⁆ = ⊥ := by
    apply le_antisymm
    · exact (Subgroup.commutator_mono hZaV le_rfl).trans (le_of_eq hVE)
    · exact bot_le
  have hSleGa : S ≤ Ga := (edge_sylow_data h Gamma cp).1.1
  have hSleP : S ≤ P := (edge_sylow_data h Gamma cp).2.1
  have hSnormZa : S ≤ Subgroup.normalizer (Za : Set G) :=
    hSleGa.trans (stabilizer_le_normalizer_z Gamma cp.a)
  have hEnormZa : E ≤ Subgroup.normalizer (Za : Set G) := by
    exact (Subgroup.commutator_eq_bot_iff_le_centralizer.mp
      (by rw [Subgroup.commutator_comm]; exact hZaE)).trans
        (Subgroup.centralizer_le_normalizer (Za : Set G))
  have hEP : E ⊔ S = P := by
    dsimp [E, P, CosetGraphContext.e]
    rw [Gamma.twoResidualAt_def]
    exact twoResidualIn_sup_sylow (edge_sylow_data h Gamma cp).2
  have hPnormZa : P ≤ Subgroup.normalizer (Za : Set G) := by
    rw [← hEP]
    exact sup_le hEnormZa hSnormZa
  have hGaP : Ga ⊔ P = ⊤ := by
    rcases cp.edge_stabilizers_are_P with hedge | hedge
    · simpa [Ga, P, hedge.1, hedge.2] using h.generated
    · simpa [Ga, P, hedge.1, hedge.2, sup_comm] using h.generated
  have hGnormZa : (⊤ : Subgroup G) ≤
      Subgroup.normalizer (Za : Set G) := by
    rw [← hGaP]
    exact sup_le (stabilizer_le_normalizer_z Gamma cp.a) hPnormZa
  have hZaNormal : Za.Normal :=
    Subgroup.normalizer_eq_top_iff.mp (top_unique hGnormZa)
  have haMem : cp.firstStep ∈ neighborhood Gamma cp.a :=
    (mem_neighborhood_iff_adjacent Gamma).2 cp.firstStep_adj
  have hZaElem : IsElementaryAbelian 2 Za :=
    z_isElementaryAbelian_of_neighbor h Gamma haMem
  have hZaP : IsPGroup 2 Za := IsElementaryAbelian.isPGroup 2 Za
  have hZaCore : Za ≤ pCore 2 G := le_sSup ⟨hZaNormal, hZaP⟩
  have hZaBot : Za = ⊥ := le_antisymm (hZaCore.trans (le_of_eq h.twoCore_eq_bot)) bot_le
  apply cp.critical.2
  change z Gamma cp.a ≤ q Gamma cp.a'
  change z Gamma cp.a = ⊥ at hZaBot
  rw [hZaBot]
  exact bot_le

public theorem elementaryAbelianMaxJ_not_le_pCore_of_length_gt_one
    {G : Type u} [Group G] [Finite G]
    {S P1 P2 : Subgroup G}
    (h : SectionSevenHypotheses G S P1 P2)
    (Gamma : CosetGraphContext G S P1 P2) (cp : CriticalPath Gamma)
    (hlen : 1 < cp.length)
    (hnormal : IsNormalIn (q Gamma cp.a ⊓ q Gamma cp.firstStep)
      (stabilizer Gamma cp.firstStep))
    (T : Sylow 2 (stabilizer Gamma cp.firstStep)) :
    ¬ elementaryAbelianMaxJ (T : Subgroup (stabilizer Gamma cp.firstStep)) ≤
      pCore 2 (stabilizer Gamma cp.firstStep) := by
  exfalso
  exact core_intersection_not_normal_of_length_gt_one h Gamma cp hlen hnormal

end Stellmacher.SectionsFiveToSeven.SevenSix
