module

public import Stellmacher.SectionFiveToSeven.Result7_6
public import Theory.GroupTheory.PGroup.SubnormalCore
public import Stellmacher.SectionThree.ResidualKernel

/-!
# Stellmacher (7.7)(c): the longer endpoint

For a critical path of length greater than one, the terminal residual cannot
lie in the centralizer of `Ω₁(Z(S))` when the next residual is subnormal
in that centralizer. Consequently the terminal and next centers differ.

Residual transitivity sends the initial neighbor to the second path vertex.
Since the initial center lies in the next core, its image is unchanged
modulo the next residual 2-core. Critical minimality and subnormal core
monotonicity therefore put it in `(C ∩ Q_{a′}) O₂(C)`. Assuming the
terminal residual lies in `C`, a product decomposition shows its commutator
with the initial center lies in `Q_{a′}`. The residual-kernel criterion
then contradicts criticality. Finally equality of terminal and next centers
would make the endpoint centers commute; the endpoint-center conclusion
of (7.5) would put the terminal residual in `C`, again a contradiction.

Source: B. Stellmacher, Journal of Algebra 190 (1997), (7.7)(c), p.36;
`refs/latex/stellmacher-n-group.tex`.
-/

open scoped Pointwise commutatorElement

namespace Stellmacher.SectionsFiveToSeven

open CosetGraphContext SevenSix

universe u v

private theorem residual_moves_initial_to_neighbor
    {G : Type u} [Group G] [Finite G]
    {S P1 P2 : Subgroup G}
    (h : SectionSevenHypotheses G S P1 P2)
    (Gamma : CosetGraphContext G S P1 P2) (cp : CriticalPath Gamma)
    (m : Gamma.Vertex) (hm : m ∈ neighborhood Gamma cp.firstStep) :
    ∃ g : e Gamma cp.firstStep, Gamma.act (g : G) cp.a = m := by
  let P := stabilizer Gamma cp.firstStep
  let E := e Gamma cp.firstStep
  have hEP : E ≤ P := by
    dsimp [E, P, CosetGraphContext.e, stabilizer]
    rw [Gamma.twoResidualAt_def]
    exact twoResidualIn_le _
  have hSP : S ≤ P := (edge_sylow_data h Gamma cp).2.1
  have hES : E ⊔ S = P := by
    dsimp [E, P, CosetGraphContext.e, stabilizer]
    rw [Gamma.twoResidualAt_def]
    exact twoResidualIn_sup_sylow (edge_sylow_data h Gamma cp).2
  have hEnormal : (E.subgroupOf P).Normal := by
    dsimp [E, P, CosetGraphContext.e, stabilizer]
    rw [Gamma.twoResidualAt_def]
    exact twoResidualIn_normal _
  let _ : (E.subgroupOf P).Normal := hEnormal
  have hsup : S.subgroupOf P ⊔ E.subgroupOf P = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hSP hEP, sup_comm, hES, Subgroup.subgroupOf_self]
  have ha : cp.a ∈ neighborhood Gamma cp.firstStep :=
    (mem_neighborhood_iff_adjacent Gamma).2 (Gamma.adjacent_symm cp.firstStep_adj)
  obtain ⟨g, hg⟩ := (lemma_seven_one h Gamma).local_transitivity cp.firstStep ha hm
  obtain ⟨s, hs, e, he, hse⟩ := Subgroup.mem_sup_of_normal_right.mp
    (show g ∈ S.subgroupOf P ⊔ E.subgroupOf P by rw [hsup]; trivial)
  have hsfix : Gamma.act (s : G) cp.a = cp.a := by
    exact (Set.ext_iff.mp (Gamma.stabilizer_def cp.a) (s : G)).mp
      ((edge_sylow_data h Gamma cp).1.1 hs)
  refine ⟨⟨(e : G), he⟩, ?_⟩
  have hseG : (s : G) * (e : G) = (g : G) := congrArg Subtype.val hse
  rw [← hseG, Gamma.act_mul, hsfix] at hg
  exact hg

private theorem initial_center_le_neighbor_join_residual_core
    {G : Type u} [Group G] [Finite G]
    {S P1 P2 : Subgroup G}
    (h : SectionSevenHypotheses G S P1 P2)
    (Gamma : CosetGraphContext G S P1 P2) (cp : CriticalPath Gamma)
    (hlen : 1 < cp.length)
    (m : Gamma.Vertex) (hm : m ∈ neighborhood Gamma cp.firstStep) :
    z Gamma cp.a ≤ z Gamma m ⊔ twoCoreIn (e Gamma cp.firstStep) := by
  obtain ⟨g, hg⟩ := residual_moves_initial_to_neighbor h Gamma cp m hm
  have hZaQ : z Gamma cp.a ≤ q Gamma cp.firstStep :=
    critical_minimality Gamma cp (by
      rw [(adjacent_iff_distance_eq_one Gamma).mp cp.firstStep_adj]
      exact hlen)
  have hQR : ⁅q Gamma cp.firstStep, e Gamma cp.firstStep⁆ ≤
      twoCoreIn (e Gamma cp.firstStep) := by
    rw [Subgroup.commutator_comm]
    dsimp [q, CosetGraphContext.e]
    rw [Gamma.twoCoreAt_def, Gamma.twoResidualAt_def]
    exact residual_commutator_core_le _
  intro x hx
  have hzmap : (g : G)⁻¹ * x * (g : G) ∈ z Gamma m := by
    rw [← hg, z_act]
    simpa [MulAut.conj_apply] using
      Subgroup.mem_map_of_mem (MulAut.conj (g : G)⁻¹).toMonoidHom hx
  have hcomm : ⁅x, (g : G)⁻¹⁆ ∈ twoCoreIn (e Gamma cp.firstStep) :=
    hQR (Subgroup.commutator_mem_commutator (hZaQ hx)
      ((e Gamma cp.firstStep).inv_mem g.2))
  have hmprod := (z Gamma m ⊔ twoCoreIn (e Gamma cp.firstStep)).mul_mem
    ((le_sup_right : twoCoreIn (e Gamma cp.firstStep) ≤ _) hcomm)
    ((le_sup_left : z Gamma m ≤ _) hzmap)
  simpa [commutatorElement_def, mul_assoc] using hmprod

private theorem commutator_le_core_of_le_sup_core
    {G : Type u} [Group G] [Finite G]
    (D U E P C : Subgroup G)
    (hDP : D ≤ P) (hUQ : U ≤ twoCoreIn P) (hUC : U ≤ C)
    (hEP : E ≤ P) (hEC : E ≤ C) (hEnormal : (E.subgroupOf P).Normal)
    (hDsup : D ≤ U ⊔ twoCoreIn C) :
    ⁅D, E⁆ ≤ twoCoreIn P := by
  let R := twoCoreIn C
  let Q := twoCoreIn P
  have hCnormR : C ≤ Subgroup.normalizer R :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (twoCoreIn_le C)).mp
      (twoCoreIn_normal C)
  have hPnormE : P ≤ Subgroup.normalizer E :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hEP).mp hEnormal
  have hPnormQ : P ≤ Subgroup.normalizer Q :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (twoCoreIn_le P)).mp
      (twoCoreIn_normal P)
  have hUP : U ≤ P := hUQ.trans (twoCoreIn_le P)
  let N := R ⊓ E
  have hNnormalE : (N.subgroupOf E).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_right).mpr
      ((le_inf (hEC.trans hCnormR) E.le_normalizer).trans
        Subgroup.inf_normalizer_le_normalizer_inf)
  have hNp : IsPGroup 2 N :=
    ((pCore_isPGroup (p := 2) (G := C)).map C.subtype).to_le inf_le_left
  have hNcoreE : N ≤ twoCoreIn E :=
    isPGroup_le_pCoreAmbient_of_isSubnormalIn E N 2 inf_le_right
      hNnormalE.isSubnormal hNp
  have hcoreEQ : twoCoreIn E ≤ Q :=
    pCoreAmbient_mono_of_isSubnormalIn E P 2 hEP hEnormal.isSubnormal
  apply Subgroup.commutator_le.mpr
  intro d hd e he
  have hdsup : d ∈ U ⊔ R := hDsup hd
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right U R
    (hUC.trans hCnormR)] at hdsup
  obtain ⟨u, hu, r, hr, hur⟩ := hdsup
  have hrP : r ∈ P := by
    have heq : r = u⁻¹ * d := by rw [← hur]; group
    rw [heq]
    exact P.mul_mem (P.inv_mem (hUP hu)) (hDP hd)
  have hreR : ⁅r, e⁆ ∈ R :=
    (Subgroup.le_normalizer_iff_commutator_le_left.mp (hEC.trans hCnormR))
      (Subgroup.commutator_mem_commutator hr he)
  have hreE : ⁅r, e⁆ ∈ E :=
    (Subgroup.le_normalizer_iff_commutator_le_right.mp hPnormE)
      (Subgroup.commutator_mem_commutator hrP he)
  have hreQ : ⁅r, e⁆ ∈ Q := hcoreEQ (hNcoreE ⟨hreR, hreE⟩)
  have hueQ : ⁅u, e⁆ ∈ Q :=
    (Subgroup.le_normalizer_iff_commutator_le_left.mp (hEP.trans hPnormQ))
      (Subgroup.commutator_mem_commutator (hUQ hu) he)
  rw [← hur, commutatorElement_mul_left_eq_conj_mul]
  exact Q.mul_mem
    ((Subgroup.le_normalizer_iff.mp hPnormQ) u (hUP hu) _ hreQ) hueQ

private theorem initial_center_le_endpoint_core_sup_centralizer_core
    {G : Type u} [Group G] [Finite G]
    {S P1 P2 : Subgroup G}
    (h : SectionSevenHypotheses G S P1 P2)
    (Gamma : CosetGraphContext G S P1 P2) (cp : CriticalPath Gamma)
    (C : Subgroup G)
    (hC : C = Subgroup.centralizer (omegaOneCenter S : Set G))
    (hsubnormal : SubnormalIn (e Gamma cp.firstStep) C)
    (hlen : 1 < cp.length) :
    z Gamma cp.a ≤ (C ⊓ q Gamma cp.a') ⊔ twoCoreIn C := by
  let second : Gamma.Vertex := cp.path ⟨2, by omega⟩
  have hsecondAdj : Gamma.adjacent cp.firstStep second := by
    have hp := cp.path_adj ⟨1, by omega⟩
    simpa [second, cp.path_first] using hp
  have hm : second ∈ neighborhood Gamma cp.firstStep :=
    (mem_neighborhood_iff_adjacent Gamma).2 hsecondAdj
  have hZsecondQ : z Gamma second ≤ q Gamma cp.a' := by
    apply critical_minimality Gamma cp
    have hd := path_distance_le Gamma cp 2 cp.length (by omega) le_rfl
    rw [cp.path_end] at hd
    exact hd.trans_lt (by omega)
  have hZaS : z Gamma cp.a ≤ S :=
    ((lemma_seven_three h Gamma).center_core cp.a cp.firstStep
      ((mem_neighborhood_iff_adjacent Gamma).2 cp.firstStep_adj)).trans
      ((omegaOneCenter_le_centerAmbient (q Gamma cp.a)).trans
        ((Subgroup.map_subtype_le _).trans (local_cores_le_edge_sylow h Gamma cp).1))
  have hSC : S ≤ C := by
    rw [hC, ← Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.commutator_comm]
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
      ((omegaOneCenter_le_centerAmbient S).trans (centerAmbient_le_centralizer S))
  have hZsecondC : z Gamma second ≤ C := by
    obtain ⟨g, hg⟩ := residual_moves_initial_to_neighbor h Gamma cp second hm
    rw [← hg, z_act]
    rintro x ⟨y, hy, rfl⟩
    change (g : G)⁻¹ * y * ((g : G)⁻¹)⁻¹ ∈ C
    exact C.mul_mem (C.mul_mem (C.inv_mem (hsubnormal.1 g.2)) (hSC (hZaS hy)))
      (C.inv_mem (C.inv_mem (hsubnormal.1 g.2)))
  exact (initial_center_le_neighbor_join_residual_core h Gamma cp hlen second hm).trans
    (sup_le_sup (le_inf hZsecondC hZsecondQ)
      (pCoreAmbient_mono_of_isSubnormalIn (e Gamma cp.firstStep) C 2
        hsubnormal.1 hsubnormal.2))

private theorem initial_z_le_S
    {G : Type u} [Group G] [Finite G]
    {S P1 P2 : Subgroup G}
    (h : SectionSevenHypotheses G S P1 P2)
    (Gamma : CosetGraphContext G S P1 P2) (cp : CriticalPath Gamma) :
    z Gamma cp.a ≤ S :=
  ((lemma_seven_three h Gamma).center_core cp.a cp.firstStep
    ((mem_neighborhood_iff_adjacent Gamma).2 cp.firstStep_adj)).trans
    ((omegaOneCenter_le_centerAmbient (q Gamma cp.a)).trans
      ((Subgroup.map_subtype_le _).trans (local_cores_le_edge_sylow h Gamma cp).1))

public theorem lemma_seven_seven_longer_endpoint
    {G : Type u} [Group G] [Finite G]
    {S P1 P2 : Subgroup G}
    (h : SectionSevenHypotheses G S P1 P2)
    (Gamma : CosetGraphContext G S P1 P2) (cp : CriticalPath Gamma)
    (C : Subgroup G)
    (hC : C = Subgroup.centralizer (omegaOneCenter S : Set G))
    (hsubnormal : SubnormalIn (e Gamma cp.firstStep) C)
    (hlen : 1 < cp.length) :
    ¬ e Gamma cp.a' ≤ C ∧ z Gamma cp.a' ≠ z Gamma cp.firstStep := by
  have hnot : ¬ e Gamma cp.a' ≤ C := by
    intro hEC
    let P := stabilizer Gamma cp.a'
    let E := e Gamma cp.a'
    have hEP : E ≤ P := by
      dsimp [E, P, CosetGraphContext.e, stabilizer]
      rw [Gamma.twoResidualAt_def]
      exact twoResidualIn_le _
    have hEnormal : (E.subgroupOf P).Normal := by
      dsimp [E, P, CosetGraphContext.e, stabilizer]
      rw [Gamma.twoResidualAt_def]
      exact twoResidualIn_normal _
    have hZaP : z Gamma cp.a ≤ P :=
      (lemma_seven_four h Gamma cp).first_containment.1.trans
        (lemma_seven_four h Gamma cp).first_containment.2
    have hQeq : q Gamma cp.a' = twoCoreIn P := by
      dsimp [P, q, stabilizer]
      rw [Gamma.twoCoreAt_def]
    have hUQ : C ⊓ q Gamma cp.a' ≤ twoCoreIn P := by
      rw [← hQeq]
      exact inf_le_right
    have hcomm := commutator_le_core_of_le_sup_core (z Gamma cp.a)
      (C ⊓ q Gamma cp.a') E P C hZaP hUQ inf_le_left hEP hEC hEnormal
      (initial_center_le_endpoint_core_sup_centralizer_core h Gamma cp C hC hsubnormal hlen)
    have hEeq : E = twoResidualAmbient P := by
      dsimp [E, P, CosetGraphContext.e, stabilizer]
      rw [Gamma.twoResidualAt_def]
      rfl
    have hZaTwo : IsPGroup 2 (z Gamma cp.a) := by
      let _ : IsElementaryAbelian 2 (z Gamma cp.a) := z_isElementaryAbelian_of_neighbor h Gamma
        ((mem_neighborhood_iff_adjacent Gamma).2 cp.firstStep_adj)
      exact IsElementaryAbelian.isPGroup 2 (z Gamma cp.a)
    have hZaQ := Stellmacher.SectionThree.two_subgroup_le_core_of_commutator_residual_le_core
      (z Gamma cp.a) P hZaP hZaTwo (by rw [← hEeq]; exact hcomm)
    apply cp.critical.2
    change z Gamma cp.a ≤ q Gamma cp.a'
    rw [hQeq]
    exact hZaQ
  refine ⟨hnot, ?_⟩
  intro hzeq
  have hOmegaS : omegaOneCenter S ≤ S :=
    (omegaOneCenter_le_centerAmbient S).trans (Subgroup.map_subtype_le _)
  have hSOmega : ⁅S, omegaOneCenter S⁆ = ⊥ := by
    rw [Subgroup.commutator_comm]
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
      ((omegaOneCenter_le_centerAmbient S).trans (centerAmbient_le_centralizer S))
  have hSC : S ≤ C := by
    rw [hC]
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp hSOmega
  let Pnext := stabilizer Gamma cp.firstStep
  have hPnextC : Pnext ≤ C := by
    have hEP : e Gamma cp.firstStep ⊔ S = Pnext := by
      dsimp [Pnext, CosetGraphContext.e, stabilizer]
      rw [Gamma.twoResidualAt_def]
      exact twoResidualIn_sup_sylow (edge_sylow_data h Gamma cp).2
    rw [← hEP]
    exact sup_le hsubnormal.1 hSC
  have hOmegaPnext : omegaOneCenter S ≤ Pnext :=
    hOmegaS.trans (edge_sylow_data h Gamma cp).2.1
  have hOmegaNormal : NormalIn (omegaOneCenter S) Pnext := by
    refine ⟨hOmegaPnext, ?_⟩
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hOmegaPnext]
    exact hPnextC.trans (by rw [hC]; exact Subgroup.centralizer_le_normalizer _)
  have hNextOmega : z Gamma cp.firstStep = omegaOneCenter S :=
    z_eq_omega_sylow_of_normal Gamma cp.firstStep (edge_sylow_data h Gamma cp).2 hOmegaNormal
  have hcomm : ⁅z Gamma cp.a, z Gamma cp.a'⁆ = ⊥ := by
    rw [hzeq, hNextOmega]
    exact le_bot_iff.mp ((Subgroup.commutator_mono (initial_z_le_S h Gamma cp) le_rfl).trans
      (le_of_eq hSOmega))
  have hEndOmega := lemma_seven_five_endpoint_center h Gamma cp hcomm
  have hEndCentral : stabilizer Gamma cp.a' ≤
      Subgroup.centralizer (z Gamma cp.a' : Set G) := by
    rw [hEndOmega, ← Subgroup.commutator_eq_bot_iff_le_centralizer,
      Subgroup.commutator_comm]
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
      ((omegaOneCenter_le_centerAmbient _).trans (centerAmbient_le_centralizer _))
  apply hnot
  have hEP : e Gamma cp.a' ≤ stabilizer Gamma cp.a' := by
    dsimp [CosetGraphContext.e, stabilizer]
    rw [Gamma.twoResidualAt_def]
    exact twoResidualIn_le _
  have hCeq : C = Subgroup.centralizer (z Gamma cp.a' : Set G) := by
    rw [hC, hzeq, hNextOmega]
  rw [hCeq]
  exact hEP.trans hEndCentral

end Stellmacher.SectionsFiveToSeven

