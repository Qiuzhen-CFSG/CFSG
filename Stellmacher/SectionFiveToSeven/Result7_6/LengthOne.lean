module

public import Stellmacher.SectionFiveToSeven.Result7_6.GraphFacts
public import Stellmacher.SectionFiveToSeven.Result7_6.LocalFacts
public import Theory.GroupTheory.PGroup.CharacteristicTwoNormalClosure

/-!
# Stellmacher (7.6): non-normality for a critical edge

When the critical path has length one, its initial center is not contained in
the next 2-core. Lemma (3.4) forces the next residual into its local normal
closure. If the core intersection were normal, the centrality of the initial
center and the characteristic-two normal-closure theorem would make that
closure a 2-group, contradicting this residual containment. This proves the
length-one branch of (7.6)(a).

Source: B. Stellmacher, Journal of Algebra 190 (1997), Lemma (7.6),
pp. 35–36; `refs/latex/stellmacher-n-group.tex`.
-/

open scoped Pointwise

namespace Stellmacher.SectionsFiveToSeven.SevenSix

open CosetGraphContext

universe u v

public theorem core_intersection_not_normal_of_length_one
    {G : Type u} [Group G] [Finite G]
    {S P1 P2 : Subgroup G}
    (h : SectionSevenHypotheses G S P1 P2)
    (Gamma : CosetGraphContext G S P1 P2) (cp : CriticalPath Gamma)
    (hlen : cp.length = 1)
    (hZaNormalS : ((z Gamma cp.a).subgroupOf S).Normal) :
    ¬ IsNormalIn (q Gamma cp.a ⊓ q Gamma cp.firstStep)
      (stabilizer Gamma cp.firstStep) := by
  let A := q Gamma cp.a
  let Q := q Gamma cp.firstStep
  let Za := z Gamma cp.a
  let P := stabilizer Gamma cp.firstStep
  let E := e Gamma cp.firstStep
  let N := A ⊓ Q
  have ha_mem : cp.firstStep ∈ neighborhood Gamma cp.a :=
    (mem_neighborhood_iff_adjacent Gamma).2 cp.firstStep_adj
  have hZaA : Za ≤ A :=
    ((lemma_seven_three h Gamma).center_core cp.a cp.firstStep ha_mem).trans
      ((omegaOneCenter_le_centerAmbient A).trans
        (Subgroup.map_subtype_le (Subgroup.center A)))
  have hZaCentralA : Za ≤ Subgroup.centralizer (A : Set G) :=
    ((lemma_seven_three h Gamma).center_core cp.a cp.firstStep ha_mem).trans
      ((omegaOneCenter_le_centerAmbient A).trans
        (centerAmbient_le_centralizer A))
  have hcores := local_cores_le_edge_sylow h Gamma cp
  have hA_le_S : A ≤ S := hcores.1
  have hQ_le_S : Q ≤ S := hcores.2
  have hS_le_Ga : S ≤ stabilizer Gamma cp.a :=
    (edge_sylow_data h Gamma cp).1.1
  have hS_le_P : S ≤ P := (edge_sylow_data h Gamma cp).2.1
  have hZaS : Za ≤ S := hZaA.trans hA_le_S
  have hZaP : Za ≤ P := hZaS.trans hS_le_P
  have hQleP : Q ≤ P := by
    dsimp [Q, P, q]
    rw [Gamma.twoCoreAt_def]
    exact twoCoreIn_le _
  have hA_norm_S : S ≤ Subgroup.normalizer (A : Set G) :=
    hS_le_Ga.trans (stabilizer_le_normalizer_q Gamma cp.a)
  have hQ_norm_S : S ≤ Subgroup.normalizer (Q : Set G) :=
    hS_le_P.trans (stabilizer_le_normalizer_q Gamma cp.firstStep)
  have hQZa : ⁅Q, Za⁆ ≤ N := by
    apply le_inf
    · exact (Subgroup.commutator_mono le_rfl hZaA).trans
        (Subgroup.le_normalizer_iff_commutator_le_right.mp
          (hQ_le_S.trans hA_norm_S))
    · rw [Subgroup.commutator_comm]
      exact Subgroup.le_normalizer_iff_commutator_le_right.mp
        (hZaS.trans hQ_norm_S)
  have hNZa : ⁅N, Za⁆ = ⊥ := by
    apply le_bot_iff.mp
    rw [Subgroup.commutator_comm]
    exact (Subgroup.commutator_mono le_rfl inf_le_left).trans
      (le_of_eq (Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
        hZaCentralA))
  have hfirst_eq_end : cp.firstStep = cp.a' := by
    calc
      cp.firstStep = cp.path ⟨1, by omega⟩ := cp.path_first.symm
      _ = cp.path ⟨cp.length, Nat.lt_succ_self _⟩ := by
        congr 1
        apply Fin.ext
        simp [hlen]
      _ = cp.a' := cp.path_end
  have hZaNotQ : ¬ Za ≤ Q := by
    dsimp [Za, Q, z, q]
    rw [hfirst_eq_end]
    exact cp.critical.2
  have h34 := Stellmacher.SectionThree.lemma_three_four S
    (sectionThreeHypotheses h) P
    ((pFamily_iff_pSet (⊤ : Subgroup G) S P).mp
      (edge_local_data h Gamma cp).2.1)
    Za ⟨hZaS, hZaNormalS⟩ (edge_local_data h Gamma cp).2.2
  have hcomm : ⁅E, Za⁆ = E := by
    rcases h34 with hle | hcomm
    · apply (hZaNotQ ?_).elim
      dsimp [Q, P, q]
      rw [Gamma.twoCoreAt_def]
      exact hle
    · dsimp [E, CosetGraphContext.e]
      rw [Gamma.twoResidualAt_def]
      simpa [P, stabilizer, twoResidualIn] using hcomm
  have hEclosure : E ≤ conjugateClosure Za P := by
    rw [← hcomm]
    exact commutator_le_conjugateClosure E Za P (by
      dsimp [E, P, CosetGraphContext.e]
      rw [Gamma.twoResidualAt_def]
      exact twoResidualIn_le _)
  intro hnormal
  let Np : Subgroup P := N.subgroupOf P
  let Zp : Subgroup P := Za.subgroupOf P
  let W : Subgroup P := Subgroup.normalClosure (Zp : Set P)
  have hNleP : N ≤ P := inf_le_right.trans hQleP
  have hNmap : Np.map P.subtype = N :=
    Subgroup.map_subgroupOf_eq_of_le hNleP
  have hZmap : Zp.map P.subtype = Za :=
    Subgroup.map_subgroupOf_eq_of_le hZaP
  have hQmap : (pCore 2 P).map P.subtype = Q := by
    dsimp [Q, P, q]
    rw [Gamma.twoCoreAt_def]
    rfl
  have hQZp : ⁅pCore 2 P, Zp⁆ ≤ Np := by
    apply Subgroup.map_subtype_le_map_subtype.mp
    rw [Subgroup.map_commutator, hQmap, hZmap, hNmap]
    exact hQZa
  have hNZp : ⁅Np, Zp⁆ = ⊥ := by
    apply Subgroup.map_injective (f := P.subtype) P.subtype_injective
    rw [Subgroup.map_commutator, hNmap, hZmap, Subgroup.map_bot]
    exact hNZa
  have hZelem : IsElementaryAbelian 2 Za :=
    z_isElementaryAbelian_of_neighbor h Gamma ha_mem
  let _ : IsElementaryAbelian 2 Za := hZelem
  have hZpelem : IsElementaryAbelian 2 Zp := by
    dsimp [Zp]
    exact IsElementaryAbelian.subgroupOf hZaP
  have hWp : IsPGroup 2 W := by
    dsimp [W]
    exact normalClosure_isPGroup_of_characteristicTwo Np Zp
      (edge_characteristic_data h Gamma cp).2 hnormal.2 hQZp hNZp hZpelem
  let E0 : Subgroup P := twoResidualSubgroup P
  have hE0leW : E0 ≤ W := by
    have hmap := hEclosure.trans
      (conjugateClosure_le_map_normalClosure Za P hZaP)
    have hE0map : E0.map P.subtype = E := by
      dsimp [E0, E, CosetGraphContext.e]
      rw [Gamma.twoResidualAt_def]
      rfl
    have hmap' : E0.map P.subtype ≤ W.map P.subtype := by
      rw [hE0map]
      exact hmap
    exact Subgroup.map_subtype_le_map_subtype.mp hmap'
  have hE0p : IsPGroup 2 E0 :=
    (hWp.to_subgroup (E0.subgroupOf W)).of_equiv
      (Subgroup.subgroupOfEquivOfLe hE0leW)
  have hE0normal : E0.Normal := by
    dsimp [E0]
    unfold twoResidualSubgroup
    rw [sInf_eq_iInf]
    exact Subgroup.normal_iInf_normal (fun K ↦
      Subgroup.normal_iInf_normal (fun hK ↦ hK.1))
  have hE0leCore : E0 ≤ pCore 2 P := le_sSup ⟨hE0normal, hE0p⟩
  have hEleQ : E ≤ Q := by
    have hmap := Subgroup.map_mono (f := P.subtype) hE0leCore
    dsimp [E, Q, CosetGraphContext.e, q]
    rw [Gamma.twoResidualAt_def, Gamma.twoCoreAt_def]
    change twoResidualAmbient P ≤ twoCoreIn P
    simpa [E0, twoResidualAmbient, twoCoreIn] using hmap
  have hEP : E ⊔ S = P := by
    dsimp [E, P, CosetGraphContext.e]
    rw [Gamma.twoResidualAt_def]
    exact twoResidualIn_sup_sylow (edge_sylow_data h Gamma cp).2
  have hPleS : P ≤ S := by
    rw [← hEP]
    exact sup_le (hEleQ.trans hQ_le_S) le_rfl
  have hPeqS : P = S := le_antisymm hPleS hS_le_P
  have hSp : IsPGroup 2 S := by
    obtain ⟨_, T, hTmap⟩ := (edge_sylow_data h Gamma cp).2
    rw [← hTmap]
    exact T.isPGroup'.map P.subtype
  have hPp : IsPGroup 2 P := by
    rw [hPeqS]
    exact hSp
  have hPleQ : P ≤ Q := by
    dsimp [Q, q]
    rw [Gamma.twoCoreAt_def]
    intro x hx
    refine ⟨⟨x, hx⟩, ?_, rfl⟩
    have htop : (⊤ : Subgroup P) ≤ pCore 2 P :=
      le_sSup ⟨inferInstance, hPp.to_subgroup ⊤⟩
    exact htop trivial
  have hSeqQ : S = Q := le_antisymm (hS_le_P.trans hPleQ) hQ_le_S
  apply (edge_local_data h Gamma cp).2.1.1.2.2.2
  have hcore : Q = twoCoreIn P := by
    dsimp [Q, P, q, stabilizer]
    rw [Gamma.twoCoreAt_def]
  rw [← hcore]
  exact hSeqQ

end Stellmacher.SectionsFiveToSeven.SevenSix

