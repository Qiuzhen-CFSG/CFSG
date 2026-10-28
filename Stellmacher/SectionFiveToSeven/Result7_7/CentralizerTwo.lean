module

public import Stellmacher.SectionFiveToSeven.Result7_7.CentralizerCommutator
public import Stellmacher.SectionFiveToSeven.ResidualTwoExtension

/-!
# Stellmacher (7.7)(b): the neighbor-center centralizer

Under the subnormal-centralizer assumptions of (7.7), the centralizer of
the next neighbor-center join is a 2-group.

Let `E=O²(C_G(V_{a+1}))`. Part (a) makes `E_a` normalize `E Q_a`.
Residual stability under a normal 2-extension identifies its characteristic
residual with `E`, so `E_a` normalizes `E`. The next stabilizer does
also, because it normalizes `V_{a+1}`. Together these groups generate the
ambient group. Thus `E` is globally normal and lies in `C`. A nontrivial
normal subgroup contained in a characteristic-two subgroup has a nontrivial
2-core; the trivial ambient 2-core therefore forces `E=1`. The residual
quotient theorem now proves that the entire centralizer is a 2-group.

Source: B. Stellmacher, Journal of Algebra 190 (1997), (7.7)(b), p.36;
`refs/latex/stellmacher-n-group.tex`.
-/

open scoped Pointwise commutatorElement
open BenderSuzuki.External

namespace Stellmacher.SectionsFiveToSeven

open CosetGraphContext SevenSix

universe u v

private theorem normalizer_le_normalizer_residual
    {G : Type u} [Group G] [Finite G] (K : Subgroup G) :
    Subgroup.normalizer K ≤ Subgroup.normalizer (twoResidualIn K : Set G) := by
  intro g hg
  apply Subgroup.mem_normalizer_iff_map_conj_eq.mpr
  exact map_twoResidualAmbient_of_subgroup_image K (MulAut.conj g).toMonoidHom K
    (Subgroup.mem_normalizer_iff_map_conj_eq.mp hg)

private theorem normal_subgroup_le_characteristicTwo_eq_bot
    {G : Type u} [Group G] [Finite G]
    (E C : Subgroup G) (hE : E.Normal) (hEC : E ≤ C)
    (hchar : Stellmacher.IsCharacteristicTwoType C)
    (hcore : pCore 2 G = ⊥) : E = ⊥ := by
  let _ : E.Normal := hE
  let Q := twoCoreIn C
  have hEQnormal : (twoCoreIn E).Normal :=
    ConjAct.normal_of_characteristic_of_normal
  have hEQp : IsPGroup 2 (twoCoreIn E) :=
    (pCore_isPGroup (p := 2) (G := E)).map E.subtype
  have hEQbot : twoCoreIn E = ⊥ := by
    apply le_bot_iff.mp
    rw [← hcore]
    exact le_sSup ⟨hEQnormal, hEQp⟩
  have hCnormQ : C ≤ Subgroup.normalizer Q :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (twoCoreIn_le C)).mp
      (twoCoreIn_normal C)
  let N := ⁅E, Q⁆
  have hNE : N ≤ E := Subgroup.commutator_le_left E Q
  have hNQ : N ≤ Q :=
    Subgroup.le_normalizer_iff_commutator_le_right.mp (hEC.trans hCnormQ)
  have hNnormalE : (N.subgroupOf E).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNE).mpr
      (Subgroup.normalizer_commutator_ge_left E Q)
  have hNp : IsPGroup 2 N :=
    ((pCore_isPGroup (p := 2) (G := C)).map C.subtype).to_le hNQ
  have hNcore : N ≤ twoCoreIn E :=
    isPGroup_le_pCoreAmbient_of_isSubnormalIn E N 2 hNE
      hNnormalE.isSubnormal hNp
  have hcomm : ⁅E, Q⁆ = ⊥ := le_bot_iff.mp (hNcore.trans (le_of_eq hEQbot))
  have hEQ : E ≤ Q := by
    intro x hx
    let xC : C := ⟨x, hEC hx⟩
    have hxCent : xC ∈ Subgroup.centralizer (pCore 2 C : Set C) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      apply Subtype.ext
      exact (Subgroup.mem_centralizer_iff.mp
        ((Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm) hx)) y
          (Subgroup.mem_map_of_mem C.subtype hy)
    exact Subgroup.mem_map_of_mem C.subtype (hchar hxCent)
  have hEp : IsPGroup 2 E :=
    ((pCore_isPGroup (p := 2) (G := C)).map C.subtype).to_le hEQ
  have hEcore : E ≤ pCore 2 G := le_sSup ⟨hE, hEp⟩
  exact le_bot_iff.mp (hEcore.trans (le_of_eq hcore))

public theorem lemma_seven_seven_centralizer_two
    {G : Type u} [Group G] [Finite G]
    {S P1 P2 : Subgroup G}
    (h : SectionSevenHypotheses G S P1 P2)
    (Gamma : CosetGraphContext G S P1 P2) (cp : CriticalPath Gamma)
    (C : Subgroup G)
    (hC : C = Subgroup.centralizer (omegaOneCenter S : Set G))
    (hsubnormal : SubnormalIn (e Gamma cp.firstStep) C)
    (hcore : twoCoreIn C ≤ S)
    (hchar : Stellmacher.IsCharacteristicTwoType C) :
    IsTwoGroup (Subgroup.centralizer (v Gamma cp.firstStep : Set G)) := by
  let K := Subgroup.centralizer (v Gamma cp.firstStep : Set G)
  let E := twoResidualIn K
  let Q := q Gamma cp.a
  let Ea := e Gamma cp.a
  let P := stabilizer Gamma cp.a
  let Pnext := stabilizer Gamma cp.firstStep
  let J := E ⊔ Q
  have hQleS : Q ≤ S := (local_cores_le_edge_sylow h Gamma cp).1
  have hQp : IsPGroup 2 Q := by
    have hqp : IsPGroup 2 (q Gamma cp.a) := by
      rw [q, Gamma.twoCoreAt_def]
      exact (pCore_isPGroup (p := 2)).map _
    exact hqp
  have hPnextNormK : Pnext ≤ Subgroup.normalizer K :=
    (stabilizer_le_normalizer_v Gamma cp.firstStep).trans
      ((Subgroup.normal_subgroupOf_iff_le_normalizer
        (Subgroup.centralizer_le_normalizer (v Gamma cp.firstStep : Set G))).mp
          (Subgroup.normal_subgroupOf_centralizer_normalizer _))
  have hPnextNormE : Pnext ≤ Subgroup.normalizer E :=
    hPnextNormK.trans (normalizer_le_normalizer_residual K)
  have hQNormE : Q ≤ Subgroup.normalizer E :=
    hQleS.trans ((edge_sylow_data h Gamma cp).2.1.trans hPnextNormE)
  have hResJ : twoResidualIn J = E := twoResidualIn_sup_twoGroup_eq K Q hQp hQNormE
  have hEaP : Ea ≤ P := by
    dsimp [Ea, P, CosetGraphContext.e, stabilizer]
    rw [Gamma.twoResidualAt_def]
    exact twoResidualIn_le _
  have hEaNormQ : Ea ≤ Subgroup.normalizer Q :=
    hEaP.trans (stabilizer_le_normalizer_q Gamma cp.a)
  have hKDC : K ≤ Subgroup.centralizer (z Gamma cp.a : Set G) :=
    Subgroup.centralizer_le (lemma_seven_four h Gamma cp).first_containment.1
  have hEacommE : ⁅Ea, E⁆ ≤ Q := by
    rw [Subgroup.commutator_comm]
    exact (Subgroup.commutator_mono ((twoResidualIn_le K).trans hKDC) le_sup_left).trans
      (lemma_seven_seven_centralizer_commutator h Gamma cp C hC hsubnormal hcore)
  have hEaNormJ : Ea ≤ Subgroup.normalizer J := by
    rw [Subgroup.le_normalizer_iff]
    intro a ha x hx
    let f := (MulAut.conj a).toMonoidHom
    have hmapE : E.map f ≤ J := by
      rintro _ ⟨e, he, rfl⟩
      have hc : ⁅a, e⁆ ∈ Q := hEacommE (Subgroup.commutator_mem_commutator ha he)
      have hm := J.mul_mem (show ⁅a, e⁆ ∈ J from (le_sup_right : Q ≤ J) hc)
        (show e ∈ J from (le_sup_left : E ≤ J) he)
      simpa [f, MulAut.conj_apply, commutatorElement_def, mul_assoc] using hm
    have hmapQ : Q.map f ≤ J := by
      have heq : Q.map f = Q := Subgroup.mem_normalizer_iff_map_conj_eq.mp (hEaNormQ ha)
      rw [heq]
      exact le_sup_right
    have hmapJ : J.map f ≤ J := by
      rw [Subgroup.map_sup]
      exact sup_le hmapE hmapQ
    exact hmapJ (Subgroup.mem_map_of_mem f hx)
  have hEaNormE : Ea ≤ Subgroup.normalizer E := by
    rw [← hResJ]
    exact hEaNormJ.trans (normalizer_le_normalizer_residual J)
  have hEaPnext : Ea ⊔ Pnext = ⊤ := by
    have hEaS : Ea ⊔ S = P := by
      dsimp [Ea, P, CosetGraphContext.e, stabilizer]
      rw [Gamma.twoResidualAt_def]
      exact twoResidualIn_sup_sylow (edge_sylow_data h Gamma cp).1
    have hPPnext : P ⊔ Pnext = ⊤ := by
      rcases cp.edge_stabilizers_are_P with he | he
      · simpa [P, Pnext, he.1, he.2] using h.generated
      · simpa [P, Pnext, he.1, he.2, sup_comm] using h.generated
    rw [← hPPnext, ← hEaS, sup_assoc,
      sup_eq_right.mpr (edge_sylow_data h Gamma cp).2.1]
  have hEnormal : E.Normal := Subgroup.normalizer_eq_top_iff.mp (by
    apply top_unique
    rw [← hEaPnext]
    exact sup_le hEaNormE hPnextNormE)
  have hOmegaZa : omegaOneCenter S ≤ z Gamma cp.a := by
    obtain ⟨_, T, hT⟩ := (edge_sylow_data h Gamma cp).1
    rw [z, Gamma.zAt_def]
    exact le_sSup ⟨T, congrArg omegaOneCenter hT.symm⟩
  have hEC : E ≤ C := by
    rw [hC]
    exact ((twoResidualIn_le K).trans hKDC).trans (Subgroup.centralizer_le hOmegaZa)
  have hEbot : E = ⊥ := normal_subgroup_le_characteristicTwo_eq_bot E C hEnormal hEC hchar
    h.twoCore_eq_bot
  have hresbot : hktPResidual 2 K = ⊥ := by
    have hmap : (twoResidualAmbient (⊤ : Subgroup K)).map K.subtype = E :=
      map_twoResidualAmbient_of_subgroup_image (⊤ : Subgroup K) K.subtype K
        ((MonoidHom.range_eq_map K.subtype).symm.trans (Subgroup.range_subtype K))
    rw [Stellmacher.SectionThree.twoResidualAmbient_top_eq_hktPResidual] at hmap
    apply (Subgroup.map_eq_bot_iff_of_injective (hktPResidual 2 K) K.subtype_injective).mp
    exact hmap.trans hEbot
  let _ : (hktPResidual 2 K).Normal := hktPResidual_normal
  have hp := hktPResidual_quotient_isPGroup (Q := K) (q := 2)
  have hpb : IsPGroup 2 (K ⧸ (⊥ : Subgroup K)) :=
    hp.of_equiv (QuotientGroup.quotientMulEquivOfEq hresbot)
  exact hpb.of_equiv QuotientGroup.quotientBot

end Stellmacher.SectionsFiveToSeven

