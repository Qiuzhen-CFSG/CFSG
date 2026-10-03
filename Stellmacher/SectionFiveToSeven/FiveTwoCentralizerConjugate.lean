module

public import Stellmacher.SectionFiveToSeven.FiveTwoInitialReductions
public import Stellmacher.SectionFiveToSeven.FiveTwoSylowConjugate
public import Stellmacher.SectionFiveToSeven.FiveTwoResidualCentralization

/-!
# The conjugate centralizer in Stellmacher (5.2)

This module proves assertion (3) in Stellmacher's proof of (5.2), conditional
on the maximal-counterexample induction hypothesis for the larger subgroup
`O²(P)`.  Starting from the initial normalizer reduction, it embeds
`O₂(C)B(S)` in a Sylow subgroup of `N_H(K)` conjugate to the global
Sylow by an element of `N_H(B(S))`.

The essential characteristic-two step is made explicit.  For
`N=N_H(O₂(C))`, the global Sylow lies in `C ≤ N`; consequently
`O₂(N) ≤ C` and normality gives `O₂(N)=O₂(C)`.  Characteristic 2 of
`N` therefore yields `C_H(O₂(C))≤O₂(C)`.  The omega-center of the
chosen conjugate Sylow then lies in `Ω₁(Z(O₂(C)))`, whose centralization
of `O²(P)` was proved from (3.5).  The induction hypothesis is restricted
from the omega-center normalizer to its centralizer and composed with
`K ◁◁ O²(P)`.  The equality case uses the identity conjugate.

Source: B. Stellmacher, *An Application of the Amalgam Method: The 2-Local
Structure of N-Groups of Characteristic 2 Type*, Journal of Algebra 190
(1997), proof of (5.2), p. 28, assertion (3).
-/

open scoped Pointwise

namespace Stellmacher.SectionsFiveToSeven

open BenderSuzuki.External

universe u

private theorem twoCoreIn_le_52conj
    {G : Type u} [Group G] (P : Subgroup G) : twoCoreIn P ≤ P :=
  Subgroup.map_subtype_le _

private theorem twoCoreIn_isPGroup_52conj
    {G : Type u} [Group G] (P : Subgroup G) : IsPGroup 2 (twoCoreIn P) :=
  (pCore_isPGroup (p := 2) (G := P)).map P.subtype

private theorem twoCoreIn_normal_52conj
    {G : Type u} [Group G] (P : Subgroup G) :
    ((twoCoreIn P).subgroupOf P).Normal := by
  change (Subgroup.comap P.subtype ((pCore 2 P).map P.subtype)).Normal
  rw [Subgroup.comap_map_eq_self_of_injective P.subtype_injective]
  infer_instance

private theorem le_normalizer_twoCoreIn_52conj
    {G : Type u} [Group G] (P : Subgroup G) :
    P ≤ Subgroup.normalizer (twoCoreIn P : Set G) :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer (twoCoreIn_le_52conj P)).mp
    (twoCoreIn_normal_52conj P)

private theorem normal_twoSubgroup_le_twoCoreIn_52conj
    {G : Type u} [Group G] (Q P : Subgroup G)
    (hQP : Q ≤ P) (hQp : IsPGroup 2 Q)
    (hQnormal : (Q.subgroupOf P).Normal) : Q ≤ twoCoreIn P := by
  have hQpP : IsPGroup 2 (Q.subgroupOf P) :=
    hQp.of_equiv (Subgroup.subgroupOfEquivOfLe hQP).symm
  have hle : Q.subgroupOf P ≤ pCore 2 P := le_sSup ⟨hQnormal, hQpP⟩
  calc
    Q = (Q.subgroupOf P).map P.subtype :=
      (Subgroup.map_subgroupOf_eq_of_le hQP).symm
    _ ≤ (pCore 2 P).map P.subtype := Subgroup.map_mono hle
    _ = twoCoreIn P := rfl

private theorem omegaOneCenter_le_self_52conj
    {G : Type u} [Group G] (S : Subgroup G) : omegaOneCenter S ≤ S := by
  unfold omegaOneCenter
  exact (Subgroup.map_mono (Subgroup.map_subtype_le _)).trans
    (Subgroup.map_subtype_le _)

private theorem omegaOneCenter_le_centerAmbient_52conj
    {G : Type u} [Group G] (S : Subgroup G) :
    omegaOneCenter S ≤ (Subgroup.center S).map S.subtype := by
  unfold omegaOneCenter
  exact Subgroup.map_mono (Subgroup.map_subtype_le _)

private theorem omegaOneCenter_isPGroup_52conj
    {G : Type u} [Group G] (S : Subgroup G) :
    IsPGroup 2 (omegaOneCenter S) := by
  rw [show omegaOneCenter S = Stellmacher.omegaOneCenterAmbient S by rfl]
  exact (Stellmacher.omegaOneCenterAmbient_elementaryAbelian S).isPGroup

private theorem twoResidualSubgroup_normal_52conj
    {G : Type u} [Group G] (P : Subgroup G) :
    (twoResidualSubgroup P).Normal := by
  unfold twoResidualSubgroup
  rw [sInf_eq_iInf]
  exact Subgroup.normal_iInf_normal (fun N =>
    Subgroup.normal_iInf_normal (fun hN => hN.1))

private theorem omegaOneCenter_ne_bot_52conj
    {G : Type u} [Group G] [Finite G]
    (S : Subgroup G) (hS : IsPGroup 2 S) (hSne : S ≠ ⊥) :
    omegaOneCenter S ≠ ⊥ := by
  let _ : Nontrivial S :=
    (Subgroup.nontrivial_iff_ne_bot S).2 hSne
  let _ : Nontrivial (Subgroup.center S) := hS.center_nontrivial
  have hcenterP : IsPGroup 2 (Subgroup.center S) :=
    hS.to_subgroup (Subgroup.center S)
  obtain ⟨n, hn, hcard⟩ := hcenterP.nontrivial_iff_card.mp inferInstance
  have htwo : 2 ∣ Nat.card (Subgroup.center S) := by
    rw [hcard]
    exact dvd_pow_self 2 (Nat.pos_iff_ne_zero.mp hn)
  have hinner := omega₁_map_subtype_ne_bot
    (G := S) (Subgroup.center S) 2 htwo
  intro hbot
  apply hinner
  apply Subgroup.map_injective (f := S.subtype) S.subtype_injective
  simpa [omegaOneCenter] using hbot

private theorem centralizer_map_equiv_52conj
    {G : Type u} [Group G] (A : Subgroup G) (e : G ≃* G) :
    (Subgroup.centralizer (A : Set G)).map e.toMonoidHom =
      Subgroup.centralizer (A.map e.toMonoidHom : Set G) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    change x ∈ Subgroup.centralizer (A : Set G) at hx
    change e x ∈ Subgroup.centralizer (A.map e.toMonoidHom : Set G)
    rw [Subgroup.mem_centralizer_iff] at hx ⊢
    rintro _ ⟨a, ha, rfl⟩
    simpa using congrArg e (hx a ha)
  · intro hy
    refine ⟨e.symm y, ?_, by simp⟩
    change y ∈ Subgroup.centralizer (A.map e.toMonoidHom : Set G) at hy
    change e.symm y ∈ Subgroup.centralizer (A : Set G)
    rw [Subgroup.mem_centralizer_iff] at hy ⊢
    intro a ha
    apply e.injective
    simpa using hy (e a) ⟨a, ha, rfl⟩

private theorem subnormalIn_restrict_52conj
    {G : Type u} [Group G] {A B C : Subgroup G}
    (hAB : A ≤ B) (hBC : B ≤ C) (hsub : SubnormalIn A C) :
    SubnormalIn A B := by
  let BC : Subgroup C := B.subgroupOf C
  let e : BC ≃* B := Subgroup.subgroupOfEquivOfLe hBC
  have hsubBC :
      ((A.subgroupOf C).subgroupOf BC).IsSubnormal := hsub.2.subgroupOf
  have hmapped := Subgroup.IsSubnormal.map
    (f := e.toMonoidHom) e.surjective hsubBC
  have hmap : ((A.subgroupOf C).subgroupOf BC).map e.toMonoidHom =
      A.subgroupOf B := by
    ext a
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact hx
    · intro ha
      let xC : C := ⟨a, hBC (hAB ha)⟩
      let xBC : BC := ⟨xC, hAB ha⟩
      exact ⟨xBC, ha, rfl⟩
  rw [hmap] at hmapped
  exact ⟨hAB, hmapped⟩

private theorem subnormalIn_trans_52conj
    {G : Type u} [Group G] {A B C : Subgroup G}
    (hAB : A ≤ B) (hBC : B ≤ C)
    (hsubAB : SubnormalIn A B) (hsubBC : SubnormalIn B C) :
    SubnormalIn A C := by
  let BC : Subgroup C := B.subgroupOf C
  let e : B ≃* BC := (Subgroup.subgroupOfEquivOfLe hBC).symm
  have hmapped := Subgroup.IsSubnormal.map
    (f := e.toMonoidHom) e.surjective hsubAB.2
  have hmap : (A.subgroupOf B).map e.toMonoidHom =
      (A.subgroupOf C).subgroupOf BC := by
    ext a
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact hx
    · intro ha
      exact ⟨⟨a, hAB ha⟩, ha, rfl⟩
  rw [hmap] at hmapped
  exact ⟨hAB.trans hBC,
    Subgroup.IsSubnormal.trans
      (Subgroup.subgroupOf_mono C hAB) hmapped hsubBC.2⟩

private theorem centralizer_twoCore_le_of_global_sylow_52conj
    {G : Type u} [Group G] [Finite G]
    (S : Sylow 2 G) (C : Subgroup G)
    (hSC : (S : Subgroup G) ≤ C)
    (hOne : C = Subgroup.centralizer (omegaOneCenter (S : Subgroup G) : Set G))
    (hSne : (S : Subgroup G) ≠ ⊥)
    (hlocal : ∀ U : Subgroup G,
      IsTwoLocal U → baumannIn (S : Subgroup G) ≤ U →
        Group.IsSolvable U ∧ Stellmacher.IsCharacteristicTwoType U) :
    Subgroup.centralizer (twoCoreIn C : Set G) ≤ twoCoreIn C := by
  let O : Subgroup G := twoCoreIn C
  let N : Subgroup G := Subgroup.normalizer (O : Set G)
  let Z : Subgroup G := omegaOneCenter (S : Subgroup G)
  have hZC : Z ≤ C := by
    rw [hOne]
    intro z hz
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    obtain ⟨zc, hzc, rfl⟩ := omegaOneCenter_le_centerAmbient_52conj _ hz
    simpa using congrArg (fun x : S => (x : G))
      ((Subgroup.mem_center_iff.mp hzc) ⟨w, omegaOneCenter_le_self_52conj _ hw⟩)
  have hCnormZ : C ≤ Subgroup.normalizer (Z : Set G) := by
    rw [hOne]
    exact Subgroup.centralizer_le_normalizer _
  have hZnormalC : (Z.subgroupOf C).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hZC).mpr hCnormZ
  have hZO : Z ≤ O := normal_twoSubgroup_le_twoCoreIn_52conj Z C hZC
    (omegaOneCenter_isPGroup_52conj _) hZnormalC
  have hZne : Z ≠ ⊥ := omegaOneCenter_ne_bot_52conj
    (S : Subgroup G) S.isPGroup' hSne
  have hOne : O ≠ ⊥ := fun hObot => hZne (le_bot_iff.mp (hZO.trans (le_of_eq hObot)))
  have hCN : C ≤ N := le_normalizer_twoCoreIn_52conj C
  have hSN : (S : Subgroup G) ≤ N := hSC.trans hCN
  have hBN : baumannIn (S : Subgroup G) ≤ N :=
    inf_le_left.trans hSN
  have hNlocal : IsTwoLocal N :=
    ⟨O, hOne, twoCoreIn_isPGroup_52conj C, rfl⟩
  have hNchar : Stellmacher.IsCharacteristicTwoType N :=
    (hlocal N hNlocal hBN).2
  have hcoreNS : twoCoreIn N ≤ (S : Subgroup G) := by
    let SN : Sylow 2 N := S.subtype hSN
    calc
      twoCoreIn N = (pCore 2 N).map N.subtype := rfl
      _ ≤ (SN : Subgroup N).map N.subtype := Subgroup.map_mono
        ((pCore_isPGroup (p := 2) (G := N)).le_sylow_of_normal SN)
      _ = (S : Subgroup G) := by
        dsimp [SN]
        exact Subgroup.map_subgroupOf_eq_of_le hSN
  have hcoreNC : twoCoreIn N ≤ C := hcoreNS.trans hSC
  have hNnormCoreN : N ≤ Subgroup.normalizer (twoCoreIn N : Set G) :=
    le_normalizer_twoCoreIn_52conj N
  have hcoreNnormalC : ((twoCoreIn N).subgroupOf C).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hcoreNC).mpr
      (hCN.trans hNnormCoreN)
  have hcoreNO : twoCoreIn N ≤ O :=
    normal_twoSubgroup_le_twoCoreIn_52conj _ C hcoreNC
      (twoCoreIn_isPGroup_52conj N) hcoreNnormalC
  intro x hx
  have hxN : x ∈ N := Subgroup.centralizer_le_normalizer (O : Set G) hx
  let xN : N := ⟨x, hxN⟩
  have hxcent : xN ∈ Subgroup.centralizer (pCore 2 N : Set N) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hyO : (y : G) ∈ O := hcoreNO (Subgroup.mem_map_of_mem N.subtype hy)
    have hxy := Subgroup.mem_centralizer_iff.mp hx (y : G) hyO
    exact Subtype.ext hxy
  have hxcoreN : xN ∈ pCore 2 N := hNchar hxcent
  exact hcoreNO (Subgroup.mem_map_of_mem N.subtype hxcoreN)

/-- Conditional assertion (3) of Stellmacher (5.2): the normalizer Sylow may be
chosen compatibly with a conjugate omega-centralizer containing `K`
subnormally. -/
public theorem five_two_exists_centralizer_conjugate
    {G : Type u} [Group G] [Finite G]
    (S : Sylow 2 G) (P K : Subgroup G)
    (hP : P ∈ PStarFamily
      (Subgroup.centralizer (omegaOneCenter (S : Subgroup G) : Set G))
      (S : Subgroup G))
    (hK : K ≤ P)
    (hlocal : ∀ U : Subgroup G,
      IsTwoLocal U → baumannIn (S : Subgroup G) ≤ U →
        Group.IsSolvable U ∧ Stellmacher.IsCharacteristicTwoType U)
    (hcomm : K = ⁅K, baumannIn (S : Subgroup G)⁆)
    (hKne : K ≠ ⊥)
    (hlarger : K ≠ twoResidualIn P →
      ∀ U : Subgroup G, IsTwoLocal U →
        baumannIn (S : Subgroup G) ⊔ twoResidualIn P ≤ U →
        SubnormalIn (twoResidualIn P) U) :
    ∃ h : G,
      h ∈ Subgroup.normalizer (baumannIn (S : Subgroup G) : Set G) ∧
      IsSylowTwoIn
        (((S : Subgroup G).map (MulAut.conj h).toMonoidHom) ⊓
          Subgroup.normalizer (K : Set G))
        (Subgroup.normalizer (K : Set G)) ∧
      SubnormalIn K
        ((Subgroup.centralizer
          (omegaOneCenter (S : Subgroup G) : Set G)).map
            (MulAut.conj h).toMonoidHom) := by
  classical
  let S0 : Subgroup G := (S : Subgroup G)
  let B : Subgroup G := baumannIn S0
  let C : Subgroup G := Subgroup.centralizer (omegaOneCenter S0 : Set G)
  let O : Subgroup G := twoCoreIn C
  let R : Subgroup G := twoResidualIn P
  let NK : Subgroup G := Subgroup.normalizer (K : Set G)
  have hinit := five_two_initial_reductions S P K hP hK hlocal hcomm
  have hsolv : Group.IsSolvable P := hinit.1
  have hRsubC : SubnormalIn R C := by simpa [R, C] using hinit.2.1
  have hKsubR : SubnormalIn K R := by simpa [R] using hinit.2.2.1
  have hnormProp := hinit.2.2.2
  have hSP : S0 ≤ P := hP.1.1.2.1.1
  have hPC : P ≤ C := hP.1.1.1
  have hSC : S0 ≤ C := hSP.trans hPC
  by_cases hKR : K = R
  · subst K
    have hPnormR : P ≤ Subgroup.normalizer (R : Set G) := by
      apply (Subgroup.normal_subgroupOf_iff_le_normalizer
        (Subgroup.map_subtype_le (twoResidualSubgroup P))).mp
      change (Subgroup.comap P.subtype
        ((twoResidualSubgroup P).map P.subtype)).Normal
      rw [Subgroup.comap_map_eq_self_of_injective P.subtype_injective]
      exact twoResidualSubgroup_normal_52conj P
    have hSNK : S0 ≤ NK := hSP.trans hPnormR
    refine ⟨1, by simp, ?_, ?_⟩
    · have hSmapOne : S0.map (MulAut.conj (1 : G)).toMonoidHom = S0 := by
        ext x
        simp [Subgroup.mem_map]
      change IsSylowTwoIn
        (S0.map (MulAut.conj (1 : G)).toMonoidHom ⊓ NK) NK
      rw [hSmapOne]
      rw [inf_eq_left.mpr hSNK]
      exact
        (show IsSylowTwoIn S0 NK from ⟨hSNK, S.subtype hSNK, by
          rw [Sylow.coe_subtype, Subgroup.map_subgroupOf_eq_of_le hSNK]⟩)
    · have hCmapOne : C.map (MulAut.conj (1 : G)).toMonoidHom = C := by
        ext x
        simp [Subgroup.mem_map]
      rw [hCmapOne]
      exact hRsubC
  · have hOp : IsPGroup 2 O := twoCoreIn_isPGroup_52conj C
    have hBp : IsPGroup 2 B := S.isPGroup'.to_le inf_le_left
    have hBnormO : B ≤ Subgroup.normalizer (O : Set G) :=
      inf_le_left.trans (hSC.trans (le_normalizer_twoCoreIn_52conj C))
    have hQp : IsPGroup 2 ↑(O ⊔ B) :=
      hOp.to_sup_of_normal_left' hBp hBnormO
    have hBKnormO : B ⊔ K ≤ Subgroup.normalizer (O : Set G) := by
      exact sup_le
        (inf_le_left.trans (hSC.trans (le_normalizer_twoCoreIn_52conj C)))
        (hK.trans (hPC.trans (le_normalizer_twoCoreIn_52conj C)))
    have hOnK : O ≤ NK := by
      simpa [B, NK] using hnormProp O hOp (by simpa [B, sup_comm] using hBKnormO)
    have hBnK : B ≤ NK := by
      apply Subgroup.le_normalizer_iff_commutator_le_left.mpr
      exact hcomm.symm.le
    have hQNK : O ⊔ B ≤ NK := sup_le hOnK hBnK
    obtain ⟨h, hhB, hQSh, hSylow⟩ :=
      exists_sylow_inter_baumann_conjugate S NK (O ⊔ B)
        hQp hQNK le_sup_right
    let e : G ≃* G := MulAut.conj h
    let Sh : Subgroup G := S0.map e.toMonoidHom
    let Zh : Subgroup G := (omegaOneCenter S0).map e.toMonoidHom
    have hZmap : omegaOneCenter Sh = Zh := by
      simpa [Sh, Zh, omegaOneCenter,
        Stellmacher.omegaOneCenterAmbient] using
        (Stellmacher.omegaOneCenterAmbient_map_injective
          e.toMonoidHom e.injective S0)
    have hOSh : O ≤ Sh := le_sup_left.trans (by simpa [Sh, e] using hQSh)
    have hBSh : B ≤ Sh := le_sup_right.trans (by simpa [Sh, e] using hQSh)
    have hSne : S0 ≠ ⊥ := by
      intro hSbot
      have hcoreP_leS : twoCoreIn P ≤ S0 := by
        obtain ⟨_, T, hT⟩ := hP.1.1.2.1
        change twoCoreIn P ≤ (S : Subgroup G)
        rw [← hT]
        simpa [twoCoreIn] using Subgroup.map_mono (f := P.subtype)
          ((pCore_isPGroup (G := P) (p := 2)).le_sylow_of_normal T)
      exact hP.1.1.2.2.1
        (le_bot_iff.mp (hcoreP_leS.trans (le_of_eq hSbot)))
    have hCO : Subgroup.centralizer (O : Set G) ≤ O :=
      centralizer_twoCore_le_of_global_sylow_52conj S C hSC rfl hSne hlocal
    have hZhO : Zh ≤ O := by
      intro z hz
      apply hCO
      rw [Subgroup.mem_centralizer_iff]
      intro o ho
      have hzcenter := omegaOneCenter_le_centerAmbient_52conj Sh
        (show z ∈ omegaOneCenter Sh by simpa [hZmap] using hz)
      obtain ⟨zc, hzc, hzeq⟩ := hzcenter
      have hcommz := (Subgroup.mem_center_iff.mp hzc) ⟨o, hOSh ho⟩
      have hcoe := congrArg (fun x : Sh => (x : G)) hcommz
      change o * z = z * o
      rw [← hzeq]
      simpa using hcoe
    have hZhOmegaO : Zh ≤ omegaOneCenter O := by
      intro z hz
      have hzSh : z ∈ omegaOneCenter Sh := by simpa [hZmap] using hz
      have hzdata := (Stellmacher.mem_omegaOneCenterAmbient_iff Sh z).mp
        (by simpa [omegaOneCenter, Stellmacher.omegaOneCenterAmbient] using hzSh)
      apply (Stellmacher.mem_omegaOneCenterAmbient_iff O z).mpr
      refine ⟨hZhO hz, hzdata.2.1, ?_⟩
      intro o ho
      have hzcenter := omegaOneCenter_le_centerAmbient_52conj Sh hzSh
      obtain ⟨zc, hzc, hzeq⟩ := hzcenter
      have hcommz := (Subgroup.mem_center_iff.mp hzc) ⟨o, hOSh ho⟩
      have hcoe := congrArg (fun x : Sh => (x : G)) hcommz
      simpa [← hzeq] using hcoe
    have hcent := pstar_omegaTwoCore_centralizes_twoResidual S P hP hsolv
    have hRcentOmega : R ≤ Subgroup.centralizer (omegaOneCenter O : Set G) := by
      rw [← Subgroup.commutator_eq_bot_iff_le_centralizer,
        Subgroup.commutator_comm]
      simpa [R, O, C] using hcent
    have hRcentZh : R ≤ Subgroup.centralizer (Zh : Set G) :=
      hRcentOmega.trans (Subgroup.centralizer_le hZhOmegaO)
    have hBcentZh : B ≤ Subgroup.centralizer (Zh : Set G) := by
      intro b hb
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      have hzSh : z ∈ omegaOneCenter Sh := by simpa [hZmap] using hz
      obtain ⟨zc, hzc, hzeq⟩ := omegaOneCenter_le_centerAmbient_52conj Sh hzSh
      have hcommz := (Subgroup.mem_center_iff.mp hzc) ⟨b, hBSh hb⟩
      have hcoe := congrArg (fun x : Sh => (x : G)) hcommz
      simpa [← hzeq] using hcoe.symm
    have hCmap : C.map e.toMonoidHom = Subgroup.centralizer (Zh : Set G) := by
      change (Subgroup.centralizer (omegaOneCenter S0 : Set G)).map e.toMonoidHom = _
      exact centralizer_map_equiv_52conj (omegaOneCenter S0) e
    have hRsubCh : SubnormalIn R (C.map e.toMonoidHom) := by
      rw [hCmap]
      have hZne : omegaOneCenter S0 ≠ ⊥ :=
        omegaOneCenter_ne_bot_52conj S0 S.isPGroup' hSne
      have hZhNe : Zh ≠ ⊥ := by
        intro hbot
        apply hZne
        exact (Subgroup.map_eq_bot_iff_of_injective _ e.injective).mp hbot
      have hZhp : IsPGroup 2 Zh :=
        (omegaOneCenter_isPGroup_52conj S0).map e.toMonoidHom
      let NZ : Subgroup G := Subgroup.normalizer (Zh : Set G)
      have hNZlocal : IsTwoLocal NZ := ⟨Zh, hZhNe, hZhp, rfl⟩
      have hBRNZ : B ⊔ R ≤ NZ := by
        exact (sup_le hBcentZh hRcentZh).trans
          (Subgroup.centralizer_le_normalizer _)
      have hRsubNZ : SubnormalIn R NZ := by
        simpa [B, R] using hlarger hKR NZ hNZlocal (by simpa [B, R] using hBRNZ)
      exact subnormalIn_restrict_52conj hRcentZh
        (Subgroup.centralizer_le_normalizer _) hRsubNZ
    have hKsubCh : SubnormalIn K (C.map e.toMonoidHom) :=
      subnormalIn_trans_52conj hKsubR.1 hRsubCh.1 hKsubR hRsubCh
    exact ⟨h, hhB, by simpa [NK, S0, e] using hSylow, hKsubCh⟩

end Stellmacher.SectionsFiveToSeven
