module

public import Stellmacher.SectionFiveToSeven.PFamilyBridge
public import Stellmacher.SectionFiveToSeven.FiveTwoPStarCentralizer
public import Stellmacher.SectionThree.LemmaThreeFive
public import BenderSuzuki.External.Huppert.IV.Basic
public import Theory.GroupTheory.PGroup.Subnormal

/-!
# Centralizing the P-star residual in Stellmacher (5.2)

Let `S` be a Sylow 2-subgroup, put `C = C_G(Ω₁(Z(S)))`, and let `P` be a
solvable member of `PStarFamily C S`. This module proves the (3.5) consequence
used in the maximal-counterexample argument of Stellmacher (5.2):
`Ω₁(Z(O₂(C)))` centralizes `O²(P)`.

The proof derives the Section 3 hypotheses from the Sylow and P-star data.
The subgroup `O₂(C)` lies in `S`, hence in `P`, and is normal in `P`. Also,
`O₂(P) ∩ O²(P)` is normal in the subnormal subgroup `O²(P)` of `C`;
the subnormal p-subgroup theorem therefore puts this intersection in `O₂(C)`.
Its centralization by `Ω₁(Z(O₂(C)))` gives the hypothesis of (3.5).
The other branch of (3.5) is impossible because `P ≤ C_G(Ω₁(Z(S)))`.

Source: B. Stellmacher, *An Application of the Amalgam Method: The 2-Local
Structure of N-Groups of Characteristic 2 Type*, Journal of Algebra 190
(1997), proof of Lemma (5.2), p. 28; see
`refs/latex/stellmacher-n-group.tex`.
-/

open scoped Pointwise

namespace Stellmacher.SectionsFiveToSeven

universe u

private theorem twoCoreIn_le_of_isSylowTwoIn_52c
    {G : Type u} [Group G]
    {S P : Subgroup G} (hS : IsSylowTwoIn S P) :
    twoCoreIn P ≤ S := by
  obtain ⟨_hSP, T, rfl⟩ := hS
  exact Subgroup.map_mono
    ((pCore_isPGroup (G := P) (p := 2)).le_sylow_of_normal T)

private theorem twoCoreIn_normal_subgroupOf_52c
    {G : Type u} [Group G] (P : Subgroup G) :
    ((twoCoreIn P).subgroupOf P).Normal := by
  rw [← Subgroup.comap_subtype, twoCoreIn,
    Subgroup.comap_map_eq_self_of_injective P.subtype_injective]
  exact (inferInstance : (pCore 2 P).Normal)

private theorem twoCoreIn_isPGroup_52c
    {G : Type u} [Group G] (P : Subgroup G) :
    IsPGroup 2 (twoCoreIn P) :=
  (pCore_isPGroup (p := 2) (G := P)).map P.subtype

private theorem normal_pSubgroup_le_twoCoreIn_52c
    {G : Type u} [Group G]
    (Q P : Subgroup G) (hQP : Q ≤ P)
    (hQp : IsPGroup 2 Q) (hQnormal : (Q.subgroupOf P).Normal) :
    Q ≤ twoCoreIn P := by
  have hQpP : IsPGroup 2 (Q.subgroupOf P) :=
    hQp.of_equiv (Subgroup.subgroupOfEquivOfLe hQP).symm
  have hle : Q.subgroupOf P ≤ pCore 2 P := le_sSup ⟨hQnormal, hQpP⟩
  calc
    Q = (Q.subgroupOf P).map P.subtype :=
      (Subgroup.map_subgroupOf_eq_of_le hQP).symm
    _ ≤ (pCore 2 P).map P.subtype := Subgroup.map_mono hle
    _ = twoCoreIn P := rfl

private theorem normalizer_le_normalizer_omegaOneCenter_52c
    {G : Type u} [Group G] (Q : Subgroup G) :
    Subgroup.normalizer (Q : Set G) ≤
      Subgroup.normalizer (omegaOneCenter Q : Set G) := by
  let K : Subgroup Q :=
    (omega₁ (G := Subgroup.center Q) (p := 2)).map
      (Subgroup.center Q).subtype
  let _ : (omega₁ (G := Subgroup.center Q) (p := 2)).Characteristic :=
    omega₁_characteristic (Subgroup.center Q)
  have hK : K.Characteristic := inferInstance
  let _ : K.Characteristic := hK
  exact BenderSuzuki.External.hkt_normalizer_le_normalizer_map_subtype_of_characteristic
    Q K

private theorem omegaOneCenter_le_centerAmbient_52c
    {G : Type u} [Group G] (Q : Subgroup G) :
    omegaOneCenter Q ≤ (Subgroup.center Q).map Q.subtype := by
  unfold omegaOneCenter
  exact Subgroup.map_mono (Subgroup.map_subtype_le _)

private theorem centerAmbient_le_centralizer_52c
    {G : Type u} [Group G] (Q : Subgroup G) :
    (Subgroup.center Q).map Q.subtype ≤
      Subgroup.centralizer (Q : Set G) := by
  intro x hx
  obtain ⟨xc, hxc, rfl⟩ := hx
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  exact congrArg Subtype.val
    (Subgroup.mem_center_iff.mp hxc ⟨y, hy⟩)

private theorem normal_subgroupOf_subgroupOf_52c
    {G : Type u} [Group G] {H K L : Subgroup G}
    (hHK : H ≤ K) (_hKL : K ≤ L)
    (hN : (H.subgroupOf K).Normal) :
    ((H.subgroupOf L).subgroupOf (K.subgroupOf L)).Normal := by
  rw [Subgroup.normal_subgroupOf_iff (Subgroup.subgroupOf_mono L hHK)]
  intro h k hh hk
  exact (Subgroup.normal_subgroupOf_iff hHK).mp hN
    (h : G) (k : G) hh hk

private theorem sectionThreeHypotheses_of_pstar_52c
    {G : Type u} [Group G] [Finite G]
    (S : Sylow 2 G) (P : Subgroup G)
    (hP : P ∈ PStarFamily
      (Subgroup.centralizer (omegaOneCenter (S : Subgroup G) : Set G))
      (S : Subgroup G)) :
    Stellmacher.SectionThree.Hypotheses G (S : Subgroup G) := by
  have hcoreP_le_S : twoCoreIn P ≤ (S : Subgroup G) :=
    twoCoreIn_le_of_isSylowTwoIn_52c hP.1.1.2.1
  have hSne : (S : Subgroup G) ≠ ⊥ := by
    intro hSbot
    apply hP.1.1.2.2.1
    exact le_bot_iff.mp (hcoreP_le_S.trans (le_of_eq hSbot))
  let _ : Nontrivial (S : Subgroup G) :=
    (Subgroup.nontrivial_iff_ne_bot (S : Subgroup G)).2 hSne
  obtain ⟨n, hn, hcard⟩ := S.isPGroup'.nontrivial_iff_card.mp inferInstance
  have hEven : Even (Nat.card G) := by
    apply even_iff_two_dvd.mpr
    apply (show 2 ∣ Nat.card (S : Subgroup G) by
      rw [hcard]
      exact dvd_pow_self 2 (Nat.pos_iff_ne_zero.mp hn)).trans
    exact Subgroup.card_subgroup_dvd_card (S : Subgroup G)
  exact
    { even_order := hEven
      nontrivial_two_subgroup := ⟨hSne, S.isPGroup'⟩ }

/-- In the P-star configuration of (5.2), the omega-one center of the
2-core of the omega centralizer centralizes the two-residual of `P`. -/
public theorem pstar_omegaTwoCore_centralizes_twoResidual
    {G : Type u} [Group G] [Finite G]
    (S : Sylow 2 G) (P : Subgroup G)
    (hP : P ∈ PStarFamily
      (Subgroup.centralizer (omegaOneCenter (S : Subgroup G) : Set G))
      (S : Subgroup G))
    (hsolv : Group.IsSolvable P) :
    ⁅omegaOneCenter
        (twoCoreIn
          (Subgroup.centralizer
            (omegaOneCenter (S : Subgroup G) : Set G))),
      twoResidualIn P⁆ = ⊥ := by
  let C : Subgroup G :=
    Subgroup.centralizer (omegaOneCenter (S : Subgroup G) : Set G)
  let Q : Subgroup G := twoCoreIn C
  let R : Subgroup G := twoResidualIn P
  let N : Subgroup G := omegaOneCenter Q
  have hSC : (S : Subgroup G) ≤ C := by
    intro s hs
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    obtain ⟨zc, hzc, rfl⟩ :=
      omegaOneCenter_le_centerAmbient_52c (S : Subgroup G) hz
    exact congrArg Subtype.val
      (Subgroup.mem_center_iff.mp hzc ⟨s, hs⟩).symm
  have hSylowC : IsSylowTwoIn (S : Subgroup G) C := by
    refine ⟨hSC, S.subtype hSC, ?_⟩
    rw [Sylow.coe_subtype, Subgroup.map_subgroupOf_eq_of_le hSC]
  have hQleS : Q ≤ (S : Subgroup G) :=
    twoCoreIn_le_of_isSylowTwoIn_52c hSylowC
  have hPC : P ≤ C := hP.1.1.1
  have hSP : (S : Subgroup G) ≤ P := hP.1.1.2.1.1
  have hQleP : Q ≤ P := hQleS.trans hSP
  have hCnormQ : C ≤ Subgroup.normalizer (Q : Set G) := by
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer
      (Subgroup.map_subtype_le (pCore 2 C))).mp
        (twoCoreIn_normal_subgroupOf_52c C)
  have hPnormQ : P ≤ Subgroup.normalizer (Q : Set G) := hPC.trans hCnormQ
  have hQnormalP : (Q.subgroupOf P).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQleP).mpr hPnormQ
  have hQleCoreP : Q ≤ twoCoreIn P :=
    normal_pSubgroup_le_twoCoreIn_52c Q P hQleP
      (twoCoreIn_isPGroup_52c C) hQnormalP
  have hNleQ : N ≤ Q := by
    exact (omegaOneCenter_le_centerAmbient_52c Q).trans
      (Subgroup.map_subtype_le (Subgroup.center Q))
  have hPnormN : P ≤ Subgroup.normalizer (N : Set G) :=
    hPnormQ.trans (normalizer_le_normalizer_omegaOneCenter_52c Q)
  have hNleP : N ≤ P := hNleQ.trans hQleP
  have hNnormalP : (N.subgroupOf P).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNleP).mpr hPnormN
  have hRsubC : SubnormalIn R C := by
    simpa [R, C] using
      pstar_residual_subnormal_in_omegaCentralizer S P hP
  let A : Subgroup G := twoCoreIn P ⊓ R
  have hAleR : A ≤ R := inf_le_right
  have hRleP : R ≤ P := Subgroup.map_subtype_le (twoResidualSubgroup P)
  have hPnormCoreP : P ≤ Subgroup.normalizer (twoCoreIn P : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer
      (Subgroup.map_subtype_le (pCore 2 P))).mp
        (twoCoreIn_normal_subgroupOf_52c P)
  have hAnormalR : (A.subgroupOf R).Normal := by
    apply (Subgroup.normal_subgroupOf_iff_le_normalizer hAleR).mpr
    exact (le_inf (hRleP.trans hPnormCoreP) R.le_normalizer).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  have hAsubC : (A.subgroupOf C).IsSubnormal := by
    refine Subgroup.IsSubnormal.step _ (R.subgroupOf C)
      (Subgroup.subgroupOf_mono C hAleR) hRsubC.2 ?_
    exact normal_subgroupOf_subgroupOf_52c hAleR hRsubC.1 hAnormalR
  have hAp : IsPGroup 2 A :=
    IsPGroup.to_le (twoCoreIn_isPGroup_52c P) inf_le_left
  have hAleQ : A ≤ Q := by
    exact isPGroup_le_pCoreAmbient_of_isSubnormalIn C A 2
      (hAleR.trans hRsubC.1) hAsubC hAp
  have hcentral : ⁅N, twoCoreIn P ⊓ R⁆ = ⊥ := by
    apply Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
    exact (omegaOneCenter_le_centerAmbient_52c Q).trans
      ((centerAmbient_le_centralizer_52c Q).trans
        (Subgroup.centralizer_le hAleQ))
  have hPtop : P ∈ PFamily (⊤ : Subgroup G) (S : Subgroup G) := by
    exact ⟨⟨le_top, hP.1.1.2⟩, hP.1.2⟩
  have hPset : P ∈ Stellmacher.SectionThree.PSet
      (⊤ : Subgroup G) (S : Subgroup G) :=
    (pFamily_iff_pSet (⊤ : Subgroup G) (S : Subgroup G) P).mp hPtop
  have hsec := sectionThreeHypotheses_of_pstar_52c S P hP
  rcases Stellmacher.SectionThree.lemma_three_five_omega
      (S : Subgroup G) hsec P hPset N
      ⟨hNleP, hNleQ.trans hQleCoreP, hNnormalP⟩ hsolv hcentral with
    hnot | hcomm
  · exfalso
    apply hnot
    apply Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
    apply Subgroup.le_centralizer_iff.mp
    exact hRleP.trans hPC
  · change ⁅omegaOneCenter
        (twoCoreIn
          (Subgroup.centralizer
            (omegaOneCenter (S : Subgroup G) : Set G))),
      twoResidualAmbient P⁆ = ⊥
    simpa [C, Q, R, N] using hcomm

end Stellmacher.SectionsFiveToSeven
