module

public import Stellmacher.SectionThree.LemmaThreeFive
public import Theory.GroupTheory.PGroup.SubnormalCore

/-!
# Centralization of subnormal two-cores in Stellmacher (5.2)

Let `P ∈ ℘(S)` be solvable and suppose the omega-center of `S`
centralizes `O²(P)`.  This module proves the consequence of Stellmacher
(3.5) used in assertion (7) of (5.2): if `K` is subnormal in `O²(P)`,
then `Z(O₂(K))` centralizes `K`.

The proof first applies the omega-center form of (3.5) at
`R = O²(P)`.  Here `Z(O₂(R))` really is normal in the original `P`,
and `O₂(P) ∩ R ≤ O₂(R)` supplies the required centralization hypothesis.
It then descends through a subnormal chain.  At a normal step `K ◁ L`,
the subgroup `[Z(O₂(K)),K]` is a normal two-subgroup of `L`, hence lies
in `O₂(L)`.  If nontrivial, it meets `Z(O₂(L))` nontrivially.  The upper
centralization makes such an element fixed by `K`, while Lemma (3.3)(a)
makes the effective action of `K ≤ O²(P)` on `Z(O₂(K))` an odd-prime
group.  Coprime splitting says that the fixed subgroup meets the action
commutator trivially, a contradiction.

Thus normality of `Z(O₂(K))` is only used in its actual containing normal
step; the proof does not supply the unjustified original-`P` normality
that is suppressed by the source's terse invocation of (3.5).

Source: B. Stellmacher, *An Application of the Amalgam Method: The 2-Local
Structure of N-Groups of Characteristic 2 Type*, Journal of Algebra 190
(1997), Lemma (3.5), p. 22 and proof of Lemma (5.2), p. 29; see
`refs/latex/stellmacher-n-group.tex`.
-/

open scoped Pointwise IsMulCommutative commutatorElement

namespace Stellmacher.SectionThree

universe u

private theorem twoResidualSubgroup_normal'
    {X : Type*} [Group X] (P : Subgroup X) :
    (twoResidualSubgroup P).Normal := by
  unfold twoResidualSubgroup
  rw [sInf_eq_iInf]
  exact Subgroup.normal_iInf_normal (fun N =>
    Subgroup.normal_iInf_normal (fun hN => hN.1))

private theorem twoCoreAmbient_normal_subgroupOf'
    {X : Type*} [Group X] (K : Subgroup X) :
    ((twoCoreAmbient K).subgroupOf K).Normal := by
  rw [← Subgroup.comap_subtype, twoCoreAmbient,
    Subgroup.comap_map_eq_self_of_injective K.subtype_injective]
  exact (inferInstance : (pCore 2 K).Normal)

private theorem twoCoreAmbient_isPGroup'
    {X : Type*} [Group X] [Finite X] (K : Subgroup X) :
    IsPGroup 2 (twoCoreAmbient K) :=
  (pCore_isPGroup (p := 2) (G := K)).map K.subtype

private theorem center_twoCoreAmbient_isPGroup'
    {X : Type*} [Group X] [Finite X] (K : Subgroup X) :
    IsPGroup 2 ((Subgroup.center (twoCoreAmbient K)).map
      (twoCoreAmbient K).subtype) := by
  exact (twoCoreAmbient_isPGroup' K).to_subgroup
    (Subgroup.center (twoCoreAmbient K)) |>.map (twoCoreAmbient K).subtype

private theorem normalizer_le_normalizer_center_twoCoreAmbient'
    {X : Type*} [Group X] (K : Subgroup X) :
    Subgroup.normalizer (K : Set X) ≤
      Subgroup.normalizer
        ((Subgroup.center (twoCoreAmbient K)).map
          (twoCoreAmbient K).subtype : Set X) := by
  have hcore : Subgroup.normalizer (K : Set X) ≤
      Subgroup.normalizer (twoCoreAmbient K : Set X) := by
    simpa only [twoCoreAmbient] using
      (BenderSuzuki.External.hkt_normalizer_le_normalizer_map_subtype_of_characteristic
        K (pCore 2 K))
  exact hcore.trans
    (BenderSuzuki.External.hkt_normalizer_le_normalizer_map_subtype_of_characteristic
      (twoCoreAmbient K) (Subgroup.center (twoCoreAmbient K)))

private theorem center_twoCoreAmbient_normal_subgroupOf'
    {X : Type*} [Group X] (K : Subgroup X) :
    (((Subgroup.center (twoCoreAmbient K)).map
      (twoCoreAmbient K).subtype).subgroupOf K).Normal := by
  apply (Subgroup.normal_subgroupOf_iff_le_normalizer (by
    exact (Subgroup.map_subtype_le _).trans (Subgroup.map_subtype_le _))).mpr
  exact K.le_normalizer.trans (normalizer_le_normalizer_center_twoCoreAmbient' K)

private theorem commutator_twoCore_center_normal_subgroupOf'
    {X : Type*} [Group X] (K L : Subgroup X) (hKL : K ≤ L)
    (hKnormal : (K.subgroupOf L).Normal) :
    (⁅(Subgroup.center (twoCoreAmbient K)).map
      (twoCoreAmbient K).subtype, K⁆.subgroupOf L).Normal := by
  let ZK : Subgroup X := (Subgroup.center (twoCoreAmbient K)).map
    (twoCoreAmbient K).subtype
  let A : Subgroup X := ⁅ZK, K⁆
  have hKnorm : L ≤ Subgroup.normalizer (K : Set X) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKL).mp hKnormal
  have hZKleK : ZK ≤ K :=
    (Subgroup.map_subtype_le _).trans (Subgroup.map_subtype_le _)
  have hZKnorm : (ZK.subgroupOf L).Normal := by
    apply (Subgroup.normal_subgroupOf_iff_le_normalizer (hZKleK.trans hKL)).mpr
    exact hKnorm.trans (normalizer_le_normalizer_center_twoCoreAmbient' K)
  have hKnormL : (K.subgroupOf L).Normal := hKnormal
  let _ : (ZK.subgroupOf L).Normal := hZKnorm
  let _ : (K.subgroupOf L).Normal := hKnormL
  have hcommNormal : (⁅ZK.subgroupOf L, K.subgroupOf L⁆).Normal := inferInstance
  have hAleL : A ≤ L :=
    (Subgroup.commutator_le_sup ZK K).trans
      (sup_le (hZKleK.trans hKL) hKL)
  have heq : A.subgroupOf L = ⁅ZK.subgroupOf L, K.subgroupOf L⁆ := by
    apply Subgroup.map_injective L.subtype_injective
    rw [Subgroup.map_subgroupOf_eq_of_le hAleL]
    symm
    simpa [A] using commutator_subgroupOf_map_eq L K ZK hKL
      (hZKleK.trans hKL)
  change (A.subgroupOf L).Normal
  rw [heq]
  exact hcommNormal

private theorem normal_pSubgroup_le_twoCoreAmbient'
    {X : Type*} [Group X] [Finite X]
    (Q K : Subgroup X) (hQK : Q ≤ K)
    (hQp : IsPGroup 2 Q) (hQnormal : (Q.subgroupOf K).Normal) :
    Q ≤ twoCoreAmbient K := by
  have hQpK : IsPGroup 2 (Q.subgroupOf K) :=
    hQp.of_equiv (Subgroup.subgroupOfEquivOfLe hQK).symm
  have hle : Q.subgroupOf K ≤ pCore 2 K := le_sSup ⟨hQnormal, hQpK⟩
  calc
    Q = (Q.subgroupOf K).map K.subtype :=
      (Subgroup.map_subgroupOf_eq_of_le hQK).symm
    _ ≤ (pCore 2 K).map K.subtype := Subgroup.map_mono hle
    _ = twoCoreAmbient K := rfl

private theorem twoResidualAmbient_normal_subgroupOf'
    {X : Type*} [Group X] (P : Subgroup X) :
    ((twoResidualAmbient P).subgroupOf P).Normal := by
  rw [← Subgroup.comap_subtype, twoResidualAmbient,
    Subgroup.comap_map_eq_self_of_injective P.subtype_injective]
  exact twoResidualSubgroup_normal' P

private theorem residual_twoCore_center_centralizes'
    {G : Type u} [Group G] [Finite G]
    (S : Subgroup G) (h : Hypotheses G S)
    (P : Subgroup G) (hP : P ∈ PSet (⊤ : Subgroup G) S)
    (hsolv : Group.IsSolvable P)
    (hOmega : ⁅omegaOneCenterAmbient S, twoResidualAmbient P⁆ = ⊥) :
    let R := twoResidualAmbient P
    ⁅(Subgroup.center (twoCoreAmbient R)).map
      (twoCoreAmbient R).subtype, R⁆ = ⊥ := by
  classical
  let R : Subgroup G := twoResidualAmbient P
  let OR : Subgroup G := twoCoreAmbient R
  let ZR : Subgroup G := (Subgroup.center OR).map OR.subtype
  have hRP : R ≤ P := Subgroup.map_subtype_le _
  have hRnormalP : (R.subgroupOf P).Normal :=
    twoResidualAmbient_normal_subgroupOf' P
  have hRsubP : (R.subgroupOf P).IsSubnormal := hRnormalP.isSubnormal
  have hORleOP : OR ≤ twoCoreAmbient P := by
    simpa [OR, twoCoreAmbient] using
      (pCoreAmbient_mono_of_isSubnormalIn R P 2 hRP hRsubP)
  have hZRleOR : ZR ≤ OR := Subgroup.map_subtype_le _
  have hZRleP : ZR ≤ P := hZRleOR.trans
    ((Subgroup.map_subtype_le _ : OR ≤ R).trans hRP)
  have hZRleOP : ZR ≤ twoCoreAmbient P := hZRleOR.trans hORleOP
  have hPnormR : P ≤ Subgroup.normalizer (R : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hRP).mp hRnormalP
  have hZRnormalP : (ZR.subgroupOf P).Normal := by
    apply (Subgroup.normal_subgroupOf_iff_le_normalizer hZRleP).mpr
    exact hPnormR.trans (normalizer_le_normalizer_center_twoCoreAmbient' R)
  let OP : Subgroup G := twoCoreAmbient P
  let Q : Subgroup G := OP ⊓ R
  have hOPnormalP : (OP.subgroupOf P).Normal :=
    twoCoreAmbient_normal_subgroupOf' P
  have hQleR : Q ≤ R := inf_le_right
  have hQnormalR : (Q.subgroupOf R).Normal := by
    apply (Subgroup.normal_subgroupOf_iff hQleR).mpr
    intro q r hq hr
    refine ⟨?_, ?_⟩
    · exact (Subgroup.normal_subgroupOf_iff (Subgroup.map_subtype_le _)).mp
        hOPnormalP q r hq.1 (hRP hr)
    · exact R.mul_mem (R.mul_mem hr hq.2) (R.inv_mem hr)
  have hQp : IsPGroup 2 Q :=
    (twoCoreAmbient_isPGroup' P).to_subgroup (Q.subgroupOf OP) |>.of_equiv
      (Subgroup.subgroupOfEquivOfLe inf_le_left)
  have hQleOR : Q ≤ OR :=
    normal_pSubgroup_le_twoCoreAmbient' Q R hQleR hQp hQnormalR
  have hcentral : ⁅ZR, Q⁆ = ⊥ := by
    apply Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
    intro z hz q hq
    obtain ⟨z0, hz0, rfl⟩ := hz
    let q0 : OR := ⟨q, hQleOR hq⟩
    exact congrArg (fun x : OR => (x : G))
      ((Subgroup.mem_center_iff.mp hz0) q0)
  have h35 := lemma_three_five_omega S h P hP ZR
    ⟨hZRleP, hZRleOP, hZRnormalP⟩ hsolv (by simpa [Q, OP] using hcentral)
  rcases h35 with hbad | hgood
  · exact False.elim (hbad hOmega)
  · simpa [R, OR, ZR] using hgood

private theorem commutatorAction_range_toMulAut_eq'
    {X A : Type*} [Group X] [Group A] [MulDistribMulAction A X] :
    let rho : A →* MulAut X := MulDistribMulAction.toMulAut A X
    commutatorAction (A := rho.range) (G := X) =
      commutatorAction (A := A) (G := X) := by
  classical
  let rho : A →* MulAut X := MulDistribMulAction.toMulAut A X
  dsimp
  rw [commutatorAction_eq_closure, commutatorAction_eq_closure]
  congr 1
  ext x
  constructor
  · rintro ⟨b, y, rfl⟩
    rcases b with ⟨_, a, rfl⟩
    refine ⟨a, y, ?_⟩
    simp [MulDistribMulAction.toMulAut_apply]
  · rintro ⟨a, y, rfl⟩
    refine ⟨⟨rho a, ⟨a, rfl⟩⟩, y, ?_⟩
    simp [rho, MulDistribMulAction.toMulAut_apply]

private theorem isPGroup_range_of_ker_le_ker'
    {A Q B : Type*} [Group A] [Finite A] [Group Q] [Finite Q]
    [Group B] [Finite B]
    {p : ℕ} [Fact p.Prime] (q : A →* Q) (rho : A →* B)
    (hq : IsPGroup p q.range) (hker : q.ker ≤ rho.ker) :
    IsPGroup p rho.range := by
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := p)).mp hq
  apply IsPGroup.of_card_dvd_pow (n := n)
  rw [← Subgroup.index_ker rho, ← hn, ← Subgroup.index_ker q]
  exact Subgroup.index_dvd_of_le hker

private theorem isPGroup_subgroup_of_le'
    {X : Type*} [Group X] {p : ℕ} {U V : Subgroup X}
    (hV : IsPGroup p V) (hUV : U ≤ V) : IsPGroup p U := by
  exact hV.of_injective (Subgroup.inclusion hUV)
    (Subgroup.inclusion_injective hUV)

private theorem twoResidualSubgroup_map_quotient_le'
    {X : Type*} [Group X] [Finite X]
    (R O : Subgroup X) [O.Normal]
    (hR : R = sInf {N : Subgroup X | N.Normal ∧ ∃ n : ℕ, N.index = 2 ^ n}) :
    R.map (QuotientGroup.mk' O) ≤
      twoResidualAmbient (⊤ : Subgroup (X ⧸ O)) := by
  classical
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let q : X →* X ⧸ O := QuotientGroup.mk' O
  let U : Subgroup (X ⧸ O) :=
    twoResidualAmbient (⊤ : Subgroup (X ⧸ O))
  have hUeq : U = BenderSuzuki.External.hktPResidual 2 (X ⧸ O) := by
    simpa [U] using
      (twoResidualAmbient_top_eq_hktPResidual (Q := X ⧸ O))
  have hUnormal : U.Normal := by
    rw [hUeq]
    exact BenderSuzuki.External.hktPResidual_normal
  let _ : U.Normal := hUnormal
  have hUquotient : IsPGroup 2 ((X ⧸ O) ⧸ U) := by
    let V : Subgroup (X ⧸ O) :=
      BenderSuzuki.External.hktPResidual 2 (X ⧸ O)
    have hVnormal : V.Normal :=
      BenderSuzuki.External.hktPResidual_normal
    let _ : V.Normal := hVnormal
    have hVquotient : IsPGroup 2 ((X ⧸ O) ⧸ V) :=
      BenderSuzuki.External.hktPResidual_quotient_isPGroup
    exact hVquotient.of_equiv
      (QuotientGroup.quotientMulEquivOfEq hUeq).symm
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := 2)).mp hUquotient
  have hUindex : U.index = 2 ^ n := by
    rw [Subgroup.index_eq_card]
    exact hn
  let M : Subgroup X := U.comap q
  have hMnormal : M.Normal := hUnormal.comap q
  have hMindex : M.index = 2 ^ n := by
    calc
      M.index = U.index := by
        simpa [M, q] using
          (Subgroup.index_comap_of_surjective U
            (QuotientGroup.mk'_surjective O))
      _ = 2 ^ n := hUindex
  have hRleM : R ≤ M := by
    rw [hR]
    exact sInf_le ⟨hMnormal, n, hMindex⟩
  rintro _ ⟨x, hx, rfl⟩
  exact hRleM hx

private theorem residual_quotient_is_odd_pGroup'
    {G : Type u} [Group G] [Finite G]
    (S : Subgroup G) (h : Hypotheses G S)
    (P : Subgroup G) (hP : P ∈ PSet (⊤ : Subgroup G) S)
    (hsolv : Group.IsSolvable P) :
    ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧
      IsPGroup p
        (((QuotientGroup.mk' (pCore 2 P)).comp
          (Subgroup.inclusion
            (show twoResidualAmbient P ≤ P from Subgroup.map_subtype_le _))).range) := by
  classical
  have hSleP : S ≤ P := by
    obtain ⟨SP, hSP⟩ := hP.1.2.1
    rw [← hSP]
    exact Subgroup.map_subtype_le (SP : Subgroup P)
  let SP : Subgroup P := S.subgroupOf P
  obtain ⟨B, hBcoatom, hSB, hBuniq⟩ := hP.2
  have hSPB : SP ≤ B := by
    intro x hx
    have hxS : (x : G) ∈ S := hx
    have hxmap : (x : G) ∈ B.map P.subtype := hSB hxS
    obtain ⟨b, hb, hbx⟩ := hxmap
    have : b = x := P.subtype_injective hbx
    simpa [this] using hb
  have hBuniq' : ∀ B' : Subgroup P, IsCoatom B' → SP ≤ B' → B' = B := by
    intro B' hB' hSPB'
    apply hBuniq B' hB'
    intro s hs
    obtain ⟨x, hx, rfl⟩ : ∃ x : P, x ∈ SP ∧ (x : G) = s := by
      exact ⟨⟨s, hSleP hs⟩, hs, rfl⟩
    exact Subgroup.mem_map_of_mem P.subtype (hSPB' hx)
  let P0 : Subgroup P := B.normalCore
  have hP0data : P0 ≤ B ∧ P0.Normal ∧
      ∀ M : Subgroup P, M.Normal → M ≤ B → M ≤ P0 := by
    refine ⟨B.normalCore_le, inferInstance, ?_⟩
    intro M hM hMB
    exact @Subgroup.normal_le_normalCore P _ B M hM |>.mpr hMB
  have h33 := lemma_three_three S h P hP B P0
    ⟨hBcoatom, hSPB, hBuniq'⟩ hP0data hsolv
  obtain ⟨p, hp, hodd, hpquot⟩ := h33.part_a
  let _ : Fact p.Prime := ⟨hp⟩
  let O : Subgroup P := pCore 2 P
  let RP : Subgroup P := twoResidualSubgroup P
  let R : Subgroup G := twoResidualAmbient P
  have hRPle : R ≤ P := Subgroup.map_subtype_le _
  let q : P →* P ⧸ O := QuotientGroup.mk' O
  let qR : R →* P ⧸ O := q.comp (Subgroup.inclusion hRPle)
  have hqRle : qR.range ≤
      twoResidualAmbient (⊤ : Subgroup (P ⧸ O)) := by
    change (q.comp (Subgroup.inclusion hRPle)).range ≤
      twoResidualAmbient (⊤ : Subgroup (P ⧸ O))
    rw [MonoidHom.range_comp]
    have hRsub : R.subgroupOf P = RP := by
      apply Subgroup.map_injective P.subtype_injective
      rw [Subgroup.map_subgroupOf_eq_of_le hRPle]
      rfl
    have hrange : (Subgroup.inclusion hRPle).range = R.subgroupOf P := by
      ext x
      simp
    rw [hrange, hRsub]
    simpa [q, O, RP] using
      twoResidualSubgroup_map_quotient_le' RP O rfl
  have hqRp : IsPGroup p qR.range :=
    isPGroup_subgroup_of_le' hpquot hqRle
  refine ⟨p, hp, ?_, ?_⟩
  · rcases hodd with ⟨m, hm⟩
    omega
  · simpa [qR, q, O, R] using hqRp

private theorem center_twoCore_centrality_descends_normal'
    {G : Type u} [Group G] [Finite G]
    (P R : Subgroup G) (hRP : R ≤ P)
    (p : ℕ) [Fact p.Prime] (hpne : p ≠ 2)
    (hqR : IsPGroup p
      ((QuotientGroup.mk' (pCore 2 P)).comp
        (Subgroup.inclusion hRP)).range)
    (K L : Subgroup G) (hKL : K ≤ L) (hLR : L ≤ R)
    (hKnormal : (K.subgroupOf L).Normal)
    (hupper :
      ⁅(Subgroup.center (twoCoreAmbient L)).map
        (twoCoreAmbient L).subtype, L⁆ = ⊥) :
    ⁅(Subgroup.center (twoCoreAmbient K)).map
      (twoCoreAmbient K).subtype, K⁆ = ⊥ := by
  classical
  let O : Subgroup P := pCore 2 P
  let q : P →* P ⧸ O := QuotientGroup.mk' O
  let ZK : Subgroup G := (Subgroup.center (twoCoreAmbient K)).map
    (twoCoreAmbient K).subtype
  let A : Subgroup G := ⁅ZK, K⁆
  have hKP : K ≤ P := hKL.trans (hLR.trans hRP)
  have hLP : L ≤ P := hLR.trans hRP
  have hZKleK : ZK ≤ K :=
    (Subgroup.map_subtype_le _).trans (Subgroup.map_subtype_le _)
  have hKnormZK : K ≤ Subgroup.normalizer (ZK : Set G) :=
    K.le_normalizer.trans (normalizer_le_normalizer_center_twoCoreAmbient' K)
  let _ : Subgroup.Normalizes K ZK := ⟨hKnormZK⟩
  let qK : K →* P ⧸ O := q.comp (Subgroup.inclusion hKP)
  let qR : R →* P ⧸ O := q.comp (Subgroup.inclusion hRP)
  have hqKle : qK.range ≤ qR.range := by
    rintro _ ⟨k, rfl⟩
    exact ⟨⟨k, hLR (hKL k.property)⟩, rfl⟩
  have hqKp : IsPGroup p qK.range :=
    isPGroup_subgroup_of_le' hqR hqKle
  let rho : K →* MulAut ZK := MulDistribMulAction.toMulAut K ZK
  let QK : Subgroup G := (twoCoreAmbient P) ⊓ K
  have hQKleK : QK ≤ K := inf_le_right
  have hOPnormalP : ((twoCoreAmbient P).subgroupOf P).Normal :=
    twoCoreAmbient_normal_subgroupOf' P
  have hQKnormal : (QK.subgroupOf K).Normal := by
    apply (Subgroup.normal_subgroupOf_iff hQKleK).mpr
    intro x k hx hk
    refine ⟨?_, K.mul_mem (K.mul_mem hk hx.2) (K.inv_mem hk)⟩
    exact (Subgroup.normal_subgroupOf_iff (Subgroup.map_subtype_le _)).mp
      hOPnormalP x k hx.1 (hKP hk)
  have hQKp : IsPGroup 2 QK :=
    (twoCoreAmbient_isPGroup' P).to_le inf_le_left
  have hQKcore : QK ≤ twoCoreAmbient K :=
    normal_pSubgroup_le_twoCoreAmbient' QK K hQKleK hQKp hQKnormal
  have hqker_rhoker : qK.ker ≤ rho.ker := by
    intro k hk
    rw [MonoidHom.mem_ker] at hk ⊢
    let kP : P := ⟨k, hKP k.property⟩
    have hkq : q kP = 1 := hk
    have hkO : kP ∈ O :=
      (QuotientGroup.eq_one_iff (N := O) kP).mp hkq
    have hkOamb : (k : G) ∈ twoCoreAmbient P :=
      Subgroup.mem_map_of_mem P.subtype hkO
    have hkcore : (k : G) ∈ twoCoreAmbient K :=
      hQKcore ⟨hkOamb, k.property⟩
    apply MulEquiv.ext
    intro z
    apply Subtype.ext
    obtain ⟨z0, hz0, hz⟩ := z.property
    have hkz : (k : G) * (z : G) = (z : G) * (k : G) := by
      let k0 : twoCoreAmbient K := ⟨k, hkcore⟩
      have h0 := (Subgroup.mem_center_iff.mp hz0) k0
      have hz' : (z0 : G) = (z : G) := hz
      calc
        (k : G) * (z : G) = (k : G) * (z0 : G) :=
          congrArg (fun x : G => (k : G) * x) hz'.symm
        _ = (z0 : G) * (k : G) :=
          congrArg (fun x : twoCoreAmbient K => (x : G)) h0
        _ = (z : G) * (k : G) :=
          congrArg (fun x : G => x * (k : G)) hz'
    change (k : G) * (z : G) * (k : G)⁻¹ = (z : G)
    rw [hkz, mul_inv_cancel_right]
  have hrhop : IsPGroup p rho.range :=
    isPGroup_range_of_ker_le_ker' qK rho hqKp hqker_rhoker
  have hZKtwo : IsPGroup 2 ZK := center_twoCoreAmbient_isPGroup' K
  have hcop : Nat.Coprime (Nat.card rho.range) (Nat.card ZK) := by
    simpa using IsPGroup.coprime_card_of_ne p 2 hpne
      (⊤ : Subgroup rho.range) (⊤ : Subgroup ZK)
      (hrhop.to_subgroup ⊤) (hZKtwo.to_subgroup ⊤)
  have hZKcomm : IsMulCommutative ZK := inferInstance
  have hZKsolv : Group.IsSolvable ZK := by
    let _ : IsMulCommutative ZK := hZKcomm
    infer_instance
  have hcompl : IsCompl (fixedPointSubgroup rho.range ZK)
      (commutatorAction (A := rho.range) (G := ZK)) :=
    isCompl_fixedPointSubgroup_commutatorAction_of_solvable_coprime_of_isMulCommutative
      hZKsolv hcop hZKcomm
  have hcommMap :
      (commutatorAction (A := K) (G := ZK)).map ZK.subtype = A := by
    simpa [A] using
      commutatorAction_subgroup_conj_map_eq_commutator ZK K hKnormZK
  have hcommRange : commutatorAction (A := rho.range) (G := ZK) =
      commutatorAction (A := K) (G := ZK) := by
    simpa [rho] using commutatorAction_range_toMulAut_eq' (X := ZK) (A := K)
  have hAleZK : A ≤ ZK :=
    (Subgroup.le_normalizer_iff_commutator_le_left.mp hKnormZK)
  have hAleK : A ≤ K := hAleZK.trans hZKleK
  have hAnormalL : (A.subgroupOf L).Normal := by
    simpa [A, ZK] using
      commutator_twoCore_center_normal_subgroupOf' K L hKL hKnormal
  have hAp : IsPGroup 2 A := hZKtwo.to_le hAleZK
  have hAleOL : A ≤ twoCoreAmbient L :=
    normal_pSubgroup_le_twoCoreAmbient' A L (hAleK.trans hKL) hAp hAnormalL
  by_contra hAne
  change A ≠ ⊥ at hAne
  have hALnormal : (A.subgroupOf (twoCoreAmbient L)).Normal := by
    apply (Subgroup.normal_subgroupOf_iff hAleOL).mpr
    intro a l ha hl
    exact (Subgroup.normal_subgroupOf_iff (hAleK.trans hKL)).mp hAnormalL
      a l ha (Subgroup.map_subtype_le _ hl)
  let AL : Subgroup (twoCoreAmbient L) := A.subgroupOf (twoCoreAmbient L)
  let _ : AL.Normal := hALnormal
  have hALne : AL ≠ ⊥ := by
    intro hbot
    apply hAne
    calc
      A = AL.map (twoCoreAmbient L).subtype :=
        (Subgroup.map_subgroupOf_eq_of_le hAleOL).symm
      _ = ⊥ := by rw [hbot, Subgroup.map_bot]
  let _ : Fact (IsPGroup 2 (twoCoreAmbient L)) :=
    ⟨twoCoreAmbient_isPGroup' L⟩
  obtain ⟨z, hzA, hzcenter, hzne, _⟩ :=
    exists_nontrivial_mem_center_of_normal_p_subgroup
      (G := twoCoreAmbient L) (p := 2) AL hALne
  have hzAamb : (z : G) ∈ A := hzA
  have hzZK : (z : G) ∈ ZK := hAleZK hzAamb
  let zK : ZK := ⟨z, hzZK⟩
  have hzfix : zK ∈ fixedPointSubgroup rho.range ZK := by
    rw [FixedPoints.mem_subgroup]
    rintro ⟨_, k, rfl⟩
    apply Subtype.ext
    have hzZL : (z : G) ∈
        (Subgroup.center (twoCoreAmbient L)).map
          (twoCoreAmbient L).subtype :=
      Subgroup.mem_map_of_mem (twoCoreAmbient L).subtype hzcenter
    have hzk : (z : G) * (k : G) = (k : G) * (z : G) :=
      ((Subgroup.commutator_eq_bot_iff_le_centralizer.mp hupper hzZL)
        k (hKL k.property)).symm
    change (k : G) * (z : G) * (k : G)⁻¹ = (z : G)
    rw [← hzk, mul_inv_cancel_right]
  have hzcommK : zK ∈ commutatorAction (A := K) (G := ZK) := by
    have hzmap : (z : G) ∈
        (commutatorAction (A := K) (G := ZK)).map ZK.subtype := by
      rw [hcommMap]
      exact hzAamb
    obtain ⟨y, hy, hyz⟩ := hzmap
    have hyEq : y = zK := ZK.subtype_injective hyz
    simpa [hyEq] using hy
  have hzcomm : zK ∈ commutatorAction (A := rho.range) (G := ZK) := by
    rw [hcommRange]
    exact hzcommK
  have hzbot : zK ∈ (⊥ : Subgroup ZK) := hcompl.disjoint.le_bot ⟨hzfix, hzcomm⟩
  have hzone : zK = 1 := by simpa using hzbot
  apply hzne
  apply (twoCoreAmbient L).subtype_injective
  exact congrArg (fun x : ZK => ((x : ZK) : G)) hzone

/-- The (3.5) consequence used in assertion (7) of Stellmacher (5.2). -/
public theorem subnormal_twoCore_center_centralizes_of_residual_omega_central
    {G : Type u} [Group G] [Finite G]
    (S : Subgroup G) (h : Hypotheses G S)
    (P : Subgroup G) (hP : P ∈ PSet (⊤ : Subgroup G) S)
    (hsolv : Group.IsSolvable P)
    (hOmega : ⁅omegaOneCenterAmbient S, twoResidualAmbient P⁆ = ⊥)
    (K : Subgroup G)
    (hKsub : IsSubnormalIn K (twoResidualAmbient P)) :
    ⁅(Subgroup.center (twoCoreAmbient K)).map
      (twoCoreAmbient K).subtype, K⁆ = ⊥ := by
  classical
  let R : Subgroup G := twoResidualAmbient P
  have hRP : R ≤ P := Subgroup.map_subtype_le _
  obtain ⟨p, hp, hpne, hqRp⟩ :=
    residual_quotient_is_odd_pGroup' S h P hP hsolv
  let _ : Fact p.Prime := ⟨hp⟩
  have htop :
      ⁅(Subgroup.center (twoCoreAmbient R)).map
        (twoCoreAmbient R).subtype, R⁆ = ⊥ := by
    simpa [R] using
      residual_twoCore_center_centralizes' S h P hP hsolv hOmega
  let Goal : Subgroup R → Prop := fun A =>
    ⁅(Subgroup.center (twoCoreAmbient (A.map R.subtype))).map
        (twoCoreAmbient (A.map R.subtype)).subtype,
      A.map R.subtype⁆ = ⊥
  have hrec : ∀ A : Subgroup R, A.IsSubnormal → Goal A := by
    intro A hA
    induction hA with
    | top =>
        have hmapTop : (⊤ : Subgroup R).map R.subtype = R := by
          simpa [MonoidHom.range_eq_map] using Subgroup.range_subtype R
        dsimp [Goal]
        rw [hmapTop]
        exact htop
    | step H L hHL hLsub hHnormal ih =>
        have hmapNormal :
            ((H.map R.subtype).subgroupOf (L.map R.subtype)).Normal := by
          rw [Subgroup.normal_subgroupOf_iff_le_normalizer hHL] at hHnormal
          rw [Subgroup.normal_subgroupOf_iff_le_normalizer
            (Subgroup.map_mono hHL)]
          exact (Subgroup.map_mono hHnormal).trans
            (Subgroup.le_normalizer_map R.subtype)
        exact center_twoCore_centrality_descends_normal'
          P R hRP p hpne hqRp
          (H.map R.subtype) (L.map R.subtype)
          (Subgroup.map_mono hHL) (Subgroup.map_subtype_le L)
          hmapNormal ih
  have hgoal := hrec (K.subgroupOf R) hKsub.2
  have hmap : (K.subgroupOf R).map R.subtype = K :=
    Subgroup.map_subgroupOf_eq_of_le hKsub.1
  dsimp [Goal] at hgoal
  rw [hmap] at hgoal
  exact hgoal

end Stellmacher.SectionThree
