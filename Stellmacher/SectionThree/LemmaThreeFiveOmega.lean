module

public import Stellmacher.SectionThree.LemmaThreeThree
public import Theory.GroupAction.CoprimeHall
public import FeitThompson.BGsection1.theorem_1_13

/-!
# Stellmacher (3.5): the omega-center commutator dichotomy

Let `P ∈ ℘(S)` be solvable and let `N ◁ P` lie in `O₂(P)`.  If `N`
centralizes `O₂(P) ∩ O²(P)`, then either `Ω₁(Z(S))` does not centralize
`O²(P)`, or `N` does.

The proof follows Stellmacher's Maschke argument.  Put
`K = [N, O²(P)]`.  The centralizer hypothesis makes `K` abelian.  Lemma
(3.3) says that the image of `O²(P)` modulo `O₂(P)` is an odd-prime
group, so its effective conjugation actions on `N` and `K` are coprime.
Coprime action gives `[K, O²(P)] = K` and `C_K(O²(P)) = 1`.  If `K`
is nontrivial, its normality in the Sylow two-subgroup `S` supplies a
nontrivial element of order two in `K ∩ Z(S)`, forcing the first alternative.
This strengthens the printed center alternative to the omega-center form used
in (7.6); the original public theorem follows by commutator monotonicity.

Source: B. Stellmacher, *An Application of the Amalgam Method: The 2-Local
Structure of N-Groups of Characteristic 2 Type*, Journal of Algebra 190
(1997), Lemma (3.5), p. 22; see also
`refs/latex/stellmacher-n-group.tex`.
-/

namespace Stellmacher.SectionThree

open scoped IsMulCommutative commutatorElement

universe u

private theorem commutatorAction_range_toMulAut_eq
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

private theorem commutatorAction₂_range_toMulAut_eq
    {X A : Type*} [Group X] [Group A] [MulDistribMulAction A X] :
    let rho : A →* MulAut X := MulDistribMulAction.toMulAut A X
    commutatorAction₂ (A := rho.range) (G := X) =
      commutatorAction₂ (A := A) (G := X) := by
  classical
  let rho : A →* MulAut X := MulDistribMulAction.toMulAut A X
  have hfirst :
      commutatorAction (A := rho.range) (G := X) =
        commutatorAction (A := A) (G := X) := by
    simpa [rho] using commutatorAction_range_toMulAut_eq (X := X) (A := A)
  change
    Subgroup.closure
        {x : X | ∃ a : rho.range, ∃ g : X,
          g ∈ commutatorAction (A := rho.range) (G := X) ∧
            x = g⁻¹ * (a • g)} =
      Subgroup.closure
        {x : X | ∃ a : A, ∃ g : X,
          g ∈ commutatorAction (A := A) (G := X) ∧
            x = g⁻¹ * (a • g)}
  congr 1
  ext x
  constructor
  · rintro ⟨b, y, hy, rfl⟩
    rcases b with ⟨_, a, rfl⟩
    refine ⟨a, y, ?_, ?_⟩
    · simpa [hfirst] using hy
    · have hsmul : (⟨rho a, ⟨a, rfl⟩⟩ : rho.range) • y = a • y := rfl
      rw [hsmul]
  · rintro ⟨a, y, hy, rfl⟩
    refine ⟨⟨rho a, ⟨a, rfl⟩⟩, y, ?_, ?_⟩
    · simpa [hfirst] using hy
    · simp [rho, MulDistribMulAction.toMulAut_apply]

private theorem commutatorAction₂_subgroup_conj_map_eq
    {X : Type*} [Group X] (N R : Subgroup X)
    (hRnormN : R ≤ Subgroup.normalizer N) :
    have : Subgroup.Normalizes R N := ⟨hRnormN⟩
    (commutatorAction₂ (A := R) (G := N)).map N.subtype =
      ⁅⁅N, R⁆, R⁆ := by
  classical
  let _ : Subgroup.Normalizes R N := ⟨hRnormN⟩
  let C : Subgroup N := commutatorAction (A := R) (G := N)
  let SC : Set N :=
    {x : N | ∃ r : R, ∃ n : N, n ∈ C ∧ x = n⁻¹ * (r • n)}
  let SX : Set X :=
    {x : X | ∃ r : R, ∃ n : N, n ∈ C ∧
      x = ⁅((n : X))⁻¹, (r : X)⁆}
  let SK : Set X :=
    {x : X | ∃ k ∈ ⁅N, R⁆, ∃ r ∈ R, ⁅k, r⁆ = x}
  have hCmap : C.map N.subtype = ⁅N, R⁆ := by
    simpa [C] using commutatorAction_subgroup_conj_map_eq_commutator N R hRnormN
  have himage : N.subtype '' SC = SX := by
    ext x
    constructor
    · rintro ⟨y, ⟨r, n, hn, rfl⟩, rfl⟩
      refine ⟨r, n, hn, ?_⟩
      simp [Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe,
        commutatorElement_def, mul_assoc]
    · rintro ⟨r, n, hn, rfl⟩
      refine ⟨n⁻¹ * (r • n), ⟨r, n, hn, rfl⟩, ?_⟩
      simp [Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe,
        commutatorElement_def, mul_assoc]
  have hsets : SX = SK := by
    ext x
    constructor
    · rintro ⟨r, n, hn, rfl⟩
      have hnmap : (n : X) ∈ ⁅N, R⁆ := by
        rw [← hCmap]
        exact Subgroup.mem_map_of_mem N.subtype hn
      exact ⟨(n : X)⁻¹, (⁅N, R⁆).inv_mem hnmap,
        (r : X), r.2, by simp⟩
    · rintro ⟨k, hk, r, hr, rfl⟩
      rw [← hCmap] at hk
      obtain ⟨n, hn, hnk⟩ := hk
      refine ⟨⟨r, hr⟩, n⁻¹, C.inv_mem hn, ?_⟩
      have hnk' : (n : X) = k := hnk
      subst k
      simp
  calc
    (commutatorAction₂ (A := R) (G := N)).map N.subtype
        = (Subgroup.closure SC).map N.subtype := by
            rfl
    _ = Subgroup.closure (N.subtype '' SC) := by
          simpa using MonoidHom.map_closure N.subtype SC
    _ = Subgroup.closure SX := by rw [himage]
    _ = Subgroup.closure SK := by rw [hsets]
    _ = ⁅⁅N, R⁆, R⁆ := by
          simp [SK, Subgroup.commutator_def]

private theorem twoResidualSubgroup_normal
    {X : Type*} [Group X] (P : Subgroup X) :
    (twoResidualSubgroup P).Normal := by
  unfold twoResidualSubgroup
  rw [sInf_eq_iInf]
  exact Subgroup.normal_iInf_normal (fun N =>
    Subgroup.normal_iInf_normal (fun hN => hN.1))

private theorem twoResidualSubgroup_map_quotient_le
    {X : Type*} [Group X] [Finite X]
    (R O : Subgroup X) [O.Normal]
    (hR : R = sInf {N : Subgroup X | N.Normal ∧ ∃ n : ℕ, N.index = 2 ^ n})
    :
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

private theorem isPGroup_range_of_ker_le_ker
    {A Q B : Type*} [Group A] [Finite A] [Group Q] [Finite Q]
    [Group B] [Finite B]
    {p : ℕ} [Fact p.Prime] (q : A →* Q) (rho : A →* B)
    (hq : IsPGroup p q.range) (hker : q.ker ≤ rho.ker) :
    IsPGroup p rho.range := by
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := p)).mp hq
  apply IsPGroup.of_card_dvd_pow (n := n)
  rw [← Subgroup.index_ker rho, ← hn, ← Subgroup.index_ker q]
  exact Subgroup.index_dvd_of_le hker

private theorem isPGroup_subgroup_of_le
    {X : Type*} [Group X] {p : ℕ} {U V : Subgroup X}
    (hV : IsPGroup p V) (hUV : U ≤ V) : IsPGroup p U := by
  exact hV.of_injective (Subgroup.inclusion hUV) (Subgroup.inclusion_injective hUV)

/-! **Stellmacher (3.5).** -/
public theorem lemma_three_five_omega
    {G : Type u} [Group G] [Finite G]
    (S : Subgroup G) (h : Hypotheses G S)
    (P : Subgroup G) (hP : P ∈ PSet (⊤ : Subgroup G) S)
    (N : Subgroup G)
    (hN : N ≤ P ∧ N ≤ twoCoreAmbient P ∧ (N.subgroupOf P).Normal)
    (hsolv : Group.IsSolvable P)
    (hcentral : ⁅N, twoCoreAmbient P ⊓ twoResidualAmbient P⁆ = ⊥) :
    ⁅omegaOneCenterAmbient S, twoResidualAmbient P⁆ ≠ ⊥ ∨
      ⁅N, twoResidualAmbient P⁆ = ⊥ := by
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
    have hbeq : b = x := P.subtype_injective hbx
    simpa [hbeq] using hb
  have hBuniq' : ∀ B' : Subgroup P, IsCoatom B' → SP ≤ B' → B' = B := by
    intro B' hB' hSPB'
    apply hBuniq B' hB'
    intro s hs
    obtain ⟨x, hx, rfl⟩ : ∃ x : P, x ∈ SP ∧ (x : G) = s := by
      exact ⟨⟨s, hSleP hs⟩, hs, rfl⟩
    exact Subgroup.mem_map_of_mem P.subtype (hSPB' hx)
  let P₀ : Subgroup P := B.normalCore
  have hP₀data : P₀ ≤ B ∧ P₀.Normal ∧
      ∀ M : Subgroup P, M.Normal → M ≤ B → M ≤ P₀ := by
    refine ⟨B.normalCore_le, inferInstance, ?_⟩
    intro M hM hMB
    exact @Subgroup.normal_le_normalCore P _ B M hM |>.mpr hMB
  have h33 := lemma_three_three S h P hP B P₀
    ⟨hBcoatom, hSPB, hBuniq'⟩ hP₀data hsolv
  obtain ⟨p, hp, hodd, hpquot⟩ := h33.part_a
  let _ : Fact p.Prime := ⟨hp⟩
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

  let O : Subgroup P := pCore 2 P
  let R : Subgroup P := twoResidualSubgroup P
  let NP : Subgroup P := N.subgroupOf P
  have hNPmap : NP.map P.subtype = N := by
    exact Subgroup.map_subgroupOf_eq_of_le hN.1
  have hOmap : O.map P.subtype = twoCoreAmbient P := by
    rfl
  have hRmap : R.map P.subtype = twoResidualAmbient P := by
    rfl
  have hNPnormal : NP.Normal := hN.2.2
  let _ : NP.Normal := hNPnormal
  have hRnormal : R.Normal := twoResidualSubgroup_normal P
  let _ : R.Normal := hRnormal
  have hNPleO : NP ≤ O := by
    intro x hx
    have hxN : (x : G) ∈ N := hx
    have hxcore : (x : G) ∈ O.map P.subtype := by
      rw [hOmap]
      exact hN.2.1 hxN
    obtain ⟨y, hy, hyx⟩ := hxcore
    have : y = x := P.subtype_injective hyx
    simpa [this] using hy
  have hcentralP : ⁅NP, O ⊓ R⁆ = ⊥ := by
    apply (Subgroup.map_eq_bot_iff_of_injective
      (H := ⁅NP, O ⊓ R⁆) P.subtype_injective).mp
    calc
      (⁅NP, O ⊓ R⁆ : Subgroup P).map P.subtype
          = ⁅N, twoCoreAmbient P ⊓ twoResidualAmbient P⁆ := by
              rw [Subgroup.map_commutator, Subgroup.map_inf _ _ _
                P.subtype_injective, hNPmap, hOmap, hRmap]
      _ = ⊥ := hcentral
  let K : Subgroup P := ⁅NP, R⁆
  have hKleNP : K ≤ NP := by
    exact (Subgroup.commutator_le_inf NP R).trans inf_le_left
  have hKleR : K ≤ R := by
    exact (Subgroup.commutator_le_inf NP R).trans inf_le_right
  have hKleOR : K ≤ O ⊓ R := le_inf (hKleNP.trans hNPleO) hKleR
  have hKcomm : ⁅K, K⁆ = ⊥ := by
    apply le_bot_iff.mp
    exact (Subgroup.commutator_mono hKleNP hKleOR).trans (le_of_eq hcentralP)
  have hKab : IsMulCommutative K :=
    Subgroup.commutator_self_eq_bot_iff.mp hKcomm
  let q : P →* P ⧸ O := QuotientGroup.mk' O
  let qR : R →* P ⧸ O := q.comp R.subtype
  have hqRle : qR.range ≤
      twoResidualAmbient (⊤ : Subgroup (P ⧸ O)) := by
    change (q.comp R.subtype).range ≤
      twoResidualAmbient (⊤ : Subgroup (P ⧸ O))
    rw [MonoidHom.range_comp]
    simpa [q] using twoResidualSubgroup_map_quotient_le R O rfl
  have hqRp : IsPGroup p qR.range :=
    isPGroup_subgroup_of_le hpquot hqRle
  let rho : R →* MulAut NP := MulDistribMulAction.toMulAut R NP
  have hqker_rhoker : qR.ker ≤ rho.ker := by
    intro r hr
    rw [MonoidHom.mem_ker] at hr ⊢
    have hrO : (r : P) ∈ O := by
      exact (QuotientGroup.eq_one_iff (N := O) (r : P)).mp hr
    apply MulEquiv.ext
    intro n
    apply Subtype.ext
    have hcomm_mem : ⁅(n : P), (r : P)⁆ ∈ ⁅NP, O ⊓ R⁆ :=
      Subgroup.commutator_mem_commutator n.property ⟨hrO, r.property⟩
    rw [hcentralP] at hcomm_mem
    have hcomm : ⁅(n : P), (r : P)⁆ = 1 := by simpa using hcomm_mem
    have hnr : (n : P) * (r : P) = (r : P) * (n : P) :=
      commutatorElement_eq_one_iff_mul_comm.mp hcomm
    change (r : P) * (n : P) * (r : P)⁻¹ = (n : P)
    rw [← hnr, mul_inv_cancel_right]
  have hrhop : IsPGroup p rho.range :=
    isPGroup_range_of_ker_le_ker qR rho hqRp hqker_rhoker
  have hNPtwo : IsPGroup 2 NP :=
    isPGroup_subgroup_of_le (pCore_isPGroup (p := 2) (G := P)) hNPleO
  have hpne : p ≠ 2 := by
    rcases hodd with ⟨m, hm⟩
    omega
  have hcoprho : Nat.Coprime (Nat.card rho.range) (Nat.card NP) := by
    simpa using
      IsPGroup.coprime_card_of_ne p 2 hpne
        (⊤ : Subgroup rho.range) (⊤ : Subgroup NP)
        (hrhop.to_subgroup ⊤) (hNPtwo.to_subgroup ⊤)
  have hactionNP :
      commutatorAction₂ (A := R) (G := NP) =
        commutatorAction (A := R) (G := NP) := by
    calc
      commutatorAction₂ (A := R) (G := NP) =
          commutatorAction₂ (A := rho.range) (G := NP) := by
            symm
            simpa [rho] using
              commutatorAction₂_range_toMulAut_eq (X := NP) (A := R)
      _ = commutatorAction (A := rho.range) (G := NP) :=
        commutatorAction₂_eq_commutatorAction_of_coprime hcoprho
      _ = commutatorAction (A := R) (G := NP) := by
        simpa [rho] using
          commutatorAction_range_toMulAut_eq (X := NP) (A := R)
  have hRnormNP : R ≤ Subgroup.normalizer NP :=
    Subgroup.le_normalizer_of_normal
  have hKR : ⁅K, R⁆ = K := by
    have hmapped := congrArg (fun H : Subgroup NP => H.map NP.subtype) hactionNP
    have hsecond :
        (commutatorAction₂ (A := R) (G := NP)).map NP.subtype = ⁅K, R⁆ := by
      simpa [K] using
        commutatorAction₂_subgroup_conj_map_eq NP R hRnormNP
    have hfirst :
        (commutatorAction (A := R) (G := NP)).map NP.subtype = K := by
      simpa [K] using
        commutatorAction_subgroup_conj_map_eq_commutator NP R hRnormNP
    exact hsecond.symm.trans (hmapped.trans hfirst)
  have hKnormal : K.Normal := inferInstance
  let _ : K.Normal := hKnormal
  let sigma : R →* MulAut K := MulDistribMulAction.toMulAut R K
  have hqker_sigmaker : qR.ker ≤ sigma.ker := by
    intro r hr
    rw [MonoidHom.mem_ker] at hr ⊢
    have hrO : (r : P) ∈ O :=
      (QuotientGroup.eq_one_iff (N := O) (r : P)).mp hr
    apply MulEquiv.ext
    intro k
    apply Subtype.ext
    have hcomm_mem : ⁅(k : P), (r : P)⁆ ∈ ⁅NP, O ⊓ R⁆ :=
      Subgroup.commutator_mem_commutator (hKleNP k.property) ⟨hrO, r.property⟩
    rw [hcentralP] at hcomm_mem
    have hcomm : ⁅(k : P), (r : P)⁆ = 1 := by simpa using hcomm_mem
    have hkr : (k : P) * (r : P) = (r : P) * (k : P) :=
      commutatorElement_eq_one_iff_mul_comm.mp hcomm
    change (r : P) * (k : P) * (r : P)⁻¹ = (k : P)
    rw [← hkr, mul_inv_cancel_right]
  have hsigmap : IsPGroup p sigma.range :=
    isPGroup_range_of_ker_le_ker qR sigma hqRp hqker_sigmaker
  have hKtwo : IsPGroup 2 K :=
    isPGroup_subgroup_of_le (pCore_isPGroup (p := 2) (G := P))
      (hKleNP.trans hNPleO)
  have hcopsigma : Nat.Coprime (Nat.card sigma.range) (Nat.card K) := by
    simpa using
      IsPGroup.coprime_card_of_ne p 2 hpne
        (⊤ : Subgroup sigma.range) (⊤ : Subgroup K)
        (hsigmap.to_subgroup ⊤) (hKtwo.to_subgroup ⊤)
  have hRnormK : R ≤ Subgroup.normalizer K :=
    Subgroup.le_normalizer_of_normal
  have hcommKmap :
      (commutatorAction (A := R) (G := K)).map K.subtype = K := by
    calc
      (commutatorAction (A := R) (G := K)).map K.subtype = ⁅K, R⁆ :=
        commutatorAction_subgroup_conj_map_eq_commutator K R hRnormK
      _ = K := hKR
  have hcommKtop : commutatorAction (A := R) (G := K) = ⊤ := by
    apply top_unique
    intro k _
    have hkmap : (k : P) ∈
        (commutatorAction (A := R) (G := K)).map K.subtype := by
      rw [hcommKmap]
      exact k.property
    obtain ⟨x, hx, hxk⟩ := hkmap
    have : x = k := K.subtype_injective hxk
    simpa [this] using hx
  have hcommKrange :
      commutatorAction (A := sigma.range) (G := K) = ⊤ := by
    rw [commutatorAction_range_toMulAut_eq (X := K) (A := R)]
    exact hcommKtop
  have hKsolv : Group.IsSolvable K := by
    let _ : IsMulCommutative K := hKab
    infer_instance
  have hcompl : IsCompl (fixedPointSubgroup sigma.range K)
      (commutatorAction (A := sigma.range) (G := K)) :=
    isCompl_fixedPointSubgroup_commutatorAction_of_solvable_coprime_of_isMulCommutative
      hKsolv hcopsigma hKab
  have hfixedbot : fixedPointSubgroup sigma.range K = ⊥ := by
    have hinter := hcompl.inf_eq_bot
    rw [hcommKrange, inf_top_eq] at hinter
    exact hinter
  have hKmapG : K.map P.subtype = ⁅N, twoResidualAmbient P⁆ := by
    calc
      K.map P.subtype =
          ⁅NP.map P.subtype, R.map P.subtype⁆ := by
            simpa [K] using
              (Subgroup.map_commutator NP R P.subtype)
      _ = ⁅N, twoResidualAmbient P⁆ := by rw [hNPmap, hRmap]
  by_cases hKbot : K = ⊥
  · right
    rw [← hKmapG, hKbot]
    simp
  · left
    intro hcenterbot
    obtain ⟨T, hTmap⟩ := hP.1.2.1
    have hOleT : O ≤ (T : Subgroup P) :=
      IsPGroup.le_sylow_of_normal
        (pCore_isPGroup (p := 2) (G := P)) T
    let KG : Subgroup G := K.map P.subtype
    have hKGleS : KG ≤ S := by
      intro x hx
      obtain ⟨k, hk, rfl⟩ := hx
      rw [← hTmap]
      exact Subgroup.mem_map_of_mem P.subtype
        (hOleT (hKleNP.trans hNPleO hk))
    have hKGne : KG ≠ ⊥ := by
      intro hbot
      apply hKbot
      exact (Subgroup.map_eq_bot_iff_of_injective
        (H := K) P.subtype_injective).mp hbot
    let KS : Subgroup S := KG.subgroupOf S
    have hKSnormal : KS.Normal := by
      apply (Subgroup.normal_subgroupOf_iff_le_normalizer hKGleS).mpr
      rw [Subgroup.le_normalizer_iff]
      intro s hs x hx
      obtain ⟨k, hk, hkx⟩ := hx
      let sP : P := ⟨s, hSleP hs⟩
      refine ⟨sP * k * sP⁻¹, hKnormal.conj_mem k hk sP, ?_⟩
      simpa [sP, mul_assoc] using
        congrArg (fun y : G => s * y * s⁻¹) hkx
    let _ : KS.Normal := hKSnormal
    have hKSne : KS ≠ ⊥ := by
      intro hbot
      apply hKGne
      have hmapKS : KS.map S.subtype = KG := by
        simpa [KS] using Subgroup.map_subgroupOf_eq_of_le hKGleS
      rw [← hmapKS, hbot]
      simp
    let _ : Fact (IsPGroup 2 S) := ⟨h.nontrivial_two_subgroup.2⟩
    obtain ⟨z, hzKS, hzcenter, hzne, hzpow⟩ :=
      exists_nontrivial_mem_center_of_normal_p_subgroup
        (G := S) (p := 2) KS hKSne
    have hzKG : (z : G) ∈ KG := hzKS
    obtain ⟨k, hk, hkz⟩ := hzKG
    let kK : K := ⟨k, hk⟩
    have hzcenterG : (z : G) ∈ omegaOneCenterAmbient S := by
      let zZ : Subgroup.center S := ⟨z, hzcenter⟩
      have hzOmega : zZ ∈ omega₁ (G := Subgroup.center S) (p := 2) := by
        change zZ ∈ Subgroup.closure {y : Subgroup.center S | y ^ (2 ^ 1) = 1}
        apply Subgroup.subset_closure
        apply Subtype.ext
        simpa [zZ] using hzpow
      exact Subgroup.mem_map_of_mem S.subtype
        (Subgroup.mem_map_of_mem (Subgroup.center S).subtype hzOmega)
    have hkfix : kK ∈ fixedPointSubgroup sigma.range K := by
      rw [FixedPoints.mem_subgroup]
      intro a
      rcases a with ⟨_, r, rfl⟩
      have hrG : ((r : R) : P) ∈ R := r.property
      have hrmap : (((r : R) : P) : G) ∈ twoResidualAmbient P := by
        rw [← hRmap]
        exact Subgroup.mem_map_of_mem P.subtype hrG
      have hcomm_mem : ⁅(z : G), (((r : R) : P) : G)⁆ ∈
          ⁅omegaOneCenterAmbient S, twoResidualAmbient P⁆ :=
        Subgroup.commutator_mem_commutator hzcenterG hrmap
      rw [hcenterbot] at hcomm_mem
      have hcomm : ⁅(z : G), (((r : R) : P) : G)⁆ = 1 := by
        simpa using hcomm_mem
      have hzr : (z : G) * (((r : R) : P) : G) =
          (((r : R) : P) : G) * (z : G) :=
        commutatorElement_eq_one_iff_mul_comm.mp hcomm
      have hkr : (k : P) * ((r : R) : P) =
          ((r : R) : P) * (k : P) := by
        have hkzG : ((k : P) : G) = (z : G) := hkz
        apply P.subtype_injective
        calc
          ((k : P) : G) * (((r : R) : P) : G) =
              (z : G) * (((r : R) : P) : G) :=
                congrArg (fun x : G => x * (((r : R) : P) : G)) hkzG
          _ = (((r : R) : P) : G) * (z : G) := hzr
          _ = (((r : R) : P) : G) * ((k : P) : G) :=
            congrArg (fun x : G => (((r : R) : P) : G) * x) hkzG.symm
      apply Subtype.ext
      change ((r : R) : P) * (k : P) * ((r : R) : P)⁻¹ = (k : P)
      rw [← hkr, mul_inv_cancel_right]
    have hkbot : kK ∈ (⊥ : Subgroup K) := by
      rw [← hfixedbot]
      exact hkfix
    have hkone : kK = 1 := by simpa using hkbot
    apply hzne
    apply S.subtype_injective
    calc
      (z : G) = (k : G) := hkz.symm
      _ = ((kK : K) : P) := rfl
      _ = 1 := congrArg (fun x : K => (((x : K) : P) : G)) hkone

end Stellmacher.SectionThree

