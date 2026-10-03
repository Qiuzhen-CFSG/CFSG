module

public import Stellmacher.SectionFiveToSeven.FiveTwoQuotientNormalizer
public import Stellmacher.SectionFiveToSeven.FiveTwoMinimalBad
public import FeitThompson.Fitting.Centralizer
public import FeitThompson.PCore.Nilpotent
public import Theory.GroupTheory.PGroup.SubnormalCore
public import Theory.GroupTheory.SylowNormalCoprimeSupplement

/-!
# The quotient two-core in the source Sylow image for Stellmacher (5.2)

Let `C0 ◁ M`, put `Mbar = M / C0`, and let `Wbar = O₂(Mbar)`.
This module proves the source step placing `Wbar` in the image of the chosen
2-subgroup `T`. Its hypotheses expose exactly the facts already constructed
in (5.2): subnormality of `K` in `K C0` and in every relevant proper
subgroup, the odd-prime structure of `K / O₂(K)`, normalization by `B`,
and the quotient normalizer statement for `Wbar`.

The proof pulls `Wbar` back to `M`. Subnormal p-core monotonicity gives
`O₂(K) ∩ W ≤ O₂(W) ≤ O₂(M) ≤ C0`; the odd index of `O₂(K)` then yields
`Kbar ∩ Wbar = 1`. The corrected odd Fitting factor
`O_{2'}(F(Mbar))` cannot centralize `O₂(Kbar)`, since otherwise Fitting
self-centralization and nilpotence put this nontrivial 2-subgroup in
`Kbar ∩ Wbar`. Assertion (6) therefore forces the odd Fitting factor,
`Kbar`, and `Bbar` to generate `Mbar`. Finally a relative-index
calculation and the normal coprime supplement theorem extend the Sylow
2-subgroup of `Kbar Bbar` to `Mbar`, giving `Wbar ≤ q(T)`.

This is the paragraph beginning with `Mbar = M/C0` in Stellmacher, Journal
of Algebra 190 (1997), Lemma (5.2), p. 29. The journal scan has
`O_{2'}(F(Mbar))`; the LaTeX transcription loses the prime.
-/

open scoped Pointwise

namespace Stellmacher.SectionsFiveToSeven

universe u

private theorem normal_pSubgroup_le_twoCoreIn_qci
    {G : Type u} [Group G] [Finite G]
    (Q K : Subgroup G) (hQK : Q ≤ K) (hQp : IsPGroup 2 Q)
    (hQnormal : (Q.subgroupOf K).Normal) :
    Q ≤ twoCoreIn K := by
  have hQpK : IsPGroup 2 (Q.subgroupOf K) :=
    hQp.of_equiv (Subgroup.subgroupOfEquivOfLe hQK).symm
  have hle : Q.subgroupOf K ≤ pCore 2 K := le_sSup ⟨hQnormal, hQpK⟩
  calc
    Q = (Q.subgroupOf K).map K.subtype :=
      (Subgroup.map_subgroupOf_eq_of_le hQK).symm
    _ ≤ (pCore 2 K).map K.subtype := Subgroup.map_mono hle
    _ = twoCoreIn K := rfl

private theorem twoCoreIn_isPGroup_qci
    {G : Type u} [Group G] [Finite G] (K : Subgroup G) :
    IsPGroup 2 (twoCoreIn K) :=
  (pCore_isPGroup (G := K) (p := 2)).map K.subtype

private theorem twoCoreIn_normalIn_qci
    {G : Type u} [Group G] (K : Subgroup G) :
    (twoCoreIn K).subgroupOf K |>.Normal := by
  change (Subgroup.comap K.subtype ((pCore 2 K).map K.subtype)).Normal
  rw [Subgroup.comap_map_eq_self_of_injective K.subtype_injective]
  infer_instance

private theorem twoCoreIn_top_qci
    {G : Type u} [Group G] :
    twoCoreIn (⊤ : Subgroup G) = pCore 2 G := by
  unfold twoCoreIn
  have htop : (⊤ : Subgroup G).subtype =
      (Subgroup.topEquiv : (⊤ : Subgroup G) ≃* G).toMonoidHom := by
    ext x
    rfl
  rw [htop]
  exact pCore_map_iso 2 (Subgroup.topEquiv : (⊤ : Subgroup G) ≃* G)

private theorem oddFitting_normal_qci
    {G : Type u} [Group G] [Finite G] :
    ((pPrimeCore 2 (fittingSubgroup G)).map
      (fittingSubgroup G).subtype : Subgroup G).Normal := by
  infer_instance

private theorem oddFitting_isOdd_qci
    {G : Type u} [Group G] [Finite G] :
    ¬ 2 ∣ Nat.card ((pPrimeCore 2 (fittingSubgroup G)).map
      (fittingSubgroup G).subtype : Subgroup G) := by
  rw [Subgroup.card_map_of_injective (fittingSubgroup G).subtype_injective]
  exact Nat.prime_two.coprime_iff_not_dvd.mp
    (pPrimeCore_coprime_card (G := fittingSubgroup G) (p := 2))

private theorem fitting_le_twoCore_sup_oddFitting_qci
    {G : Type u} [Group G] [Finite G] :
    fittingSubgroup G ≤ pCore 2 G ⊔
      (pPrimeCore 2 (fittingSubgroup G)).map
        (fittingSubgroup G).subtype := by
  let Fit : Subgroup G := fittingSubgroup G
  have hgen := nilpotent_top_le_pCore_sup_pPrimeCore
    (Q := Fit) (p := 2) (inferInstance : Group.IsNilpotent Fit)
  have hm := Subgroup.map_mono (f := Fit.subtype) hgen
  rw [Subgroup.map_sup] at hm
  have htopMap : (⊤ : Subgroup Fit).map Fit.subtype = Fit := by
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  rw [htopMap] at hm
  apply hm.trans
  apply sup_le_sup_right
  exact le_sSup ⟨(by infer_instance),
    (pCore_isPGroup (G := Fit) (p := 2)).map Fit.subtype⟩

private theorem relIndex_map_dvd_relIndex_qci
    {G G' : Type*} [Group G] [Group G'] [Finite G]
    (f : G →* G') (A K : Subgroup G) (hAK : A ≤ K) :
    (A.map f).relIndex (K.map f) ∣ A.relIndex K := by
  let fK : K →* K.map f :=
    (f.comp K.subtype).codRestrict (K.map f) (fun x =>
      Subgroup.mem_map_of_mem f x.property)
  have hfK : Function.Surjective fK := by
    rintro ⟨y, hy⟩
    rcases hy with ⟨x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, rfl⟩
  let AK : Subgroup K := A.subgroupOf K
  have hmap : AK.map fK = (A.map f).subgroupOf (K.map f) := by
    ext x
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact ⟨a, ha, rfl⟩
    · rintro ⟨a, ha, hax⟩
      refine ⟨⟨a, hAK ha⟩, ha, ?_⟩
      exact Subtype.ext hax
  have hdvd := Subgroup.index_map_dvd AK hfK
  change ((A.map f).subgroupOf (K.map f)).index ∣
    (A.subgroupOf K).index
  rw [← hmap]
  exact hdvd

private theorem twoCoreIn_le_of_pgroup_index_qci
    {G : Type u} [Group G] [Finite G]
    (Q K : Subgroup G) (hQK : Q ≤ K) (hQtwo : IsPGroup 2 Q)
    (hindex : ¬ 2 ∣ Q.relIndex K) :
    twoCoreIn K ≤ Q := by
  let QK : Subgroup K := Q.subgroupOf K
  have hQKtwo : IsPGroup 2 QK :=
    hQtwo.of_equiv (Subgroup.subgroupOfEquivOfLe hQK).symm
  have hQKindex : ¬ 2 ∣ QK.index := hindex
  let S : Sylow 2 K := hQKtwo.toSylow hQKindex
  have hcore : pCore 2 K ≤ (S : Subgroup K) := fitting_pCore_le_sylow S
  have hm := Subgroup.map_mono (f := K.subtype) hcore
  have hS : (S : Subgroup K) = QK :=
    IsPGroup.toSylow_coe hQKtwo hQKindex
  rw [hS, Subgroup.map_subgroupOf_eq_of_le hQK] at hm
  exact hm

private theorem isPGroup_le_pCore_of_le_fitting_qci
    {G : Type u} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (P : Subgroup G) (hPp : IsPGroup p P)
    (hPF : P ≤ fittingSubgroup G) :
    P ≤ pCore p G := by
  classical
  let PF : Subgroup (fittingSubgroup G) := P.subgroupOf (fittingSubgroup G)
  have hPFp : IsPGroup p PF :=
    hPp.of_equiv (Subgroup.subgroupOfEquivOfLe hPF).symm
  obtain ⟨U, hPFU⟩ := hPFp.exists_le_sylow
  have hUnormal : (U : Subgroup (fittingSubgroup G)).Normal :=
    Group.IsNilpotent.sylow_normal
      (G := fittingSubgroup G)
      (inferInstance : Group.IsNilpotent (fittingSubgroup G)) p U
  have hUchar : (U : Subgroup (fittingSubgroup G)).Characteristic :=
    Sylow.characteristic_of_normal U hUnormal
  have hUmapNormal : ((U : Subgroup (fittingSubgroup G)).map
      (fittingSubgroup G).subtype).Normal := by
    infer_instance
  have hUmapP : IsPGroup p ((U : Subgroup (fittingSubgroup G)).map
      (fittingSubgroup G).subtype) := U.isPGroup'.map (fittingSubgroup G).subtype
  have hUcore : (U : Subgroup (fittingSubgroup G)).map
      (fittingSubgroup G).subtype ≤ pCore p G :=
    le_sSup ⟨hUmapNormal, hUmapP⟩
  have hm := Subgroup.map_mono (f := (fittingSubgroup G).subtype) hPFU
  rw [Subgroup.map_subgroupOf_eq_of_le hPF] at hm
  exact hm.trans hUcore

private theorem isSubnormal_map_subgroupOf_qci
    {G G' : Type*} [Group G] [Group G']
    (f : G →* G') (A X : Subgroup G) (hAX : A ≤ X)
    (hsub : (A.subgroupOf X).IsSubnormal) :
    ((A.map f).subgroupOf (X.map f)).IsSubnormal := by
  let fX : X →* X.map f :=
    (f.comp X.subtype).codRestrict (X.map f) (fun x =>
      Subgroup.mem_map_of_mem f x.property)
  have hfX : Function.Surjective fX := by
    rintro ⟨y, hy⟩
    rcases hy with ⟨x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, rfl⟩
  have hmap : (A.subgroupOf X).map fX =
      (A.map f).subgroupOf (X.map f) := by
    ext x
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact ⟨a, ha, rfl⟩
    · rintro ⟨a, ha, hax⟩
      refine ⟨⟨a, hAX ha⟩, ha, ?_⟩
      exact Subtype.ext hax
  rw [← hmap]
  exact hsub.map hfX

private theorem relIndex_sup_eq_inf_of_normal_qci
    {G : Type*} [Group G] [Finite G]
    (Q K : Subgroup G) [K.Normal] :
    Q.relIndex (Q ⊔ K) = (Q ⊓ K).relIndex K := by
  have hKrel : K.relIndex (Q ⊔ K) = (Q ⊓ K).relIndex Q := by
    calc
      K.relIndex (Q ⊔ K) = K.relIndex Q :=
        Subgroup.relIndex_sup_right Q K
      _ = (Q ⊓ K).relIndex Q := by
        symm
        exact Subgroup.inf_relIndex_left Q K
  have hmul :
      (Q ⊓ K).relIndex Q * Q.relIndex (Q ⊔ K) =
        (Q ⊓ K).relIndex K * (Q ⊓ K).relIndex Q := by
    calc
      (Q ⊓ K).relIndex Q * Q.relIndex (Q ⊔ K) =
          (Q ⊓ K).relIndex (Q ⊔ K) :=
        Subgroup.relIndex_mul_relIndex _ _ _ inf_le_left le_sup_left
      _ = (Q ⊓ K).relIndex K * K.relIndex (Q ⊔ K) := by
        symm
        exact Subgroup.relIndex_mul_relIndex _ _ _ inf_le_right le_sup_right
      _ = (Q ⊓ K).relIndex K * (Q ⊓ K).relIndex Q := by rw [hKrel]
  have hpos : 0 < (Q ⊓ K).relIndex Q := by
    exact Nat.pos_of_ne_zero (by
      dsimp [Subgroup.relIndex]
      exact Subgroup.index_ne_zero_of_finite)
  have hmul' :
      (Q ⊓ K).relIndex Q * Q.relIndex (Q ⊔ K) =
        (Q ⊓ K).relIndex Q * (Q ⊓ K).relIndex K := by
    simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hmul
  exact Nat.eq_of_mul_eq_mul_left hpos hmul'

/-- The quotient two-core lies in the image of the source-aligned 2-subgroup. -/
public theorem five_two_quotient_twoCore_le_sylow_image
    {M : Type u} [Group M] [Finite M]
    (C0 K B T : Subgroup M) [C0.Normal]
    (hsolv : Group.IsSolvable M)
    (hcoreM : pCore 2 M ≤ C0)
    (hKsub : (K.subgroupOf (K ⊔ C0)).IsSubnormal)
    (hKcoreNot : ¬ twoCoreIn K ≤ C0)
    (hproper : ∀ X : Subgroup M,
      (B ⊔ K) ⊔ pCore 2 M ≤ X →
      X < ⊤ → (K.subgroupOf X).IsSubnormal)
    (hKodd : ∃ r : ℕ, r.Prime ∧ r ≠ 2 ∧
      IsPGroup r (K ⧸ pCore 2 K))
    (hBnormK : B ≤ Subgroup.normalizer (K : Set M))
    (hWnormK : let q : M →* M ⧸ C0 := QuotientGroup.mk' C0
      pCore 2 (M ⧸ C0) ≤ Subgroup.normalizer (K.map q : Set (M ⧸ C0)))
    (hTtwo : IsPGroup 2 T)
    (hKT : twoCoreIn K ⊔ B ≤ T) :
    let q : M →* M ⧸ C0 := QuotientGroup.mk' C0
    pCore 2 (M ⧸ C0) ≤ T.map q := by
  classical
  let q : M →* M ⧸ C0 := QuotientGroup.mk' C0
  let H : Type u := M ⧸ C0
  let Wbar : Subgroup H := pCore 2 H
  let W : Subgroup M := Wbar.comap q
  let KC : Subgroup M := K ⊔ C0
  let OKC : Subgroup M := twoCoreIn KC
  let P : Subgroup M := twoCoreIn K
  let Kbar : Subgroup H := K.map q
  let Bbar : Subgroup H := B.map q
  let Pbar : Subgroup H := P.map q
  change Wbar ≤ T.map q
  have hqsurj : Function.Surjective q := QuotientGroup.mk'_surjective C0
  have hqker : q.ker = C0 := QuotientGroup.ker_mk' C0
  have hWnormal : W.Normal := by
    dsimp [W, Wbar]
    infer_instance
  let _ : W.Normal := hWnormal
  have hWnormKbar : Wbar ≤ Subgroup.normalizer (Kbar : Set H) := by
    simpa [q, H, Wbar, Kbar] using hWnormK
  have hWnormKC : W ≤ Subgroup.normalizer (KC : Set M) := by
    have h := (Subgroup.comap_mono hWnormKbar).trans
      (Subgroup.le_normalizer_comap q)
    simpa [W, Kbar, KC, Subgroup.comap_map_eq, hqker] using h
  have hPOKC : P ≤ OKC := by
    change (pCore 2 K).map K.subtype ≤ (pCore 2 KC).map KC.subtype
    simpa only [KC] using
      (pCoreAmbient_mono_of_isSubnormalIn K (K ⊔ C0) 2 le_sup_left hKsub)
  have hWnormOKC : W ≤ Subgroup.normalizer (OKC : Set M) := by
    exact hWnormKC.trans
      (BenderSuzuki.External.hkt_normalizer_le_normalizer_map_subtype_of_characteristic
        KC (pCore 2 KC))
  let Q : Subgroup M := OKC ⊓ W
  have hQW : Q ≤ W := inf_le_right
  have hQnormalW : (Q.subgroupOf W).Normal := by
    apply (Subgroup.normal_subgroupOf_iff_le_normalizer hQW).mpr
    exact (le_inf hWnormOKC W.le_normalizer).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  have hQtwo : IsPGroup 2 Q :=
    (twoCoreIn_isPGroup_qci KC).to_subgroup (Q.subgroupOf OKC) |>.of_equiv
      (Subgroup.subgroupOfEquivOfLe inf_le_left)
  have hQcoreW : Q ≤ twoCoreIn W :=
    normal_pSubgroup_le_twoCoreIn_qci Q W hQW hQtwo hQnormalW
  have hcoreWcoreM : twoCoreIn W ≤ pCore 2 M := by
    have h := pCoreAmbient_mono_of_isSubnormalIn W (⊤ : Subgroup M) 2 le_top
      hWnormal.isSubnormal.subgroupOf
    change twoCoreIn W ≤ pCore 2 M
    rw [← twoCoreIn_top_qci]
    exact h
  have hPW : P ⊓ W ≤ C0 := by
    exact (inf_le_inf_right W hPOKC).trans hQcoreW |>.trans hcoreWcoreM |>.trans hcoreM
  obtain ⟨r, hrprime, hrne, hKodd'⟩ := hKodd
  obtain ⟨n, hKquotCard⟩ := @IsPGroup.exists_card_eq
    r (K ⧸ pCore 2 K) inferInstance ⟨hrprime⟩ inferInstance hKodd'
  have hPsubK : P.subgroupOf K = pCore 2 K := by
    dsimp [P]
    exact subgroupOf_map_subtype_eq _
  have hPindexOdd : ¬ 2 ∣ P.relIndex K := by
    change ¬ 2 ∣ (P.subgroupOf K).index
    rw [hPsubK, Subgroup.index_eq_card, hKquotCard]
    intro hdvd
    have htwoDvdR : 2 ∣ r := Nat.prime_two.dvd_of_dvd_pow hdvd
    exact hrne ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hrprime).mp htwoDvdR).symm
  have hPK : P ≤ K := by
    dsimp [P, twoCoreIn]
    exact Subgroup.map_subtype_le _
  have hPbarKbar : Pbar ≤ Kbar := Subgroup.map_mono hPK
  have hPbarTwo : IsPGroup 2 Pbar :=
    (twoCoreIn_isPGroup_qci K).map q
  have hPbarIndexOdd : ¬ 2 ∣ Pbar.relIndex Kbar := by
    intro hdvd
    exact hPindexOdd (hdvd.trans
      (relIndex_map_dvd_relIndex_qci q P K hPK))
  let OKbar : Subgroup H := twoCoreIn Kbar
  have hOKbarPbar : OKbar ≤ Pbar :=
    twoCoreIn_le_of_pgroup_index_qci Pbar Kbar hPbarKbar hPbarTwo hPbarIndexOdd
  have hPnormalK : (P.subgroupOf K).Normal := twoCoreIn_normalIn_qci K
  have hKnormP : K ≤ Subgroup.normalizer (P : Set M) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hPK).mp hPnormalK
  have hKbarnormPbar : Kbar ≤ Subgroup.normalizer (Pbar : Set H) := by
    exact (Subgroup.map_mono hKnormP).trans (Subgroup.le_normalizer_map q)
  have hPbarNormalKbar : (Pbar.subgroupOf Kbar).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hPbarKbar).mpr hKbarnormPbar
  have hPbarOKbar : Pbar ≤ OKbar :=
    normal_pSubgroup_le_twoCoreIn_qci Pbar Kbar hPbarKbar hPbarTwo hPbarNormalKbar
  have hPbarWbar : Pbar ⊓ Wbar = ⊥ := by
    apply le_bot_iff.mp
    intro x hx
    rcases hx.1 with ⟨p, hpP, rfl⟩
    have hpW : p ∈ W := hx.2
    have hpC0 : p ∈ C0 := hPW ⟨hpP, hpW⟩
    change q p = 1
    apply show p ∈ q.ker from ?_
    simpa [hqker] using hpC0
  let Rbar : Subgroup H := Kbar ⊓ Wbar
  have hRbarKbar : Rbar ≤ Kbar := inf_le_left
  have hWbarNormal : Wbar.Normal := by
    dsimp [Wbar]
    infer_instance
  let _ : Wbar.Normal := hWbarNormal
  have hKbarNormWbar : Kbar ≤ Subgroup.normalizer (Wbar : Set H) := by
    rw [Subgroup.normalizer_eq_top Wbar]
    exact le_top
  have hRbarNormalKbar : (Rbar.subgroupOf Kbar).Normal := by
    apply (Subgroup.normal_subgroupOf_iff_le_normalizer hRbarKbar).mpr
    exact (le_inf Kbar.le_normalizer hKbarNormWbar).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  have hRbarTwo : IsPGroup 2 Rbar :=
    (pCore_isPGroup (G := H) (p := 2)).to_subgroup (Rbar.subgroupOf Wbar) |>.of_equiv
      (Subgroup.subgroupOfEquivOfLe inf_le_right)
  have hRbarOKbar : Rbar ≤ OKbar :=
    normal_pSubgroup_le_twoCoreIn_qci Rbar Kbar hRbarKbar hRbarTwo hRbarNormalKbar
  have hKbarWbar : Kbar ⊓ Wbar = ⊥ := by
    apply le_bot_iff.mp
    change Rbar ≤ ⊥
    exact (le_inf (hRbarOKbar.trans hOKbarPbar)
      (show Rbar ≤ Wbar from inf_le_right)).trans hPbarWbar.le
  have hWbarCommKbar : ⁅Wbar, Kbar⁆ = ⊥ := by
    apply le_bot_iff.mp
    have hcommK : ⁅Wbar, Kbar⁆ ≤ Kbar :=
      Subgroup.le_normalizer_iff_commutator_le_right.mp hWnormKbar
    exact (le_inf hcommK (Subgroup.commutator_le_left Wbar Kbar)).trans
      hKbarWbar.le
  have hPbarNe : Pbar ≠ ⊥ := by
    intro hbot
    have hPker : P ≤ q.ker := (Subgroup.map_eq_bot_iff P).mp hbot
    exact hKcoreNot (by simpa [hqker] using hPker)
  have hOKbarNe : OKbar ≠ ⊥ := by
    intro hbot
    exact hPbarNe (le_bot_iff.mp (hPbarOKbar.trans hbot.le))
  let Fit : Subgroup H := fittingSubgroup H
  let D : Subgroup H := (pPrimeCore 2 Fit).map Fit.subtype
  have hDnormal : D.Normal := by
    dsimp [D, Fit]
    infer_instance
  let _ : D.Normal := hDnormal
  have hDodd : ¬ 2 ∣ Nat.card D := by
    simpa [D, Fit] using (oddFitting_isOdd_qci (G := H))
  have hFitGen : Fit ≤ Wbar ⊔ D := by
    simpa [Fit, Wbar, D] using (fitting_le_twoCore_sup_oddFitting_qci (G := H))
  let _ : Group.IsSolvable M := hsolv
  have hHsolv : Group.IsSolvable H :=
    Group.isSolvable_of_surjective hqsurj
  let _ : Group.IsSolvable H := hHsolv
  have hDCommOKbar : ⁅D, OKbar⁆ ≠ ⊥ := by
    intro hcomm
    have hWcentK : Wbar ≤ Subgroup.centralizer (Kbar : Set H) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp hWbarCommKbar
    have hWcentOK : Wbar ≤ Subgroup.centralizer (OKbar : Set H) :=
      hWcentK.trans (Subgroup.centralizer_le (Subgroup.map_subtype_le _))
    have hDcentOK : D ≤ Subgroup.centralizer (OKbar : Set H) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
    have hjoinComm : ⁅Wbar ⊔ D, OKbar⁆ = ⊥ :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
        (sup_le hWcentOK hDcentOK)
    have hOKcentJoin : OKbar ≤
        Subgroup.centralizer ((Wbar ⊔ D : Subgroup H) : Set H) := by
      rw [← Subgroup.commutator_eq_bot_iff_le_centralizer,
        ← Subgroup.commutator_comm]
      exact hjoinComm
    have hOKcentFit : OKbar ≤ Subgroup.centralizer (Fit : Set H) :=
      hOKcentJoin.trans (Subgroup.centralizer_le hFitGen)
    have hOKFit : OKbar ≤ Fit := by
      exact hOKcentFit.trans
        (centralizer_fittingSubgroup_le_fittingSubgroup_of_solvable hHsolv)
    have hOKtwo : IsPGroup 2 OKbar := twoCoreIn_isPGroup_qci Kbar
    have hOKW : OKbar ≤ Wbar := by
      simpa [Wbar] using
        (isPGroup_le_pCore_of_le_fitting_qci OKbar hOKtwo (by simpa [Fit] using hOKFit))
    have hOKbot : OKbar = ⊥ := le_bot_iff.mp
      ((le_inf (Subgroup.map_subtype_le _) hOKW).trans hKbarWbar.le)
    exact hOKbarNe hOKbot
  let Xbar : Subgroup H := (D ⊔ Kbar) ⊔ Bbar
  have hXbarTop : Xbar = ⊤ := by
    by_contra hXbarNe
    have hXbarLt : Xbar < ⊤ := lt_top_iff_ne_top.mpr hXbarNe
    let X : Subgroup M := Xbar.comap q
    have hXmap : X.map q = Xbar := by
      exact Subgroup.map_comap_eq_self_of_surjective hqsurj Xbar
    have hXne : X ≠ ⊤ := by
      intro hXtop
      have htopMap : (⊤ : Subgroup M).map q = (⊤ : Subgroup H) := by
        rw [← MonoidHom.range_eq_map,
          MonoidHom.range_eq_top.mpr hqsurj]
      have : (⊤ : Subgroup H) = Xbar := by
        rw [← htopMap, ← hXtop]
        exact hXmap
      exact hXbarNe this.symm
    have hXLt : X < ⊤ := lt_top_iff_ne_top.mpr hXne
    have hBX : B ≤ X := by
      apply Subgroup.map_le_iff_le_comap.mp
      change Bbar ≤ Xbar
      exact le_sup_right
    have hKX : K ≤ X := by
      apply Subgroup.map_le_iff_le_comap.mp
      change Kbar ≤ Xbar
      exact (show Kbar ≤ D ⊔ Kbar from le_sup_right).trans
        (show D ⊔ Kbar ≤ Xbar from le_sup_left)
    have hC0X : C0 ≤ X := by
      intro c hc
      change q c ∈ Xbar
      have hcKer : c ∈ q.ker := by simpa [hqker] using hc
      rw [show q c = 1 from hcKer]
      exact Xbar.one_mem
    have hcoreMX : pCore 2 M ≤ X := by
      exact hcoreM.trans hC0X
    have hKsubX : (K.subgroupOf X).IsSubnormal :=
      hproper X (sup_le (sup_le hBX hKX) hcoreMX) hXLt
    have hKbarSubXbar : (Kbar.subgroupOf Xbar).IsSubnormal := by
      have hm := isSubnormal_map_subgroupOf_qci q K X hKX hKsubX
      rw [hXmap] at hm
      exact hm
    let OXbar : Subgroup H := twoCoreIn Xbar
    have hOKbarOXbar : OKbar ≤ OXbar := by
      change (pCore 2 Kbar).map Kbar.subtype ≤
        (pCore 2 Xbar).map Xbar.subtype
      exact pCoreAmbient_mono_of_isSubnormalIn Kbar Xbar 2
        ((show Kbar ≤ D ⊔ Kbar from le_sup_right).trans
          (show D ⊔ Kbar ≤ Xbar from le_sup_left)) hKbarSubXbar
    have hDXbar : D ≤ Xbar :=
      (show D ≤ D ⊔ Kbar from le_sup_left).trans
        (show D ⊔ Kbar ≤ Xbar from le_sup_left)
    have hOXbarXbar : OXbar ≤ Xbar := by
      dsimp [OXbar, twoCoreIn]
      exact Subgroup.map_subtype_le _
    have hXbarNormOXbar : Xbar ≤ Subgroup.normalizer (OXbar : Set H) := by
      exact Xbar.le_normalizer.trans
        (BenderSuzuki.External.hkt_normalizer_le_normalizer_map_subtype_of_characteristic
          Xbar (pCore 2 Xbar))
    have hDNormOXbar : D ≤ Subgroup.normalizer (OXbar : Set H) :=
      hDXbar.trans hXbarNormOXbar
    have hOXbarNormD : OXbar ≤ Subgroup.normalizer (D : Set H) := by
      rw [Subgroup.normalizer_eq_top D]
      exact le_top
    have hcommD : ⁅D, OXbar⁆ ≤ D :=
      Subgroup.le_normalizer_iff_commutator_le_left.mp hOXbarNormD
    have hcommOX : ⁅D, OXbar⁆ ≤ OXbar :=
      Subgroup.le_normalizer_iff_commutator_le_right.mp hDNormOXbar
    have hOXbarTwo : IsPGroup 2 OXbar := twoCoreIn_isPGroup_qci Xbar
    obtain ⟨m, hOXbarCard⟩ := hOXbarTwo.exists_card_eq
    have hDcopOXbar : Nat.Coprime (Nat.card D) (Nat.card OXbar) := by
      rw [hOXbarCard]
      exact (Nat.prime_two.coprime_iff_not_dvd.mpr hDodd).symm.pow_right m
    have hDdisjOXbar : Disjoint D OXbar :=
      Subgroup.disjoint_of_coprime_natCard hDcopOXbar
    have hDCommOXbar : ⁅D, OXbar⁆ = ⊥ := le_bot_iff.mp
      ((le_inf hcommD hcommOX).trans hDdisjOXbar.le_bot)
    exact hDCommOKbar (le_bot_iff.mp
      ((Subgroup.commutator_mono le_rfl hOKbarOXbar).trans hDCommOXbar.le))
  let Y : Subgroup H := Kbar ⊔ Bbar
  let Qbar : Subgroup H := Pbar ⊔ Bbar
  have hKbarY : Kbar ≤ Y := le_sup_left
  have hQbarY : Qbar ≤ Y := by
    exact sup_le (hPbarKbar.trans le_sup_left) le_sup_right
  have hQbarT : Qbar ≤ T.map q := by
    have hm := Subgroup.map_mono (f := q) hKT
    rw [Subgroup.map_sup] at hm
    exact hm
  have hQbarTwo : IsPGroup 2 Qbar :=
    (hTtwo.map q).to_subgroup (Qbar.subgroupOf (T.map q)) |>.of_equiv
      (Subgroup.subgroupOfEquivOfLe hQbarT)
  have hBbarNormKbar : Bbar ≤ Subgroup.normalizer (Kbar : Set H) := by
    exact (Subgroup.map_mono hBnormK).trans (Subgroup.le_normalizer_map q)
  have hKbarNormalY : (Kbar.subgroupOf Y).Normal := by
    apply (Subgroup.normal_subgroupOf_iff_le_normalizer hKbarY).mpr
    exact sup_le Kbar.le_normalizer hBbarNormKbar
  let KY : Subgroup Y := Kbar.subgroupOf Y
  let QY : Subgroup Y := Qbar.subgroupOf Y
  let PY : Subgroup Y := Pbar.subgroupOf Y
  let _ : KY.Normal := hKbarNormalY
  have hQbarSupKbar : Qbar ⊔ Kbar = Y := by
    apply le_antisymm
    · exact sup_le hQbarY hKbarY
    · exact sup_le le_sup_right (le_sup_right.trans le_sup_left)
  have hQYsupKY : QY ⊔ KY = ⊤ := by
    apply Subgroup.map_injective Y.subtype_injective
    rw [Subgroup.map_sup,
      Subgroup.map_subgroupOf_eq_of_le hQbarY,
      Subgroup.map_subgroupOf_eq_of_le hKbarY,
      ← MonoidHom.range_eq_map, Subgroup.range_subtype,
      hQbarSupKbar]
  have hPYleInf : PY ≤ QY ⊓ KY := by
    intro x hx
    change (x : H) ∈ Pbar at hx
    exact ⟨(show Pbar ≤ Qbar from le_sup_left) hx, hPbarKbar hx⟩
  have hPYrel : Pbar.relIndex Kbar = PY.relIndex KY := by
    have hrel := Subgroup.relIndex_map_map_of_injective
      PY KY Y.subtype_injective
    rw [Subgroup.map_subgroupOf_eq_of_le (hPbarKbar.trans hKbarY),
      Subgroup.map_subgroupOf_eq_of_le hKbarY] at hrel
    exact hrel
  have hQYindexOdd : ¬ 2 ∣ QY.index := by
    rw [← Subgroup.relIndex_top_right (H := QY)]
    rw [← hQYsupKY, relIndex_sup_eq_inf_of_normal_qci QY KY]
    intro hdvd
    have hidxDvd : (QY ⊓ KY).relIndex KY ∣ PY.relIndex KY :=
      Subgroup.relIndex_dvd_of_le_left KY hPYleInf
    apply hPbarIndexOdd
    rw [hPYrel]
    exact hdvd.trans hidxDvd
  have hQYTwo : IsPGroup 2 QY :=
    hQbarTwo.of_equiv (Subgroup.subgroupOfEquivOfLe hQbarY).symm
  let SY : Sylow 2 Y := hQYTwo.toSylow hQYindexOdd
  have hSY : (SY : Subgroup Y) = QY :=
    IsPGroup.toSylow_coe hQYTwo hQYindexOdd
  have hDsupY : D ⊔ Y = ⊤ := by
    simpa [Xbar, Y, sup_assoc] using hXbarTop
  obtain ⟨U, hUmap⟩ :=
    Sylow.exists_map_eq_map_of_normal_coprime_sup D Y hDodd SY
  have hSYmap : (SY : Subgroup Y).map Y.subtype = Qbar := by
    rw [hSY]
    exact Subgroup.map_subgroupOf_eq_of_le hQbarY
  rw [hSYmap] at hUmap
  have hcoreU : pCore 2 (↥(D ⊔ Y : Subgroup H)) ≤
      (U : Subgroup ↥(D ⊔ Y : Subgroup H)) :=
    fitting_pCore_le_sylow U
  have hm := Subgroup.map_mono (f := (D ⊔ Y : Subgroup H).subtype) hcoreU
  change twoCoreIn (D ⊔ Y) ≤
    (U : Subgroup ↥(D ⊔ Y : Subgroup H)).map
      (D ⊔ Y : Subgroup H).subtype at hm
  have hcoreEq : twoCoreIn (D ⊔ Y) = Wbar := by
    rw [hDsupY, twoCoreIn_top_qci]
  exact hcoreEq.symm.le.trans hm |>.trans_eq hUmap |>.trans hQbarT

end Stellmacher.SectionsFiveToSeven
