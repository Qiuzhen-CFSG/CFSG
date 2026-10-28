module

public import BenderSuzuki.External.Huppert.V.FrattiniQuotient
public import Stellmacher.SectionOne.RankOneThreeGroupAssembly.SL2Products
public import Theory.GroupAction.Quotient

/-!
# Core-free nested `SL₂(2)` quotients after factoring an odd centralizer layer

This module proves the quotient transfer needed in the application of *Pushing
up* (1986), (1.4)(a), to Stellmacher's argument (2.2).  If `C ◃ G` contains
`O₂(G)`, the factor `C/O₂(G)` has odd order, and `G/C` is not a
`2`-group, then condition (A) on `G/O₂(G)` descends to `G/C`.
Moreover, the faithful quotient `G/C` has trivial `2`-core.

The proof writes `X = G/O₂(G)` and `N = C/O₂(G)`.  The image of the odd
normal subgroup `N` in `X/Φ(X) ≃ SL₂(2) ≃ S₃` has order one or three.
The order-three case, together with a Sylow `2`-subgroup, generates the
Frattini quotient and hence `X`, forcing `X/N` to be a `2`-group.
Thus `N ≤ Φ(X)`, so the Frattini quotient transports exactly.  Finally,
`O₂(X)=1` makes the nilpotent group `Φ(X)` odd; its image `Φ(X/N)`
is odd as well, while `O₂(X/N)` lies in it, proving core-freeness.
-/

open scoped Pointwise

namespace Stellmacher.PushingUp

universe u v

private theorem frattini_map_eq_of_surjective_of_ker_le
    {G H : Type u} [Group G] [Finite G] [Group H] [Finite H]
    (f : G →* H) (hf : Function.Surjective f)
    (hker : f.ker ≤ frattini G) :
    (frattini G).map f = frattini H := by
  apply le_antisymm
  · exact Subgroup.map_le_iff_le_comap.mpr
      (frattini_le_comap_frattini_of_surjective hf)
  · rw [← Subgroup.map_comap_eq_self_of_surjective hf (frattini H)]
    apply Subgroup.map_mono
    rw [frattini, Order.radical]
    refine le_iInf fun M => le_iInf fun hM => ?_
    have hΦM : frattini G ≤ M := frattini_le_coatom hM
    have hkerM : f.ker ≤ M := hker.trans hΦM
    have hmapM : IsCoatom (M.map f) :=
      BenderSuzuki.External.hkt_isCoatom_map_of_surjective_of_ker_le
        f hf hkerM hM
    calc
      (frattini H).comap f ≤ (M.map f).comap f :=
        Subgroup.comap_mono (frattini_le_coatom hmapM)
      _ = M ⊔ f.ker := Subgroup.comap_map_eq f M
      _ = M := sup_eq_left.mpr hkerM

private theorem frattini_map_equiv
    {G : Type u} {H : Type v} [Group G] [Group H] (e : G ≃* H) :
    (frattini G).map e.toMonoidHom = frattini H := by
  apply le_antisymm
  · exact Subgroup.map_le_iff_le_comap.mpr
      (frattini_le_comap_frattini_of_surjective e.surjective)
  · intro y hy
    have hy' : e.symm y ∈ frattini G :=
      frattini_le_comap_frattini_of_surjective
        (G := H) (H := G) (φ := e.symm.toMonoidHom) e.symm.surjective hy
    exact ⟨e.symm y, hy', e.apply_symm_apply y⟩

private theorem isSL2Two_frattini_quotient_of_mulEquiv
    {G : Type u} {H : Type v} [Group G] [Finite G] [Group H] [Finite H]
    (e : G ≃* H) (hG : IsSL2Two (G ⧸ frattini G)) :
    IsSL2Two (H ⧸ frattini H) := by
  let eΦ : (G ⧸ frattini G) ≃* (H ⧸ frattini H) :=
    QuotientGroup.congr _ _ e (frattini_map_equiv e)
  obtain ⟨eSL⟩ := hG
  exact ⟨eΦ.symm.trans eSL⟩

private theorem isSL2Two_frattini_quotient_of_normal_le_frattini
    {G : Type u} [Group G] [Finite G]
    (N : Subgroup G) [N.Normal] (hN : N ≤ frattini G)
    (hG : IsSL2Two (G ⧸ frattini G)) :
    IsSL2Two ((G ⧸ N) ⧸ frattini (G ⧸ N)) := by
  let q : G →* G ⧸ N := QuotientGroup.mk' N
  have hker : q.ker ≤ frattini G := by simpa [q] using hN
  have hmap : (frattini G).map q = frattini (G ⧸ N) :=
    frattini_map_eq_of_surjective_of_ker_le q
      (QuotientGroup.mk'_surjective N) hker
  let e₀ : ((G ⧸ N) ⧸ frattini (G ⧸ N)) ≃*
      ((G ⧸ N) ⧸ (frattini G).map q) :=
    QuotientGroup.quotientMulEquivOfEq hmap.symm
  let e₁ : ((G ⧸ N) ⧸ (frattini G).map q) ≃*
      G ⧸ frattini G :=
    QuotientGroup.quotientQuotientEquivQuotient N (frattini G) hN
  obtain ⟨eSL⟩ := hG
  exact ⟨(e₀.trans e₁).trans eSL⟩

private theorem normal_subgroup_card_two_le_center
    {G : Type u} [Group G] [Finite G]
    (P : Subgroup G) [P.Normal] (hPcard : Nat.card P = 2) :
    P ≤ Subgroup.center G := by
  obtain ⟨t, ht_ne, ht_unique⟩ := (Nat.card_eq_two_iff' (1 : P)).mp hPcard
  intro p hp
  rw [Subgroup.mem_center_iff]
  intro g
  by_cases hp_one : p = 1
  · simp [hp_one]
  have hp_eq_t : (⟨p, hp⟩ : P) = t := ht_unique ⟨p, hp⟩ (by
    intro h
    exact hp_one (congrArg Subtype.val h))
  have hconj_mem : g * p * g⁻¹ ∈ P :=
    (inferInstance : P.Normal).conj_mem p hp g
  have hconj_ne : g * p * g⁻¹ ≠ 1 := by
    intro hconj
    have h := congrArg (fun x : G => g⁻¹ * x * g) hconj
    exact hp_one (by simpa [mul_assoc] using h)
  have hconj_eq_t : (⟨g * p * g⁻¹, hconj_mem⟩ : P) = t :=
    ht_unique ⟨g * p * g⁻¹, hconj_mem⟩ (by
      intro h
      exact hconj_ne (congrArg Subtype.val h))
  have hconj_eq : g * p * g⁻¹ = p :=
    congrArg Subtype.val (hconj_eq_t.trans hp_eq_t.symm)
  have h := congrArg (fun x : G => x * g) hconj_eq
  simpa [mul_assoc] using h

private theorem sylow_card_two_of_isSL2Two
    {G : Type u} [Group G] [Finite G] (S : Sylow 2 G)
    (hG : IsSL2Two G) : Nat.card S = 2 := by
  have hGcard : Nat.card G = 6 :=
    SectionOne.RankOneThreeGroupAssembly.isSL2Two_card hG
  rw [S.card_eq_multiplicity, hGcard]
  have hf6 : Nat.factorization 6 2 = 1 := by
    change Nat.factorization (3 * 2) 2 = 1
    rw [Nat.factorization_mul (by decide) (by decide)]
    norm_num [Nat.prime_two.factorization, Nat.prime_three.factorization]
  simp [hf6]

private theorem pCore_eq_bot_of_isSL2Two
    {G : Type u} [Group G] [Finite G] (hG : IsSL2Two G) :
    pCore 2 G = ⊥ := by
  let S : Sylow 2 G := default
  have hcoreS : pCore 2 G ≤ (S : Subgroup G) :=
    (pCore_isPGroup (p := 2) (G := G)).le_sylow_of_normal S
  have hcardDvd : Nat.card (pCore 2 G) ∣ Nat.card S :=
    Subgroup.card_dvd_of_le hcoreS
  have hScard : Nat.card S = 2 := sylow_card_two_of_isSL2Two S hG
  rw [hScard] at hcardDvd
  rcases (Nat.dvd_prime Nat.prime_two).mp hcardDvd with hcard | hcard
  · exact Subgroup.card_eq_one.mp hcard
  · have hcenter : pCore 2 G ≤ Subgroup.center G :=
      normal_subgroup_card_two_le_center (pCore 2 G) hcard
    exact le_bot_iff.mp (hcenter.trans (le_of_eq
      (SectionOne.RankOneThreeGroupAssembly.center_eq_bot_of_isSL2Two hG)))

private theorem pCore_le_frattini_of_isSL2Two_frattiniQuotient
    {G : Type u} [Group G] [Finite G]
    (hA : IsSL2Two (G ⧸ frattini G)) :
    pCore 2 G ≤ frattini G := by
  let q : G →* G ⧸ frattini G := QuotientGroup.mk' (frattini G)
  have hmapNormal : ((pCore 2 G).map q).Normal :=
    (pCore_normal (p := 2) (G := G)).map q
      (QuotientGroup.mk'_surjective (frattini G))
  have hmapTwo : IsPGroup 2 ((pCore 2 G).map q) :=
    (pCore_isPGroup (p := 2) (G := G)).map q
  have hmapLe : (pCore 2 G).map q ≤ pCore 2 (G ⧸ frattini G) :=
    le_sSup ⟨hmapNormal, hmapTwo⟩
  have hmapBot : (pCore 2 G).map q = ⊥ :=
    le_bot_iff.mp (hmapLe.trans (le_of_eq (pCore_eq_bot_of_isSL2Two hA)))
  have hker : pCore 2 G ≤ q.ker :=
    (Subgroup.map_eq_bot_iff (H := pCore 2 G) (f := q)).mp hmapBot
  simpa [q, QuotientGroup.ker_mk'] using hker

private theorem frattini_odd_of_core_eq_bot
    {G : Type u} [Group G] [Finite G] (hcore : pCore 2 G = ⊥) :
    ¬ 2 ∣ Nat.card (frattini G) := by
  let Φ : Subgroup G := frattini G
  let P : Sylow 2 Φ := default
  have hΦnil : Group.IsNilpotent Φ := by
    simpa [Φ] using (frattini_nilpotent (G := G))
  have hPnormal : (P : Subgroup Φ).Normal :=
    Group.IsNilpotent.sylow_normal hΦnil 2 P
  let _ : (P : Subgroup Φ).Characteristic :=
    Sylow.characteristic_of_normal P hPnormal
  have hPmapNormal : ((P : Subgroup Φ).map Φ.subtype).Normal := by
    infer_instance
  have hPmapCore : (P : Subgroup Φ).map Φ.subtype ≤ pCore 2 G :=
    le_sSup ⟨hPmapNormal, P.isPGroup'.map Φ.subtype⟩
  intro hdvd
  have hPne : (P : Subgroup Φ) ≠ ⊥ := P.ne_bot_of_dvd_card hdvd
  have hPmapBot : (P : Subgroup Φ).map Φ.subtype = ⊥ :=
    le_bot_iff.mp (hPmapCore.trans (le_of_eq hcore))
  exact hPne <|
    (Subgroup.map_eq_bot_iff_of_injective
      (H := (P : Subgroup Φ)) (f := Φ.subtype) Φ.subtype_injective).mp hPmapBot

private theorem pCore_quotient_pCore_eq_bot
    {G : Type u} [Group G] :
    pCore 2 (G ⧸ pCore 2 G) = ⊥ := by
  have hmap := pCore_map_mk'_eq_of_normal_isPGroup
    (G := G) (p := 2) (pCore 2 G)
      (pCore_isPGroup (p := 2) (G := G))
  rw [← hmap]
  exact QuotientGroup.map_mk'_self (N := pCore 2 G)

private theorem pCore_eq_bot_of_le_odd
    {G : Type u} [Group G] [Finite G]
    (K : Subgroup G) (hcoreK : pCore 2 G ≤ K)
    (hKodd : ¬ 2 ∣ Nat.card K) :
    pCore 2 G = ⊥ := by
  rcases (pCore_isPGroup (p := 2) (G := G)).card_eq_or_dvd with hcard | hdvd
  · exact Subgroup.card_eq_one.mp hcard
  · exact False.elim (hKodd (hdvd.trans (Subgroup.card_dvd_of_le hcoreK)))

private theorem normal_odd_le_frattini_of_sl2Two_quotient_of_quotient_not_two
    {G : Type u} [Group G] [Finite G]
    (N : Subgroup G) [N.Normal]
    (hNodd : ¬ 2 ∣ Nat.card N)
    (hnp : ¬ IsPGroup 2 (G ⧸ N))
    (hA : IsSL2Two (G ⧸ frattini G)) :
    N ≤ frattini G := by
  classical
  let Φ : Subgroup G := frattini G
  let qΦ : G →* G ⧸ Φ := QuotientGroup.mk' Φ
  let Nbar : Subgroup (G ⧸ Φ) := N.map qΦ
  have hNbarNormal : Nbar.Normal := by
    exact (inferInstance : N.Normal).map qΦ
      (QuotientGroup.mk'_surjective Φ)
  let _ : Nbar.Normal := hNbarNormal
  have hNbarOdd : ¬ 2 ∣ Nat.card Nbar := by
    intro htwo
    apply hNodd
    exact htwo.trans (Subgroup.card_map_dvd (H := N) qΦ)
  have hquotCard : Nat.card (G ⧸ Φ) = 6 :=
    SectionOne.RankOneThreeGroupAssembly.isSL2Two_card (by
      simpa [Φ] using hA)
  have hNbarDvd : Nat.card Nbar ∣ 6 := by
    rw [← hquotCard]
    simpa using (Subgroup.card_dvd_of_le (H := Nbar) (K := ⊤) le_top)
  have hNbarCases : Nat.card Nbar = 1 ∨ Nat.card Nbar = 3 := by
    have hpos : 0 < Nat.card Nbar := Nat.card_pos
    have hle : Nat.card Nbar ≤ 6 := Nat.le_of_dvd (by norm_num) hNbarDvd
    interval_cases hcard : Nat.card Nbar
    · simp
    · norm_num at hNbarOdd
    · simp
    · norm_num at hNbarOdd
    · norm_num at hNbarDvd
    · norm_num at hNbarOdd
  rcases hNbarCases with hNbarOne | hNbarThree
  · have hNbarBot : Nbar = ⊥ := Subgroup.card_eq_one.mp hNbarOne
    have hmapBot : N.map qΦ = ⊥ := by simpa [Nbar] using hNbarBot
    have hNker : N ≤ qΦ.ker :=
      (Subgroup.map_eq_bot_iff (f := qΦ) (H := N)).mp hmapBot
    simpa [qΦ, Φ, QuotientGroup.ker_mk'] using hNker
  · let P : Sylow 2 G := default
    let Pbar : Sylow 2 (G ⧸ Φ) :=
      P.mapSurjective (QuotientGroup.mk'_surjective Φ)
    have hPbarCoe : (Pbar : Subgroup (G ⧸ Φ)) =
        (P : Subgroup G).map qΦ := by
      exact Sylow.coe_mapSurjective (QuotientGroup.mk'_surjective Φ) P
    have hPbarCard : Nat.card Pbar = 2 :=
      sylow_card_two_of_isSL2Two Pbar (by simpa [Φ] using hA)
    have hcardProd :
        Nat.card Nbar * Nat.card (Pbar : Subgroup (G ⧸ Φ)) =
          Nat.card (G ⧸ Φ) := by
      simp [hNbarThree, hPbarCard, hquotCard]
    have hcop : Nat.Coprime (Nat.card Nbar)
        (Nat.card (Pbar : Subgroup (G ⧸ Φ))) := by
      norm_num [hNbarThree, hPbarCard]
    have hsupBar : Nbar ⊔ (Pbar : Subgroup (G ⧸ Φ)) = ⊤ :=
      (Subgroup.isComplement'_of_coprime hcardProd hcop).sup_eq_top
    have hmapSup : (N ⊔ (P : Subgroup G)).map qΦ = ⊤ := by
      rw [Subgroup.map_sup]
      simpa [Nbar, hPbarCoe] using hsupBar
    have hcomapSup := congrArg (Subgroup.comap qΦ) hmapSup
    have hsupPhi : (N ⊔ (P : Subgroup G)) ⊔ frattini G = ⊤ := by
      simpa [Subgroup.comap_map_eq, qΦ, Φ, QuotientGroup.ker_mk'] using hcomapSup
    have hNPtop : N ⊔ (P : Subgroup G) = ⊤ :=
      frattini_nongenerating hsupPhi
    let qN : G →* G ⧸ N := QuotientGroup.mk' N
    have hmapTop := congrArg (fun K : Subgroup G ↦ K.map qN) hNPtop
    have hPmapTop : (P : Subgroup G).map qN = ⊤ := by
      simpa [Subgroup.map_sup, qN,
        Subgroup.map_top_of_surjective qN
          (QuotientGroup.mk'_surjective N)] using hmapTop
    have hPmapTwo : IsPGroup 2 ((P : Subgroup G).map qN) :=
      P.isPGroup'.map qN
    rw [hPmapTop] at hPmapTwo
    exact False.elim (hnp (hPmapTwo.of_equiv Subgroup.topEquiv))

public theorem isSL2Two_nested_actionQuotient
    {G : Type u} [Group G] [Finite G]
    (C : Subgroup G) [C.Normal]
    (hQC : pCore 2 G ≤ C)
    (hCodd : ¬ 2 ∣ ((pCore 2 G).subgroupOf C).index)
    (hnp : ¬ IsPGroup 2 (G ⧸ C))
    (hA : IsSL2Two
      ((G ⧸ pCore 2 G) ⧸ frattini (G ⧸ pCore 2 G))) :
    pCore 2 (G ⧸ C) = ⊥ ∧
      IsSL2Two
        (((G ⧸ C) ⧸ pCore 2 (G ⧸ C)) ⧸
          frattini ((G ⧸ C) ⧸ pCore 2 (G ⧸ C))) := by
  classical
  let Q : Subgroup G := pCore 2 G
  let X := G ⧸ Q
  let qQ : G →* X := QuotientGroup.mk' Q
  let N : Subgroup X := C.map qQ
  have hNnormal : N.Normal := by
    exact (inferInstance : C.Normal).map qQ
      (QuotientGroup.mk'_surjective Q)
  let _ : N.Normal := hNnormal
  have hNcard : Nat.card N = (Q.subgroupOf C).index := by
    calc
      Nat.card N = Nat.card (C ⧸ Q.subgroupOf C) := by
        simpa [N, qQ, X] using natCard_map_mk'_eq C Q
      _ = (Q.subgroupOf C).index :=
        (Subgroup.index_eq_card (H := Q.subgroupOf C)).symm
  have hNodd : ¬ 2 ∣ Nat.card N := by
    intro hdvd
    apply hCodd
    simpa [Q, hNcard] using hdvd
  let e : (X ⧸ N) ≃* (G ⧸ C) := by
    simpa [X, N, qQ] using
      (QuotientGroup.quotientQuotientEquivQuotient Q C hQC)
  have hnpXN : ¬ IsPGroup 2 (X ⧸ N) := by
    intro hp
    exact hnp (hp.of_equiv e)
  have hAX : IsSL2Two (X ⧸ frattini X) := by
    simpa [X, Q] using hA
  have hNΦ : N ≤ frattini X :=
    normal_odd_le_frattini_of_sl2Two_quotient_of_quotient_not_two
      N hNodd hnpXN hAX
  have hXN : IsSL2Two ((X ⧸ N) ⧸ frattini (X ⧸ N)) :=
    isSL2Two_frattini_quotient_of_normal_le_frattini N hNΦ hAX
  have hY : IsSL2Two ((G ⧸ C) ⧸ frattini (G ⧸ C)) :=
    isSL2Two_frattini_quotient_of_mulEquiv e hXN
  have hcoreX : pCore 2 X = ⊥ := by
    simpa [X, Q] using (pCore_quotient_pCore_eq_bot (G := G))
  have hΦXodd : ¬ 2 ∣ Nat.card (frattini X) :=
    frattini_odd_of_core_eq_bot hcoreX
  let qN : X →* X ⧸ N := QuotientGroup.mk' N
  have hkerN : qN.ker ≤ frattini X := by
    simpa [qN, QuotientGroup.ker_mk'] using hNΦ
  have hmapΦ : (frattini X).map qN = frattini (X ⧸ N) :=
    frattini_map_eq_of_surjective_of_ker_le qN
      (QuotientGroup.mk'_surjective N) hkerN
  have hΦXNodd : ¬ 2 ∣ Nat.card (frattini (X ⧸ N)) := by
    rw [← hmapΦ]
    intro hdvd
    exact hΦXodd (hdvd.trans (Subgroup.card_map_dvd (H := frattini X) qN))
  have hcoreXNle : pCore 2 (X ⧸ N) ≤ frattini (X ⧸ N) :=
    pCore_le_frattini_of_isSL2Two_frattiniQuotient hXN
  have hcoreXN : pCore 2 (X ⧸ N) = ⊥ :=
    pCore_eq_bot_of_le_odd (frattini (X ⧸ N)) hcoreXNle hΦXNodd
  have hcoreY : pCore 2 (G ⧸ C) = ⊥ := by
    have hmapCore := pCore_map_iso 2 e
    rw [← hmapCore, hcoreXN, Subgroup.map_bot]
  refine ⟨hcoreY, ?_⟩
  have hcoreYle : pCore 2 (G ⧸ C) ≤ frattini (G ⧸ C) :=
    pCore_le_frattini_of_isSL2Two_frattiniQuotient hY
  exact isSL2Two_frattini_quotient_of_normal_le_frattini
    (pCore 2 (G ⧸ C)) hcoreYle hY

end Stellmacher.PushingUp
