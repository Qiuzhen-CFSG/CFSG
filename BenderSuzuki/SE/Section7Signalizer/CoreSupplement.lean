module
public import Theory.GroupTheory.PPrimeCorePGroupExtension
public import Theory.GroupTheory.PGroup.CharacteristicKernel
public import Theory.GroupTheory.PPrimeCoreSupplement
public import BenderSuzuki.SE.Section7Signalizer
public import BenderSuzuki.SE.Section7

/-!
# The signalizer comparison with an even two-point stabilizer

Suppose E supplements O_{2'}(D), and a p-subgroup W of D satisfies
W C_D(W) ≤ E. Work inside the odd subgroup H = W O_{2'}(D), and apply
the existing Thompson–Bender argument to E ∩ H. The supplement identity
puts theta(E) in H, so restriction preserves it. Since H/O_{2'}(D) is a
p-group, the actual p'-core of H equals theta(D), giving theta(E) ≤ theta(D).

Neither D nor E is required to have odd order. The subgroup inclusions and
core equality are transported through the original ambient inclusion maps.
Source: GLS, Volume 4, Chapter 2, Lemma 7.6, printed p.48.
-/

noncomputable section
namespace BenderSuzuki
variable {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

omit [Finite G] in
private theorem oddCore_eq_self (H : Subgroup G) (hodd : Odd (Nat.card H)) :
    corollary64OddCore H = H := by
  have htop : twoPrimeCore H = ⊤ := by
    apply top_unique
    exact le_sSup ⟨inferInstance, by simpa using hodd.coprime_two_left⟩
  simp only [corollary64OddCore, htop, ← MonoidHom.range_eq_map, Subgroup.range_subtype]

private theorem core_image_eq (N H : Subgroup G) (hNH : N ≤ H)
    [(N.subgroupOf H).Normal] (hQ : IsPGroup p (H ⧸ N.subgroupOf H)) :
    (pPrimeCore p H).map H.subtype = (pPrimeCore p N).map N.subtype := by
  rw [← pPrimeCore_map_eq_of_isPGroup_quotient p (N.subgroupOf H) hQ,
    Subgroup.map_map]
  let e := Subgroup.subgroupOfEquivOfLe hNH
  have he : H.subtype.comp (N.subgroupOf H).subtype = N.subtype.comp e.toMonoidHom := rfl
  rw [he, ← Subgroup.map_map, pPrimeCore_map_iso]

/-- Lemma 7.6 with the odd-core supplement explicit. The p-subgroup need
not lie in the odd core, and the two-point group D may have even order. -/
public theorem theta_le_of_pgroup_centralizer_le_supplement
    {D E : Subgroup G} (hpodd : p ≠ 2) (hED : E ≤ D)
    (hsup : D = corollary64OddCore D ⊔ (D ⊓ E))
    (W : Subgroup D) (hWp : IsPGroup p W)
    (hWE : W ⊔ Subgroup.centralizer (W : Set D) ≤ E.subgroupOf D) :
    corollary64Theta p E ≤ corollary64Theta p D := by
  let O := corollary64OddCore D
  let V := W.map D.subtype
  let H := V ⊔ O
  let E1 := E ⊓ H
  have hOD : O ≤ D := Subgroup.map_subtype_le _
  have hVD : V ≤ D := Subgroup.map_subtype_le _
  have hVH : V ≤ H := le_sup_left
  have hOH : O ≤ H := le_sup_right
  have hHD : H ≤ D := sup_le hVD hOD
  have hVE : V ≤ E := by
    rintro x ⟨w, hw, rfl⟩
    exact hWE (Subgroup.mem_sup_left hw)
  have hVp : IsPGroup p V := hWp.map D.subtype
  have hDN : D ≤ Subgroup.normalizer (O : Set G) := by
    have hn := section8_normalizer_map_subtype_le_of_characteristic
      (H := D) (K := pPrimeCore 2 D)
    exact Subgroup.le_normalizer.trans hn
  let : (O.subgroupOf H).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer (hHD.trans hDN)
  have hQ : IsPGroup p (H ⧸ O.subgroupOf H) := by
    apply Subgroup.quotient_isPGroup_of_sup_eq_top (V.subgroupOf H)
      (O.subgroupOf H) hVp.comap_subtype
    rw [← Subgroup.subgroupOf_sup hVH hOH]
    exact Subgroup.subgroupOf_self H
  have hOodd : Odd (Nat.card O) := by
    have he : Nat.card O = Nat.card (pPrimeCore 2 D) :=
      Subgroup.card_map_of_injective D.subtype_injective
    rw [he]
    exact (pPrimeCore_coprime_card (p := 2) (G := D)).odd_of_left
  have hHodd : Odd (Nat.card H) := by
    obtain ⟨n, hn⟩ := hQ.exists_card_eq
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (O.subgroupOf H), hn,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hOH).toEquiv]
    exact (show Odd (p ^ n) from ((Fact.out : Nat.Prime p).odd_of_ne_two hpodd).pow).mul hOodd
  have hcoreEq : (pPrimeCore p H).map H.subtype = corollary64Theta p D :=
    core_image_eq O H hOH hQ
  have hthetaEq : corollary64Theta p H = corollary64Theta p D := by
    rw [corollary64Theta, oddCore_eq_self H hHodd]
    exact hcoreEq
  have hThetaOE : corollary64Theta p E ≤ corollary64OddCore E :=
    Subgroup.map_subtype_le _
  have hThetaE : corollary64Theta p E ≤ E :=
    hThetaOE.trans (Subgroup.map_subtype_le _)
  have hThetaO : corollary64Theta p E ≤ O := by
    exact (le_inf (hThetaE.trans hED) hThetaOE).trans
      (Subgroup.inf_pPrimeCore_map_le_of_supplement D E hsup)
  have hThetaE1 : corollary64Theta p E ≤ E1 :=
    le_inf hThetaE (hThetaO.trans hOH)
  have hfirst : corollary64Theta p E ≤ corollary64Theta p E1 :=
    theorem4b_lemma75_theta_le_theta_of_le inf_le_left hThetaE1
  let WH := V.subgroupOf H
  have hcentral : WH ⊔ Subgroup.centralizer (WH : Set H) ≤ E1.subgroupOf H := by
    apply sup_le
    · intro x hx
      exact ⟨hVE hx, x.property⟩
    · intro x hx
      have hxD : (x : G) ∈ D := hHD x.property
      have hxCD : (⟨(x : G), hxD⟩ : D) ∈ Subgroup.centralizer (W : Set D) := by
        rw [Subgroup.mem_centralizer_iff]
        intro w hw
        have hwV : (w : G) ∈ V := Subgroup.mem_map.mpr ⟨w, hw, rfl⟩
        let wH : H := ⟨w, hVH hwV⟩
        have hc := Subgroup.mem_centralizer_iff.mp hx wH (show wH ∈ WH from hwV)
        exact Subtype.ext (congrArg (fun a : H => (a : G)) hc)
      have hxE : (x : G) ∈ E := hWE (Subgroup.mem_sup_right hxCD)
      exact ⟨hxE, x.property⟩
  have hlast : corollary64Theta p E1 ≤ corollary64Theta p H :=
    theorem4b_lemma76_of_pgroup_centralizer_le_E hpodd hHodd inf_le_right
      WH hVp.comap_subtype hcentral
  exact hfirst.trans (hthetaEq ▸ hlast)
end BenderSuzuki
