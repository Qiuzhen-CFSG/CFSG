module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Action.Exclusion.MaximalNormalizer.Basic
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Action.Counting.Contracts
public import FeitThompson.PCore.CentralizerControl

/-!
# The Sylow commutator divisibility in (7D)

Section 3 puts [E,z] in the relative odd core of E. Its solvability and
coprime action make nontrivial p-action visible on its canonical p-layer.
The saturated nontrivial p-subgroup W detects that action; restriction of
any Sylow subgroup of E to [E,z] then detects it in [S,z]. E itself is
allowed to have even order.

Source: GLS, Volume 4, Chapter 2, (7D), following Proposition 7.9.
The canonical-layer and Sylow arguments adapt `SE.Section7Final`, with
coprimeness used only on the odd commutator, and W's original saturation
replacing the stronger assumption that the entire ambient action is coprime.
-/

noncomputable section
namespace BenderSuzuki.ZD
open Theory.GroupTheory PFAppendixIII PFchapter1section1
open scoped Pointwise commutatorElement

/-- A nontrivial p-subgroup in the action commutator of a coprime solvable
action detects nontrivial action on the canonical p-layer. -/
private theorem theorem4b_section7_nontrivial_pCore_quotient_action
    {H A : Type*} [Group H] [Finite H] [Group A] [Finite A]
    [MulDistribMulAction A H]
    (p : ℕ) [Fact p.Prime]
    (hsolv : Group.IsSolvable H)
    (hcoprime : Nat.Coprime (Nat.card A) (Nat.card H))
    {W : Subgroup H} (hWp : IsPGroup p W) (hWne : W ≠ ⊥)
    (hWcomm : W ≤ commutatorAction (A := A) (G := H)) :
    let K : Subgroup H := pPrimeCore p H
    let : IsInvariant A H K := isInvariant_of_characteristic K
    letI : MulDistribMulAction A (H ⧸ K) :=
      quotientMulDistribMulAction (A := A) (G := H) K
        (isInvariant_of_characteristic K)
    let : IsInvariant A (H ⧸ K) (pCore p (H ⧸ K)) :=
      isInvariant_of_characteristic _
    ¬ ActsTrivially (A := A) (G := pCore p (H ⧸ K)) := by
  dsimp only
  let _ : Group.IsSolvable H := hsolv
  let K : Subgroup H := pPrimeCore p H
  let _ : IsInvariant A H K := isInvariant_of_characteristic K
  let _ : MulDistribMulAction A (H ⧸ K) :=
    quotientMulDistribMulAction (A := A) (G := H) K
      (isInvariant_of_characteristic K)
  let _ : IsInvariant A (H ⧸ K) (pCore p (H ⧸ K)) :=
    isInvariant_of_characteristic _
  intro htrivP
  have hsolvQ : Group.IsSolvable (H ⧸ K) := by
    let _ : Group.IsSolvable H := hsolv
    exact Group.isSolvable_of_surjective
      (f := QuotientGroup.mk' K) (QuotientGroup.mk'_surjective K)
  have hcoreQ : pPrimeCore p (H ⧸ K) = ⊥ := by
    simpa [K] using
      (pPrimeCore_quotient_pPrimeCore_eq_bot (G := H) (p := p))
  have hfitQ : fittingSubgroup (H ⧸ K) = pCore p (H ⧸ K) :=
    Fitting_eq_pcore (H ⧸ K) p hcoreQ
  have hcoprimeQ : Nat.Coprime (Nat.card A) (Nat.card (H ⧸ K)) :=
    Nat.Coprime.of_dvd_right (Subgroup.card_quotient_dvd_card K) hcoprime
  have htrivQ : ActsTrivially (A := A) (G := H ⧸ K) := by
    intro a q
    exact section8_element_actsTrivially_of_centralizes_fitting_of_coprime
      hsolvQ hcoprimeQ a (fun f => by
        have hfP : (f : H ⧸ K) ∈ pCore p (H ⧸ K) := by
          rw [← hfitQ]
          exact f.property
        have hf := htrivP a ⟨(f : H ⧸ K), hfP⟩
        exact congrArg Subtype.val hf) q
  have hcomm_le : commutatorAction (A := A) (G := H) ≤ K := by
    rw [commutatorAction_eq_closure (G := H) (A := A)]
    refine (Subgroup.closure_le (K := K)).2 ?_
    rintro x ⟨a, g, rfl⟩
    apply (QuotientGroup.eq_one_iff (N := K) (x := g⁻¹ * (a • g))).mp
    change QuotientGroup.mk' K (g⁻¹ * (a • g)) = 1
    rw [map_mul, map_inv]
    have hmk : QuotientGroup.mk' K (a • g) = QuotientGroup.mk' K g := by
      calc
        QuotientGroup.mk' K (a • g) = a • QuotientGroup.mk' K g := by
          simpa only [QuotientGroup.mk'_apply] using
            (MulAction.Quotient.smul_mk K a g).symm
        _ = QuotientGroup.mk' K g := htrivQ a _
    rw [hmk]
    simp
  have hWK : W ≤ K := hWcomm.trans hcomm_le
  have hpW : p ∣ Nat.card W := by
    rcases hWp.card_eq_or_dvd with hWcard | hpW
    · exact False.elim (hWne (Subgroup.card_eq_one.mp hWcard))
    · exact hpW
  have hpK : p ∣ Nat.card K := dvd_trans hpW (Subgroup.card_dvd_of_le hWK)
  exact ((Nat.Prime.coprime_iff_not_dvd (Fact.out : Nat.Prime p)).1
    (pPrimeCore_coprime_card (G := H) (p := p))) hpK

/-- A nontrivial action on the canonical `p`-layer of `[E,A]` is visible in
the commutator with every Sylow `p`-subgroup of `E`. -/
private theorem theorem4b_section7_p_dvd_commutator_card
    {X : Type*} [Group X] [Finite X]
    (p : ℕ) [Fact p.Prime] (E A : Subgroup X)
    (hA_norm_E : A ≤ Subgroup.normalizer (E : Set X)) :
    let : Subgroup.Normalizes A E := ⟨hA_norm_E⟩
    let H : Subgroup E := commutatorAction (A := A) (G := E)
    let : IsInvariant A E H := commutatorAction_isInvariant
    let K : Subgroup H := pPrimeCore p H
    let : IsInvariant A H K := isInvariant_of_characteristic K
    letI : MulDistribMulAction A (H ⧸ K) :=
      quotientMulDistribMulAction (A := A) (G := H) K
        (isInvariant_of_characteristic K)
    let : IsInvariant A (H ⧸ K) (pCore p (H ⧸ K)) :=
      isInvariant_of_characteristic _
    (∃ a : A, ∃ q : pCore p (H ⧸ K), a • q ≠ q) →
      ∀ S : Sylow p E,
        p ∣ Nat.card (⁅A, (S : Subgroup E).map E.subtype⁆ : Subgroup X) := by
  classical
  dsimp only
  let _ : Subgroup.Normalizes A E := ⟨hA_norm_E⟩
  let H : Subgroup E := commutatorAction (A := A) (G := E)
  let _ : H.Normal := commutatorAction_normal
  let _ : IsInvariant A E H := commutatorAction_isInvariant
  let K : Subgroup H := pPrimeCore p H
  let _ : IsInvariant A H K := isInvariant_of_characteristic K
  let _ : MulDistribMulAction A (H ⧸ K) :=
    quotientMulDistribMulAction (A := A) (G := H) K
      (isInvariant_of_characteristic K)
  let _ : IsInvariant A (H ⧸ K) (pCore p (H ⧸ K)) :=
    isInvariant_of_characteristic _
  intro hnontriv S
  let qH : H →* H ⧸ K := QuotientGroup.mk' K
  let T : Sylow p H :=
    External.hallSylowSubgroupOfNormal S H
  let Tbar : Sylow p (H ⧸ K) :=
    T.mapSurjective (f := qH) (QuotientGroup.mk'_surjective K)
  let U : Subgroup (H ⧸ K) :=
    (Tbar : Subgroup (H ⧸ K)) ⊔ pCore p (H ⧸ K)
  have hsupP : IsPGroup p U := by
    dsimp [U]
    exact IsPGroup.to_sup_of_normal_right Tbar.isPGroup'
      (pCore_isPGroup (G := H ⧸ K) (p := p))
  have hsupEq : U = (Tbar : Subgroup (H ⧸ K)) :=
    Tbar.is_maximal' hsupP (by
      dsimp [U]
      exact le_sup_left)
  have hpcore_le_Tbar : pCore p (H ⧸ K) ≤ Tbar := by
    calc
      pCore p (H ⧸ K) ≤ U := by
        dsimp [U]
        exact le_sup_right
      _ = Tbar := hsupEq
  obtain ⟨a, q, hqmove⟩ := hnontriv
  have hqTbar : (q : H ⧸ K) ∈ (Tbar : Subgroup (H ⧸ K)) :=
    hpcore_le_Tbar q.property
  have hqmap : (q : H ⧸ K) ∈ (T : Subgroup H).map qH := by
    simpa [Tbar] using hqTbar
  rcases hqmap with ⟨t, htT, hqt⟩
  have hqmoveVal : a • (q : H ⧸ K) ≠ (q : H ⧸ K) := by
    intro hfix
    apply hqmove
    exact Subtype.ext hfix
  have htmove : a • qH t ≠ qH t := by
    simpa [hqt] using hqmoveVal
  let c : H := t⁻¹ * (a • t)
  have hqc : qH c = (qH t)⁻¹ * (a • qH t) := by
    simp [c, qH]
  have hqc_ne : qH c ≠ 1 := by
    intro hc1
    apply htmove
    have hinv : (qH t)⁻¹ * (a • qH t) = 1 := by
      simpa [hqc] using hc1
    exact (eq_of_inv_mul_eq_one hinv).symm
  have hqtP : qH t ∈ pCore p (H ⧸ K) := by
    rw [hqt]
    exact q.property
  have haqtP : a • qH t ∈ pCore p (H ⧸ K) :=
    (IsInvariant.invariant (A := A) (G := H ⧸ K)
      (H := pCore p (H ⧸ K)) a (qH t)).1 hqtP
  have hqcP : qH c ∈ pCore p (H ⧸ K) := by
    rw [hqc]
    exact (pCore p (H ⧸ K)).mul_mem
      ((pCore p (H ⧸ K)).inv_mem hqtP) haqtP
  let cP : pCore p (H ⧸ K) := ⟨qH c, hqcP⟩
  have hcP_ne : cP ≠ 1 := by
    intro hcP
    exact hqc_ne (congrArg Subtype.val hcP)
  obtain ⟨n, hn⟩ :=
    (IsPGroup.iff_orderOf.mp
      (pCore_isPGroup (G := H ⧸ K) (p := p))) cP
  have hn_ne : n ≠ 0 := by
    intro hn0
    subst n
    have hcP_order : orderOf cP = 1 := by simpa using hn
    exact hcP_ne (orderOf_eq_one_iff.mp hcP_order)
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn_ne
  have hp_order_cP : p ∣ orderOf cP := by
    rw [hn]
    simp [pow_succ]
  have hp_order_qc : p ∣ orderOf (qH c) := by
    rw [show orderOf (qH c) = orderOf cP from Subgroup.orderOf_coe cP]
    exact hp_order_cP
  have hp_order_c : p ∣ orderOf c :=
    dvd_trans hp_order_qc (orderOf_map_dvd qH c)
  have htS : (t : E) ∈ (S : Subgroup E) := by
    simpa [T, External.hallSylowSubgroupOfNormal_coe,
      Subgroup.mem_subgroupOf] using htT
  have htSX : (t : X) ∈ (S : Subgroup E).map E.subtype :=
    Subgroup.mem_map_of_mem E.subtype htS
  have hcComm : (c : X) ∈
      ⁅(S : Subgroup E).map E.subtype, A⁆ := by
    have hgen : ⁅(t : X)⁻¹, (a : X)⁆ ∈
        ⁅(S : Subgroup E).map E.subtype, A⁆ :=
      Subgroup.commutator_mem_commutator
        (H₁ := (S : Subgroup E).map E.subtype) (H₂ := A)
        (((S : Subgroup E).map E.subtype).inv_mem htSX) a.property
    have hsmul : ((a • t : H) : X) =
        (a : X) * (t : X) * (a : X)⁻¹ := by
      change ((a • (t : E) : E) : X) =
        (a : X) * (t : X) * (a : X)⁻¹
      exact Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe
        A E a (t : E)
    change (t : X)⁻¹ * ((a • t : H) : X) ∈
      ⁅(S : Subgroup E).map E.subtype, A⁆
    rw [hsmul]
    simpa [commutatorElement_def, mul_assoc] using hgen
  have hp_order_cX : p ∣ orderOf (c : X) := by
    simpa only [Subgroup.orderOf_coe] using hp_order_c
  let C : Subgroup X := ⁅(S : Subgroup E).map E.subtype, A⁆
  let cComm : C := ⟨(c : X), hcComm⟩
  have hp_card_comm : p ∣ Nat.card C := by
    apply dvd_trans hp_order_cX
    have horder : orderOf (c : X) = orderOf cComm := by
      simp [cComm]
    rw [horder]
    exact orderOf_dvd_natCard cComm
  simpa only [C, Subgroup.commutator_comm] using hp_card_comm


variable {G : Type*} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}

/-- The relevant commutator is odd, even when the triple stabilizer is not. -/
public theorem action_triple_commutator_odd
    (h : IsProductDisconnected Z M) (h3 : ActionSectionThree Z M)
    (d : ActionCounterexample Z M) {beta : G ⧸ M}
    (hne : beta ≠ QuotientGroup.mk 1) :
    Odd (Nat.card (⁅theorem4bSection7E M d.z beta, Subgroup.zpowers d.z⁆ : Subgroup G)) := by
  let E := theorem4bSection7E M d.z beta
  have hzMove : d.z • beta ≠ beta :=
    fun he => hne (action_fixedPoint_eq_base h d.hzZ d.hzM he)
  have hc : ⁅E, Subgroup.zpowers d.z⁆ ≤ (pPrimeCore 2 E).map E.subtype := by
    apply h3.swapping_core d.z d.hzZ beta hzMove
    · exact le_inf (inf_le_left.trans inf_le_right) inf_le_right
    · exact theorem4b_mem_normalizer_tripleStabilizer d.hz d.hzM
  have ho : Odd (Nat.card ((pPrimeCore 2 E).map E.subtype)) := by
    rw [Subgroup.card_map_of_injective E.subtype_injective]
    exact (pPrimeCore_coprime_card (G := E) (p := 2)).odd_of_left
  exact ho.of_dvd_nat (Subgroup.card_dvd_of_le hc)

/-- The nontrivial saturated p-subgroup W detects the action on the
canonical p-layer of the odd commutator [E,z]. -/
private theorem action_nontrivial_pCore_quotient_action
    (h : IsProductDisconnected Z M) (h3 : ActionSectionThree Z M)
    (d : ActionCounterexample Z M) {beta : G ⧸ M}
    (hb : beta ∈ d.toTheorem4bSixA.kFixedPoints)
    (hne : beta ≠ QuotientGroup.mk 1) :
    let E : Subgroup G := theorem4bSection7E M d.z beta
    let A : Subgroup G := Subgroup.zpowers d.z
    let : Subgroup.Normalizes A E := ⟨Subgroup.zpowers_le.mpr
      (theorem4b_mem_normalizer_tripleStabilizer d.hz d.hzM)⟩
    let H : Subgroup E := commutatorAction (A := A) (G := E)
    let : IsInvariant A E H := commutatorAction_isInvariant
    let K : Subgroup H := pPrimeCore d.p H
    let : IsInvariant A H K := isInvariant_of_characteristic K
    letI : MulDistribMulAction A (H ⧸ K) :=
      quotientMulDistribMulAction (A := A) (G := H) K (isInvariant_of_characteristic K)
    let : IsInvariant A (H ⧸ K) (pCore d.p (H ⧸ K)) := isInvariant_of_characteristic _
    ∃ a : A, ∃ q : pCore d.p (H ⧸ K), a • q ≠ q := by
  classical
  dsimp only
  let : Fact d.p.Prime := ⟨d.hp⟩
  let E : Subgroup G := theorem4bSection7E M d.z beta
  let A : Subgroup G := Subgroup.zpowers d.z
  have hA_norm_E : A ≤ Subgroup.normalizer (E : Set G) :=
    Subgroup.zpowers_le.mpr (theorem4b_mem_normalizer_tripleStabilizer d.hz d.hzM)
  let : Subgroup.Normalizes A E := ⟨hA_norm_E⟩
  let H : Subgroup E := commutatorAction (A := A) (G := E)
  let : IsInvariant A E H := commutatorAction_isInvariant
  let K : Subgroup H := pPrimeCore d.p H
  let : IsInvariant A H K := isInvariant_of_characteristic K
  let : MulDistribMulAction A (H ⧸ K) :=
    quotientMulDistribMulAction (A := A) (G := H) K (isInvariant_of_characteristic K)
  let : IsInvariant A (H ⧸ K) (pCore d.p (H ⧸ K)) := isInvariant_of_characteristic _
  have hmapComm : H.map E.subtype = ⁅E, A⁆ :=
    commutatorAction_subgroup_conj_map_eq_commutator E A hA_norm_E
  have hHodd : Odd (Nat.card H) := by
    rw [← Subgroup.card_map_of_injective E.subtype_injective (K := H), hmapComm]
    exact action_triple_commutator_odd h h3 d hne
  have hHsolv : Group.IsSolvable H := odd_order_theorem H hHodd
  have horder : orderOf d.z = 2 :=
    (orderOf_eq_prime_iff).2 ⟨d.hz.sq_eq_one, d.hz.ne_one⟩
  have hcopAH : Nat.Coprime (Nat.card A) (Nat.card H) := by
    rw [show Nat.card A = 2 by simp [A, Nat.card_zpowers, horder]]
    exact hHodd.coprime_two_left
  let WE : Subgroup E := d.W.subgroupOf E
  have hWEleH : WE ≤ H := by
    intro w hw
    have hwComm : (w : G) ∈ ⁅E, A⁆ := d.le_triple_commutator hb hw
    rw [← hmapComm] at hwComm
    obtain ⟨y, hy, hyw⟩ := hwComm
    simpa [E.subtype_injective hyw] using hy
  let WH : Subgroup H := WE.subgroupOf H
  have hWEp : IsPGroup d.p WE :=
    d.hWp.of_equiv (Subgroup.subgroupOfEquivOfLe (d.le_triple_stabilizer hb)).symm
  have hWHp : IsPGroup d.p WH :=
    hWEp.of_equiv (Subgroup.subgroupOfEquivOfLe hWEleH).symm
  have hWEne : WE ≠ ⊥ := by
    intro hbot
    exact d.hWne ((Subgroup.subgroupOf_eq_bot.mp hbot).eq_bot_of_le (d.le_triple_stabilizer hb))
  have hWHne : WH ≠ ⊥ := by
    intro hbot
    exact hWEne ((Subgroup.subgroupOf_eq_bot.mp hbot).eq_bot_of_le hWEleH)
  let f : H →* G := E.subtype.comp H.subtype
  have hf : Function.Injective f := E.subtype_injective.comp H.subtype_injective
  have hWimage : d.W ≤ (commutatorAction (A := A) (G := H)).map f := by
    rw [← d.hcomm]
    apply Subgroup.commutator_le.mpr
    intro w hw a ha
    let wE : E := ⟨w, d.le_triple_stabilizer hb hw⟩
    let wH : H := ⟨wE, hWEleH hw⟩
    let aA : A := ⟨a, ha⟩
    refine Subgroup.mem_map.mpr ⟨wH * (aA • wH⁻¹), ?_, ?_⟩
    · rw [commutatorAction_eq_closure]
      exact Subgroup.subset_closure ⟨aA, wH⁻¹, by simp⟩
    · change w * (↑(aA • (wE⁻¹)) : G) = ⁅w, a⁆
      rw [Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe]
      simp [aA, wE, commutatorElement_def, mul_assoc]
  have hWHcomm : WH ≤ commutatorAction (A := A) (G := H) := by
    intro w hw
    obtain ⟨v, hv, hvw⟩ := hWimage hw
    exact hf hvw ▸ hv
  have hnot := theorem4b_section7_nontrivial_pCore_quotient_action
    (H := H) (A := A) d.p hHsolv hcopAH hWHp hWHne hWHcomm
  by_contra hn
  apply hnot
  intro a q
  by_contra hq
  exact hn ⟨a, q, hq⟩

/-- Equation (7D), retaining the original prime and distinguished involution. -/
public theorem action_sevenD
    (h : IsProductDisconnected Z M) (h3 : ActionSectionThree Z M)
    (d : ActionCounterexample Z M) {beta : G ⧸ M}
    (hb : beta ∈ d.toTheorem4bSixA.kFixedPoints)
    (hne : beta ≠ QuotientGroup.mk 1) :
    ∀ S : Subgroup G,
      theorem4bIsSylowSubgroupOf d.p S (theorem4bSection7E M d.z beta) →
      d.p ∣ Nat.card (⁅Subgroup.zpowers d.z, S⁆ : Subgroup G) := by
  let : Fact d.p.Prime := ⟨d.hp⟩
  intro S hS
  let E : Subgroup G := theorem4bSection7E M d.z beta
  let A : Subgroup G := Subgroup.zpowers d.z
  have hn : A ≤ Subgroup.normalizer (E : Set G) :=
    Subgroup.zpowers_le.mpr (theorem4b_mem_normalizer_tripleStabilizer d.hz d.hzM)
  obtain ⟨SE, hSE⟩ := hS
  have hdvd := theorem4b_section7_p_dvd_commutator_card d.p E A hn
    (action_nontrivial_pCore_quotient_action h h3 d hb hne) SE
  simpa only [hSE] using hdvd

end BenderSuzuki.ZD
