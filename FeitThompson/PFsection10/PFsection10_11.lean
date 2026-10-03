module

public import FeitThompson.PFsection10.PFsection10_10
import FeitThompson.PFsection8.PFsection8_8

noncomputable section

open scoped BigOperators

attribute [local instance] Fintype.ofFinite

namespace Section10
universe u v w
open Section1 Section2 Section3 Section4

/-!
# Peterfalvi, Section 10: Theorem (10.11)
-/

private theorem isElementaryAbelian_of_mulEquiv
    {A B : Type*}
    [Group A]
    [Group B]
    {p : ℕ}
    (e : A ≃* B)
    [IsElementaryAbelian p A] :
    IsElementaryAbelian p B := by
  refine
    { toIsMulCommutative := ?_
      exponent_dvd_p := ?_ }
  · refine ⟨⟨?_⟩⟩
    intro b₁ b₂
    apply e.symm.injective
    have hcommA : IsMulCommutative A :=
      (inferInstance : IsElementaryAbelian p A).toIsMulCommutative
    simpa using hcommA.is_comm.comm (e.symm b₁) (e.symm b₂)
  · refine Monoid.exponent_dvd_iff_forall_pow_eq_one.2 ?_
    intro b
    apply e.symm.injective
    have hpow := Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p p A) (e.symm b)
    simpa using hpow

private theorem nat_prime_card_of_section16HasPrimeOrder
    {G : Type u}
    [Group G]
    [Finite G]
    {H : Subgroup G}
    (h : section16HasPrimeOrder H) :
    Nat.Prime (Nat.card H) := by
  rcases h with ⟨p, hp⟩
  rw [hp]
  exact p.property


private theorem section12ComplementIn_isComplement'_subgroupOf_right
    {G : Type u}
    [Group G]
    [Finite G]
    {M K L : Subgroup G}
    (hcomp : section12ComplementIn M K L)
    [hKNormal : (K.subgroupOf M).Normal] :
    (L.subgroupOf M).IsComplement' (K.subgroupOf M) := by
  rcases hcomp with ⟨hKM, hLM, hsup, hdisj⟩
  have hsup_local : L.subgroupOf M ⊔ K.subgroupOf M = ⊤ := by
    calc
      L.subgroupOf M ⊔ K.subgroupOf M = (L ⊔ K).subgroupOf M := by
        symm
        exact Subgroup.subgroupOf_sup (A := L) (A' := K) (B := M) hLM hKM
      _ = ⊤ := by
        rw [sup_comm, hsup]
        simp
  refine Subgroup.isComplement'_of_disjoint_and_mul_eq_univ ?_ ?_
  · rw [Subgroup.disjoint_def]
    intro x hxL hxK
    apply Subtype.ext
    exact hdisj.le_bot ⟨by simpa [Subgroup.mem_subgroupOf] using hxK,
      by simpa [Subgroup.mem_subgroupOf] using hxL⟩
  · simpa [hsup_local] using
      (Subgroup.mul_normal (L.subgroupOf M) (K.subgroupOf M)).symm

private theorem section12ComplementIn_left_relIndex_eq_card_right
    {G : Type u}
    [Group G]
    [Finite G]
    {M K L : Subgroup G}
    (hcomp : section12ComplementIn M K L)
    [hKNormal : (K.subgroupOf M).Normal] :
    K.relIndex M = Nat.card L := by
  have hcompLocal : (L.subgroupOf M).IsComplement' (K.subgroupOf M) :=
    section12ComplementIn_isComplement'_subgroupOf_right hcomp
  calc
    K.relIndex M = (K.subgroupOf M).index := rfl
    _ = Nat.card (L.subgroupOf M) := hcompLocal.index_eq_card
    _ = Nat.card L := natCard_subgroupOf_eq L M hcomp.2.1

private theorem nat_prime_card_first_of_section16TypeCommon_and_source_typeP
    {G : Type u}
    [Group G]
    [Finite G]
    {M MF U W1 W2 U' W1' W2' : Subgroup G}
    (hCommon : section16TypeCommon M MF U W1 W2)
    (hP : Section8.typePDefinitionData M MF U' W1' W2')
    (hExtra : Section8.typeIIToIVSourceCondition M U' W1') :
    Nat.Prime (Nat.card W1) := by
  rcases hCommon with
    ⟨_hHallD, _hMFleD, _hComp, _hVnil, _hW1norm, _hW1cyc, hW1card,
      _hMFnotCyclic, _hSecondLe, _hFittingEq, _hFittingLeD, _hW2le,
      _hW2ne, _hW2cyc, _hCentralizer, _hHatW, _hT6⟩
  rcases hP with
    ⟨_hMF, _hW1cyc, _hW1ne, _hW1Hall, hW1comp, _hUleD, _hUnil,
      _hW1norm, _hCompMFU, _hMFnotCyclic, _hSecondLe, _hFittingEq,
      _hFittingLeD, _hW2le, _hW2cyc, _hW2ne, _hCentralizer, _hHatW⟩
  have hDnorm : ((ambientDerivedSubgroup M).subgroupOf M).Normal := by
    simpa using (section12_normalIn_ambientDerivedSubgroup (G := G) (E := M)).2
  let _ : ((ambientDerivedSubgroup M).subgroupOf M).Normal := hDnorm
  have hW1card' :
      (ambientDerivedSubgroup M).relIndex M = Nat.card W1' :=
    section12ComplementIn_left_relIndex_eq_card_right hW1comp
  have hcard : Nat.card W1 = Nat.card W1' := by
    rw [hW1card, hW1card']
  rw [hcard]
  exact nat_prime_card_of_section16HasPrimeOrder hExtra.2.1

private theorem nat_prime_card_first_of_section16TypeCommon_and_source_typeIIToIV
    {G : Type u}
    [Group G]
    [Finite G]
    {M MF U W1 W2 : Subgroup G}
    (hCommon : section16TypeCommon M MF U W1 W2)
    (hType :
      Section8.typeIIDefinitionData M MF ∨
        Section8.typeIIIDefinitionData M MF ∨
          Section8.typeIVDefinitionData M MF) :
    Nat.Prime (Nat.card W1) := by
  rcases hType with hII | hRest
  · rcases hII with
      ⟨U', W1', W2', _U1, _U0, hP, hExtra, _hComm, _hNorm, _hF⟩
    exact nat_prime_card_first_of_section16TypeCommon_and_source_typeP
      hCommon hP hExtra
  · rcases hRest with hIII | hIV
    · rcases hIII with ⟨U', W1', W2', hP, hExtra, _hComm, _hNorm⟩
      exact nat_prime_card_first_of_section16TypeCommon_and_source_typeP
        hCommon hP hExtra
    · rcases hIV with ⟨U', W1', W2', hP, hExtra, _hComm, _hNorm⟩
      exact nat_prime_card_first_of_section16TypeCommon_and_source_typeP
        hCommon hP hExtra

private theorem theorem_10_11_case_b_prime_pair_bridge
    {G : Type u}
    [Group G]
    [Finite G]
    [IsMinCE G]
    {W W1 W2 Smax Tmax SF TF : Subgroup G}
    (h88 : Section8.theorem_8_8_case_b_data W W1 W2 Smax Tmax SF TF) :
    Nat.Prime (Nat.card W1) ∧ Nat.Prime (Nat.card W2) := by
  have h88Source := Section8.theorem_8_8_source_type_fields_of_case_b_data h88
  rcases h88 with
    ⟨_hProd, _hWcyc, _hW1ne, _hW2ne, _hNormalizer, hSmax, hTmax,
      hSF, hTF, _hSnotI, _hTnotI, _hSeq, _hTeq, _hSmeet, _hTmeet, _hST,
      _hMaxSplit, _hMeet, _hCover, _hTypeIIone, _hSAlt, _hTAlt, hCommons⟩
  rcases hCommons with ⟨_US, _UT, hSCommon, hTCommon⟩
  rcases h88Source with
    ⟨_hTypeIIoneSource, hSAltSource, hTAltSource, _hCoverSource⟩
  have hSnotV : ¬ Section8.typeVDefinitionData Smax SF := by
    intro hTypeV
    exact theorem_10_10 ⟨Smax, SF, hSmax, hSF, hTypeV⟩
  have hTnotV : ¬ Section8.typeVDefinitionData Tmax TF := by
    intro hTypeV
    exact theorem_10_10 ⟨Tmax, TF, hTmax, hTF, hTypeV⟩
  have dropTypeV :
      ∀ {N NF : Subgroup G},
        ¬ Section8.typeVDefinitionData N NF →
          (Section8.typeIIDefinitionData N NF ∨
            Section8.typeIIIDefinitionData N NF ∨
              Section8.typeIVDefinitionData N NF ∨
                Section8.typeVDefinitionData N NF) →
          Section8.typeIIDefinitionData N NF ∨
            Section8.typeIIIDefinitionData N NF ∨
              Section8.typeIVDefinitionData N NF := by
    intro N NF hnotV hAlt
    rcases hAlt with hII | hIII | hIV | hV
    · exact Or.inl hII
    · exact Or.inr (Or.inl hIII)
    · exact Or.inr (Or.inr hIV)
    · exact (hnotV hV).elim
  have hSType :
      Section8.typeIIDefinitionData Smax SF ∨
        Section8.typeIIIDefinitionData Smax SF ∨
          Section8.typeIVDefinitionData Smax SF := by
    exact dropTypeV hSnotV hSAltSource
  have hTType :
      Section8.typeIIDefinitionData Tmax TF ∨
        Section8.typeIIIDefinitionData Tmax TF ∨
          Section8.typeIVDefinitionData Tmax TF := by
    exact dropTypeV hTnotV hTAltSource
  exact
    ⟨nat_prime_card_first_of_section16TypeCommon_and_source_typeIIToIV hSCommon hSType,
      nat_prime_card_first_of_section16TypeCommon_and_source_typeIIToIV hTCommon hTType⟩

private theorem theorem_10_11_card_of_typeII_hypothesis
    {G : Type u}
    [Group G]
    [Finite G]
    [IsMinCE G]
    {M MF U W1 W2 H0 C Cprime : Subgroup G}
    {S : Finset (Section1.ClassFunction M)}
    {τ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    (h95 : Section9.Hypothesis_9_5 M MF U W1 W2 H0 C Cprime τ S)
    (hTypeII : section16TypeII M MF) :
    Nat.card MF = Nat.card W2 ^ Nat.card W1 := by
  have h92 : Section9.hypothesis_9_2_statement M MF U W1 W2 (Nat.card W1) :=
    h95.hypothesis92
  exact ((Section9.theorem_9_3 M MF U W1 W2 (Nat.card W1) h92).1 hTypeII).2

private theorem theorem_10_11_elementary_of_typeII_hypothesis
    {G : Type u}
    [Group G]
    [Finite G]
    [IsMinCE G]
    {M MF U W1 W2 H0 C Cprime : Subgroup G}
    {S : Finset (Section1.ClassFunction M)}
    {τ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    (hW1prime : Nat.Prime (Nat.card W1))
    (hW2prime : Nat.Prime (Nat.card W2))
    (h95 : Section9.Hypothesis_9_5 M MF U W1 W2 H0 C Cprime τ S)
    (hTypeII : section16TypeII M MF) :
    IsElementaryAbelian (Nat.card W2) MF := by
  have h92 : Section9.hypothesis_9_2_statement M MF U W1 W2 (Nat.card W1) :=
    h95.hypothesis92
  have hcardMF : Nat.card MF = Nat.card W2 ^ Nat.card W1 :=
    ((Section9.theorem_9_3 M MF U W1 W2 (Nat.card W1) h92).1 hTypeII).2
  rcases Section9.theorem_9_6 M MF U W1 W2 H0 C Cprime τ S h95 with
    ⟨_hUC, p, hpdata, h96⟩
  rcases h96 with
    ⟨_hH0le96, _hMFle96, _hH0normal96, _hchief, _hWbar, hquotcard⟩
  have hquotDvdMF : Nat.card (MF ⧸ H0.subgroupOf MF) ∣ Nat.card MF :=
    Subgroup.card_quotient_dvd_card (s := H0.subgroupOf MF)
  have hpPowDvd : p.val ^ Nat.card W1 ∣ Nat.card W2 ^ Nat.card W1 := by
    rw [hquotcard, hcardMF] at hquotDvdMF
    exact hquotDvdMF
  have hqne : Nat.card W1 ≠ 0 := hW1prime.pos.ne'
  have hpDvdPow : p.val ∣ Nat.card W2 ^ Nat.card W1 :=
    (dvd_pow_self p.val hqne).trans hpPowDvd
  have hp_eq_w2 : p.val = Nat.card W2 :=
    Nat.prime_eq_prime_of_dvd_pow p.property hW2prime hpDvdPow
  rcases hpdata with
    ⟨_hH0leMF, _hMFleM, _hH0normalM, _hH0normalMF, _hH0lt, hquotElem,
      _htypeIIIIV⟩
  rcases hquotElem with ⟨hnormal, hElemQuot⟩
  have _ : (H0.subgroupOf MF).Normal := hnormal
  have hlag :
      Nat.card MF =
        Nat.card (MF ⧸ H0.subgroupOf MF) * Nat.card (H0.subgroupOf MF) :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup (s := H0.subgroupOf MF)
  have hpow_eq_mul :
      Nat.card W2 ^ Nat.card W1 =
        Nat.card W2 ^ Nat.card W1 * Nat.card (H0.subgroupOf MF) := by
    calc
      Nat.card W2 ^ Nat.card W1 = Nat.card MF := hcardMF.symm
      _ = Nat.card (MF ⧸ H0.subgroupOf MF) * Nat.card (H0.subgroupOf MF) :=
        hlag
      _ = Nat.card W2 ^ Nat.card W1 * Nat.card (H0.subgroupOf MF) := by
        rw [hquotcard, hp_eq_w2]
  have hpowPos : 0 < Nat.card W2 ^ Nat.card W1 := pow_pos hW2prime.pos _
  have hcardH0sub : Nat.card (H0.subgroupOf MF) = 1 := by
    refine Nat.eq_of_mul_eq_mul_left hpowPos ?_
    simpa using hpow_eq_mul.symm
  have hH0sub_bot : H0.subgroupOf MF = ⊥ :=
    Subgroup.eq_bot_of_card_eq (H0.subgroupOf MF) hcardH0sub
  let e : MF ⧸ H0.subgroupOf MF ≃* MF :=
    (QuotientGroup.quotientMulEquivOfEq hH0sub_bot).trans
      (QuotientGroup.quotientBot (G := MF))
  have _ : IsElementaryAbelian p.val (MF ⧸ H0.subgroupOf MF) := hElemQuot
  have hElemMF : IsElementaryAbelian p.val MF :=
    isElementaryAbelian_of_mulEquiv e
  simpa [hp_eq_w2] using hElemMF

private theorem theorem_10_11_coherent_of_typeII_hypothesis
    {G : Type u}
    [Group G]
    [Finite G]
    [IsMinCE G]
    {M MF U W1 W2 H0 C Cprime : Subgroup G}
    {S : Finset (Section1.ClassFunction M)}
    {τ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    (hbridge :
      Section9.theorem_9_11_hypothesis52BridgeData M MF U W1 W2 H0 C Cprime τ S)
    (h95 : Section9.Hypothesis_9_5 M MF U W1 W2 H0 C Cprime τ S)
    (hTypeII : section16TypeII M MF) :
    Section6.coherentFamily S τ := by
  have h95full := h95
  rcases h95 with
    ⟨h92, _hp, hCU, _hbarU, _hCprime_le, hCprimeEq, _hDade, hS, _h52b⟩
  have hUcomm : IsMulCommutative U := (h92.typeIISource hTypeII).1
  have hCcomm : IsMulCommutative C := by
    let _ : IsMulCommutative U := hUcomm
    refine ⟨⟨?_⟩⟩
    intro a b
    exact Subtype.ext (setLike_mul_comm (s := U)
      (hCU.1 a.2) (hCU.1 b.2))
  have hCcomm_bot : _root_.commutator C = ⊥ := by
    let _ : IsMulCommutative C := hCcomm
    exact _root_.commutator_eq_bot C
  have hCprime_bot : Cprime = ⊥ := by
    rw [hCprimeEq, hCcomm_bot, Subgroup.map_bot]
  have hSH0Cprime :
      Section9.kernelInducedFamily M (ambientDerivedSubgroup M) MF (H0 ⊔ Cprime) S := by
    simpa [hCprime_bot] using hS
  have hcohForT : Section9.coherentFamilyForT M S τ :=
    Section9.theorem_9_11_of_hypothesis52BridgeData M MF U W1 W2 H0 C Cprime τ S S
      hbridge h95full hSH0Cprime
  simpa [Section9.coherentFamilyForT] using hcohForT

/-- Proof placeholder for `theorem_10_11_statement`. -/
public theorem theorem_10_11
    {G : Type u}
    [Group G]
    [Finite G]
    [IsMinCE G]
    (W W1 W2 Smax Tmax SF TF M MF U H0 C Cprime : Subgroup G)
    (S : Finset (Section1.ClassFunction M))
    (τ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G)
  : Section8.theorem_8_8_case_b_data W W1 W2 Smax Tmax SF TF →
      Nat.Prime (Nat.card W1) ∧
        Nat.Prime (Nat.card W2) ∧
        (Section9.theorem_9_11_hypothesis52BridgeData M MF U W1 W2 H0 C Cprime τ S →
          Section9.Hypothesis_9_5 M MF U W1 W2 H0 C Cprime τ S →
            section16TypeII M MF →
              typeIIElementaryConclusion M MF W1 W2 S τ) := by
  intro h88
  rcases theorem_10_11_case_b_prime_pair_bridge h88 with ⟨hW1prime, hW2prime⟩
  refine ⟨hW1prime, hW2prime, ?_⟩
  intro hbridge h95 hTypeII
  exact
    ⟨theorem_10_11_elementary_of_typeII_hypothesis hW1prime hW2prime h95 hTypeII,
      theorem_10_11_card_of_typeII_hypothesis h95 hTypeII,
      theorem_10_11_coherent_of_typeII_hypothesis hbridge h95 hTypeII⟩
end Section10
