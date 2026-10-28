module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Action.Exclusion.Generation.Proposition63.Induction
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Action.Exclusion.Generation.Proposition63.ActionBranches

/-!
# Distinguished odd-core generation: Proposition 6.3

Assume `L = ⟨z,t,[O₂′(D),t]⟩` is proper. Lemma 3.10 puts the distinguished
closure `M°` in `L`. Proper-subgroup ZD induction and the Borel quotient put
its nontrivial two-residual `Y` in `O₂′(D)`. Normality of `Y` excludes the
two-transitive branch. Theorem 2 and the local odd-core factorization then
make `z` normalize a Sylow subgroup times `Y` for each odd prime. These
Sylow subgroups generate the odd core, so `M°` lies in an odd group extended
by one involution, contradicting its elementary four.

The Section 3 interface and the explicitly displayed local factorization
are the permitted independent-development premises. The Corollary 6.4
assembly owner discharges them; this module does not assert that they follow
here from the minimal-counterexample hypotheses.

Source: GLS, Volume 4, Chapter 2, Proposition 6.3,
`refs/KGroup/GLS4/Chapter2.tex`, lines 990–1023.
The proof adapts `BenderSuzuki/SE/Theorem4Induction.lean` and
`BenderSuzuki/SE/Theorem4.lean`, using the distinguished closure throughout.
-/

noncomputable section
namespace BenderSuzuki.ZD
open Theory.GroupTheory PFAppendixIII PFchapter1section1
universe u
variable {G : Type u} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}

/-- The core contradiction of Proposition 6.3, with its local factorization
explicit. It applies to any distinguished involution outside `M`. -/
public theorem prop63_generation_of_local_factorization
    (h : MinimalCounterexample Z M) (r : SimpleReduction Z M)
    (hc : ActionCounting Z M) (hs : ActionSectionThree Z M)
    (d : ActionCounterexample Z M)
    {t : G} (htZ : t ∈ Z) (htM : t ∉ M)
    (hf : ∀ m ∈ M, ∃ o ∈ corollary64OddCore (residualPairStabilizer M t),
      ∃ c ∈ elementCentralizerIn M d.z, m = o * c) :
    residualGenerated M d.z t = ⊤ := by
  classical
  let L := residualGenerated M d.z t
  by_contra hLproper
  let D := residualPairStabilizer M t
  let Y := (prop63Residual Z M).map M.subtype
  let O : Subgroup D := twoPrimeCore D
  let OX : Subgroup G := O.map D.subtype
  have ht := h.disconnected.involutions t htZ
  have hYleOddL : Y ≤ (twoPrimeCore L).map L.subtype :=
    prop63_residual_le_oddCore h r hs d.hzZ d.hzM htZ htM hLproper
  have hYleD : Y ≤ D := hYleOddL.trans
    (prop63_oddCore_le_pairStabilizer h r hs d.hzZ d.hzM htZ htM)
  have hbetaNe : (QuotientGroup.mk t : G ⧸ M) ≠ QuotientGroup.mk 1 := by
    intro he
    apply htM
    simpa [ht.inv_eq_self] using QuotientGroup.eq.mp he
  have hnot2 : ¬ MulAction.IsMultiplyPretransitive G (G ⧸ M) 2 :=
    prop63_not_twoTransitive r.simple h.disconnected d ht hbetaNe hYleD
  have hOodd : Odd (Nat.card O) := Nat.coprime_two_left.mp pPrimeCore_coprime_card
  have hOXodd : Odd (Nat.card OX) := by
    rw [Subgroup.card_map_of_injective D.subtype_injective]
    exact hOodd
  have hYleOX : Y ≤ OX :=
    prop63_residual_le_pairOddCore_of_le_oddCore h r hs d.hzZ d.hzM htZ htM hYleOddL
  have hexists : ∀ q : (Nat.card O).primeFactors.attach,
      ∃ P₀ : Sylow q.1 O,
        d.z ∈ Subgroup.normalizer
          (((((P₀ : Subgroup O).map O.subtype).map D.subtype) ⊔ Y :
            Subgroup G) : Set G) := by
    intro q
    have hq : Nat.Prime q.1 := Nat.prime_of_mem_primeFactors q.1.2
    have hqdiv : (q.1 : ℕ) ∣ Nat.card O :=
      Nat.dvd_of_mem_primeFactors q.1.2
    have hqne : (q.1 : ℕ) ≠ 2 := by
      intro hqTwo
      rw [hqTwo] at hqdiv
      rcases hOodd with ⟨k, hk⟩
      omega
    have hqOdd : Odd (q.1 : ℕ) := hq.odd_of_ne_two hqne
    exact prop63_exists_sylow_normalized h.disconnected
      d.hzM d.hzZ ht htM hc.theorem_two hnot2 hf q.1 hq hqOdd
  choose P₀ hP₀norm using hexists
  let P : (Nat.card O).primeFactors.attach → Subgroup G :=
    fun q => (((P₀ q : Subgroup O).map O.subtype).map D.subtype)
  let S : Subgroup G := ⨆ q, P q ⊔ Y
  have hselected :
      (⨆ q, ((P₀ q : Sylow q.1 O) : Subgroup O)) = ⊤ :=
    iSup_selected_sylow_eq_top P₀
  have htopMapO : (⊤ : Subgroup O).map O.subtype = O := by
    simpa [MonoidHom.range_eq_map] using
      (Subgroup.range_subtype (H := O))
  have hPiSup : (⨆ q, P q) = OX := by
    calc
      (⨆ q, P q) =
          ((⨆ q, ((P₀ q : Sylow q.1 O) : Subgroup O)).map
            O.subtype).map D.subtype := by
              simp only [P, Subgroup.map_iSup]
      _ = ((⊤ : Subgroup O).map O.subtype).map D.subtype := by
        rw [hselected]
      _ = O.map D.subtype := by rw [htopMapO]
      _ = OX := rfl
  have hSeq : S = OX := by
    apply le_antisymm
    · refine iSup_le ?_
      intro q
      exact sup_le
        ((le_iSup (fun r => P r) q).trans_eq hPiSup) hYleOX
    · rw [← hPiSup]
      refine iSup_mono ?_
      intro q
      exact le_sup_left
  have hzNormS : d.z ∈ Subgroup.normalizer (S : Set G) := by
    have hconj : S.conjBy d.z = S := by
      dsimp only [S]
      rw [Subgroup.conjBy, Subgroup.map_iSup]
      apply iSup_congr
      intro q
      simpa only [Subgroup.conjBy] using
        section11_conjBy_eq_of_mem_normalizer (hP₀norm q)
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      have hxconj : d.z * x * d.z⁻¹ ∈ S.conjBy d.z := by
        rw [Subgroup.conjBy, Subgroup.mem_map]
        exact ⟨x, hx, by simp⟩
      simpa [hconj] using hxconj
    · intro hx
      have h_inv : S.conjBy d.z⁻¹ = S := by
        simpa [hconj] using (Subgroup.conjBy_inv S d.z)
      have hxpre : x ∈ S.conjBy d.z⁻¹ := by
        rw [Subgroup.conjBy, Subgroup.mem_map]
        refine ⟨d.z * x * d.z⁻¹, hx, ?_⟩
        simp [mul_assoc]
      simpa [h_inv] using hxpre
  have hzNormOX : d.z ∈ Subgroup.normalizer (OX : Set G) := by
    rw [← hSeq]
    exact hzNormS
  let H : Subgroup G := OX ⊔ Subgroup.zpowers d.z
  have hcoreH : Subgroup.closure (Z ∩ (M : Set G)) ≤ H := by
    apply (Subgroup.closure_le _).mpr
    intro y hy
    obtain ⟨a, ha, hay⟩ := prop63_oddCore_conjugator h.disconnected
      d.hzZ d.hzM hy.1 hy.2 D hf
    have he : y = a * d.z * a⁻¹ := by
      rw [← hay]
      simp only [rightConjugateElem]
      group
    rw [he]
    exact H.mul_mem
      (H.mul_mem (Subgroup.mem_sup_left ha)
        (Subgroup.mem_sup_right (Subgroup.mem_zpowers d.z)))
      (H.inv_mem (Subgroup.mem_sup_left ha))
  have hrankH : TwoRankAtLeastTwo H :=
    (distinguishedClosure_twoRank h r).map_of_injective
      (Subgroup.inclusion hcoreH) (Subgroup.inclusion_injective hcoreH)
  exact (not_twoRankAtLeastTwo_sup_odd_involution
    OX hOXodd d.hz hzNormOX) hrankH

/-- Proposition 6.3 under the permitted Section 3 and local factorization
premises. The commutator uses `O₂′(D)` even when `D` has even order. -/
public theorem action_residualGenerated_eq_top_of_local_factorization
    (h : MinimalCounterexample Z M) (r : SimpleReduction Z M)
    (hc : ActionCounting Z M) (d : ActionMaximalCounterexample Z M)
    (hs : ActionSectionThree Z M)
    (hf : ∀ gamma : G ⧸ M, gamma ≠ QuotientGroup.mk 1 →
      ∀ m ∈ M, ∃ o ∈ corollary64OddCore (theorem4bSection7D M gamma),
        ∃ c ∈ elementCentralizerIn M d.data.z, m = o * c)
    (beta : G ⧸ M) (_hbeta : beta ∈ d.data.toTheorem4bSixA.kFixedPoints)
    (hne : beta ≠ QuotientGroup.mk 1)
    (t : G) (htZ : t ∈ Z) (htBase : t • (QuotientGroup.mk 1 : G ⧸ M) = beta) :
    residualGenerated M d.data.z t = ⊤ := by
  have ht := h.disconnected.involutions t htZ
  have htM : t ∉ M := by
    intro htM
    apply hne
    rw [← htBase]
    exact MulAction.mem_stabilizer_iff.mp ((baseCoset_stabilizer M).symm ▸ htM)
  have hDeq : theorem4bSection7D M beta = residualPairStabilizer M t := by
    have hstab : MulAction.stabilizer G beta = rightConjugate M t := by
      rw [← htBase]
      simpa [MulAction.Quotient.smul_mk, smul_eq_mul, ht.inv_eq_self] using
        conjugateCoset_stabilizer M t
    exact congrArg (M ⊓ ·) hstab
  apply prop63_generation_of_local_factorization h r hc hs d.data htZ htM
  simpa only [hDeq] using hf beta hne

end BenderSuzuki.ZD
