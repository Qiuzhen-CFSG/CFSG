module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Action.Exclusion.Interfaces
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Action.Exclusion.Generation.ZJ
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Action.Exclusion.Generation.CorePlacement
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Action.Exclusion.Generation.Proposition63
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Action.Counting.Contracts
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Action.Counting.SectionThree

/-!
# Distinguished Proposition 6.3 and Corollary 6.4

This module assembles the complete Corollary 6.4 conclusion, including both
non-normalization assertions for every eligible `p`-subgroup of each actual
two-point stabilizer. The ZJ calculation is carried out in the odd subgroup
`O_{2'}(D)R`, and the generation commutator is `[O_{2'}(D),t]`.

Section 3 supplies the local odd-core factorization and places the
commutator-saturated witness `W` in `O_{2'}(D)`. The factorization discharges
the remaining premise of Proposition 6.3, whose proof uses the distinguished
closure and its two-residual. The final theorem then discharges every premise
of the preserved conditional Corollary 6.4 assembly.

Source: GLS, Volume 4, Chapter 2, Proposition 6.3 and Corollary 6.4,
`refs/KGroup/GLS4/Chapter2.tex`, lines 990–1035.
-/

noncomputable section
namespace BenderSuzuki.ZD
open Theory.GroupTheory PFAppendixIII PFchapter1section1
universe u
variable {G : Type u} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}

/-- Source Proposition 6.3 with the Section 3 and local factorization premises
discharged. The generated subgroup uses `[O_{2'}(D),t]`. -/
public theorem action_residualGenerated_eq_top_of_minimalCounterexample
    (h : MinimalCounterexample Z M) (r : SimpleReduction Z M)
    (hc : ActionCounting Z M) (d : ActionMaximalCounterexample Z M)
    (beta : G ⧸ M) (hbeta : beta ∈ d.data.toTheorem4bSixA.kFixedPoints)
    (hne : beta ≠ QuotientGroup.mk 1)
    (t : G) (htZ : t ∈ Z) (htBase : t • (QuotientGroup.mk 1 : G ⧸ M) = beta) :
    residualGenerated M d.data.z t = ⊤ := by
  have hs := actionSectionThree_of_minimalCounterexample h r
  apply action_residualGenerated_eq_top_of_local_factorization h r hc d hs
    (fun gamma hgamma m hm =>
      action_oddCore_factorization h.disconnected hs d.data.hzZ d.data.hzM hgamma hm)
    beta hbeta hne t htZ htBase

/-- Conditional assembly of all three clauses of Corollary 6.4. The two
remaining source inputs are odd-core generation and placement of `W` in
the odd core of each eligible two-point stabilizer. -/
public theorem actionCorollary64_of_generation
    (h : IsProductDisconnected Z M) (r : SimpleReduction Z M)
    (hs : ActionSectionThree Z M) (d : ActionCounterexample Z M)
    (hgeneration : ∀ beta : G ⧸ M,
      beta ∈ d.toTheorem4bSixA.kFixedPoints → beta ≠ QuotientGroup.mk 1 →
      ∀ t ∈ Z, t • (QuotientGroup.mk 1 : G ⧸ M) = beta →
        residualGenerated M d.z t = ⊤)
    (hWcore : ∀ beta : G ⧸ M,
      beta ∈ d.toTheorem4bSixA.kFixedPoints → beta ≠ QuotientGroup.mk 1 →
      d.W ≤ corollary64OddCore (theorem4bSection7D M beta)) :
    ActionCorollary64 d := by
  intro beta hbeta hne hzNorm
  let : Fact d.p.Prime := ⟨d.hp⟩
  obtain ⟨t, htZ, htBase⟩ := hs.swap (QuotientGroup.mk 1) beta hne.symm
  have ht := h.involutions t htZ
  have hDeq : theorem4bSection7D M beta = residualPairStabilizer M t := by
    have hstab : MulAction.stabilizer G beta = rightConjugate M t := by
      rw [← htBase]
      simpa [MulAction.Quotient.smul_mk, smul_eq_mul, ht.inv_eq_self] using
        conjugateCoset_stabilizer M t
    exact congrArg (M ⊓ ·) hstab
  have hgen := hgeneration beta hbeta hne t htZ htBase
  have htheta : corollary64Theta d.p (theorem4bSection7D M beta) = ⊥ := by
    rw [hDeq] at hzNorm ⊢
    exact action_theta_eq_bot_of_generation h r ht hgen hzNorm
  refine ⟨htheta, ?_⟩
  intro R hRp hRD hcontains
  have hcomm : ⁅residualPairStabilizer M t, Subgroup.zpowers t⁆ ≤
      corollary64OddCore (residualPairStabilizer M t) := by
    apply hs.swapping_core t htZ (QuotientGroup.mk 1)
      (by simpa only [htBase] using hne) (residualPairStabilizer M t)
    · rw [baseCoset_stabilizer, htBase, ← hDeq]
      exact le_rfl
    · exact inf_rightConjugate_mem_normalizer_of_isInvolution M ht
  have hpW : d.p ∣ Nat.card d.W := by
    rcases d.hWp.card_eq_or_dvd with hone | hdiv
    · exact False.elim (d.hWne (Subgroup.card_eq_one.mp hone))
    · exact hdiv
  have hpCore : d.p ∣ Nat.card (twoPrimeCore (residualPairStabilizer M t)) := by
    have hh := hpW.trans (Subgroup.card_dvd_of_le (hWcore beta hbeta hne))
    rw [hDeq, corollary64OddCore,
      Subgroup.card_map_of_injective (residualPairStabilizer M t).subtype_injective] at hh
    exact hh
  rw [hDeq] at htheta hRD hcontains
  exact action_corollary64_not_normalizes_of_generation h r ht d.hpOdd
    hgen htheta hcomm hpCore hRp hRD hcontains

/-- Source Corollary 6.4 for the distinguished maximal counterexample, retaining
theta triviality and both non-normalization clauses for every eligible coset
and every `p`-subgroup containing an embedded Sylow subgroup of the odd core.
The two-point stabilizer is not assumed to have odd order. -/
public theorem actionCorollary64_of_minimalCounterexample
    (h : MinimalCounterexample Z M) (r : SimpleReduction Z M)
    (hc : ActionCounting Z M) (d : ActionMaximalCounterexample Z M) :
    ActionCorollary64 d.data := by
  have hs := actionSectionThree_of_minimalCounterexample h r
  apply actionCorollary64_of_generation h.disconnected r hs d.data
    (action_residualGenerated_eq_top_of_minimalCounterexample h r hc d)
  intro beta hbeta hne
  exact actionCounterexample_le_oddCore h.disconnected hs d.data hbeta hne

end BenderSuzuki.ZD
