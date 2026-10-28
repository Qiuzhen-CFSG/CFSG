module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Action.Exclusion.Interfaces

/-!
# First-stage assembly of the distinguished Section 7 argument

The theta-chain comparisons force equality of the three theta subgroups.
Conjugation by `z` preserves the third, so Corollary 6.4 kills the first.
Lemma 6.2 then makes the inverted-cardinality bound strict, and (6B) gives
double transitivity. The second stage must still construct the final maximal-normalizer configuration.

These are conditional assembly lemmas. The generation/Corollary 6.4 proof,
the theta-chain construction, and the final maximal-normalizer construction
must still be supplied from the genuine minimal-counterexample hypotheses.
In particular this module does not yet assert `actionMaximalCounterexample_false`.

Source: GLS, Volume 4, Chapter 2, Propositions 7.2, 7.8--7.9 and the final
paragraph of the proof of Proposition 7.1.
-/

noncomputable section

namespace BenderSuzuki.ZD

open Theory.GroupTheory PFAppendixIII PFchapter1section1

universe u

variable {G : Type u} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}

/-- Equality of the theta chain and Corollary 6.4 give Proposition 7.2. -/
public theorem action_proposition72_of_theta_chain
    (d : ActionCounterexample Z M) (h64 : ActionCorollary64 d)
    (hchain : ActionThetaChain d) : Theorem4bProposition72 d.toTheorem4bSixA := by
  obtain ⟨beta, hb, hne, hFE, hED, hcard⟩ := hchain
  obtain ⟨hDE, hEF⟩ := theorem4b_section7_chain_eq hFE hED hcard
  have hzNorm : d.z ∈ Subgroup.normalizer
      (corollary64Theta d.p (theorem4bSection7D M beta) : Set G) := by
    rw [hDE.trans hEF]
    exact theorem4b_mem_normalizer_section7ThetaF d.hz d.p beta
  exact ⟨beta, hb, hne, (h64 beta hb hne hzNorm).1⟩

/-- Proposition 7.9 with distinguished involutions and same-parameter
maximality. A Sylow subgroup of `D` contains a Sylow subgroup of its odd
core even when `D` has even order. -/
public theorem ActionMaximalCounterexample.invertedCard_lt_primeShare
    (d : ActionMaximalCounterexample Z M)
    (h : IsProductDisconnected Z M) (hc : ActionCounting Z M)
    (h64 : ActionCorollary64 d.data)
    (h72 : Theorem4bProposition72 d.data.toTheorem4bSixA) :
    theorem4bInvertedCard d.data.z d.data.W <
      theorem4bPrimeShare M d.data.z d.data.p := by
  apply lt_of_le_of_ne (hc.bound d.data)
  intro heq
  obtain ⟨beta, hb, hne, htheta⟩ := h72
  obtain ⟨R, hRsyl, hzR⟩ := (d.invariant_sylow_iff h hc hb hne).mpr heq
  have hzTheta : d.data.z ∈ Subgroup.normalizer
      (corollary64Theta d.data.p (theorem4bSection7D M beta) : Set G) := by
    rw [htheta, Subgroup.normalizer_eq_top]
    exact Subgroup.mem_top _
  have hcontains := action_sylow_contains_oddCore d.data.hp hRsyl
  obtain ⟨S, hS⟩ := hRsyl
  have hRp : IsPGroup d.data.p R := by
    rw [hS]
    exact S.isPGroup'.map _
  have hRD : R ≤ theorem4bSection7D M beta := by
    rw [hS]
    exact Subgroup.map_subtype_le _
  exact ((h64 beta hb hne hzTheta).2 R hRp hRD hcontains).2 hzR

/-- The equality in (6B) rules out failure of double transitivity once
Proposition 7.2 and Corollary 6.4 have been proved. -/
public theorem ActionMaximalCounterexample.two_transitive_of_proposition72
    (d : ActionMaximalCounterexample Z M)
    (h : IsProductDisconnected Z M) (hc : ActionCounting Z M)
    (h64 : ActionCorollary64 d.data)
    (h72 : Theorem4bProposition72 d.data.toTheorem4bSixA) :
    MulAction.IsMultiplyPretransitive G (G ⧸ M) 2 := by
  by_contra hnot
  have hlt := d.invertedCard_lt_primeShare h hc h64 h72
  have heq := d.card_eq_primeShare hc hnot
  omega

end BenderSuzuki.ZD
