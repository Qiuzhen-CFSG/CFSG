module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Action.Exclusion.MaximalNormalizer.Basic
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Action.Exclusion.ThetaChain.Gamma.NormalizingSwap
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Action.Counting.SectionThree

/-!
# Maximal admissible subgroups and invariant Sylow enlargement

Section 3 extends W to a z-invariant Sylow subgroup P of the triple
stabilizer. Distinguished Lemma 7.3 gives its normalizing swap, so P is
admissible. Proposition 7.9 excludes P from being Sylow in D. The p-group
normalizer condition and finite maximization then force the selected
normalizer to have a Sylow subgroup strictly larger than P₁. Section 3
chooses that Sylow subgroup invariant under the same distinguished swap.

Source: GLS, Volume 4, Chapter 2, second-stage setup after Proposition 7.9,
preceding Lemma 7.10. The cardinal argument adapts `SE.Section7Final`;
all local Sylow extensions here use the distinguished Section 3 theorem.
-/

noncomputable section
namespace BenderSuzuki.ZD
open Theory.GroupTheory PFAppendixIII PFchapter1section1

variable {G : Type*} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}

/-- Lemma 7.3 supplies an initial admissible member with Q = P₁. -/
public theorem action_initial_admissibleQ
    (h : MinimalCounterexample Z M) (r : SimpleReduction Z M)
    (hc : ActionCounting Z M) (d : ActionMaximalCounterexample Z M)
    {beta : G ⧸ M} (hb : beta ∈ d.data.toTheorem4bSixA.kFixedPoints)
    (hne : beta ≠ QuotientGroup.mk 1) :
    ∃ a : ActionAdmissibleQ d.data beta, a.Q = a.P₁ := by
  let h3 := actionSectionThree_of_minimalCounterexample h r
  let E := theorem4bSection7E M d.data.z beta
  have hzMove : d.data.z • beta ≠ beta :=
    fun he => hne (action_fixedPoint_eq_base h.disconnected d.data.hzZ d.data.hzM he)
  obtain ⟨P, hPsyl, hWP, hzP, _⟩ := h3.swapping_sylow
    d.data.z d.data.hzZ beta hzMove d.data.p d.data.hp d.data.hpOdd E d.data.W
    (le_inf (inf_le_left.trans inf_le_right) inf_le_right)
    (theorem4b_mem_normalizer_tripleStabilizer d.data.hz d.data.hzM)
    d.data.hWp (d.data.le_triple_stabilizer hb) d.data.hzNorm
  obtain ⟨t, htZ, htP, htBase⟩ := actionGamma_normalizing_swap h r hc h3 d hb hne hPsyl hzP
  have hPp : IsPGroup d.data.p P := by
    obtain ⟨S, rfl⟩ := hPsyl
    exact S.isPGroup'.map _
  have hPE : P ≤ E := by
    obtain ⟨S, rfl⟩ := hPsyl
    exact Subgroup.map_subtype_le _
  have hPne : P ≠ ⊥ := fun he => d.data.hWne (bot_unique (he ▸ hWP))
  exact ⟨{
    Q := P, hQp := hPp, hQne := hPne, hQE := hPE, hzNormQ := hzP,
    t := t, htZ := htZ, htBase := htBase, htNormQ := htP,
    P₁ := P, hP₁sylow := hPsyl, hP₁NormQ := Subgroup.le_normalizer,
    htNormP₁ := htP }, rfl⟩

/-- The maximal choice and the strict invariant Sylow enlargement required
immediately before Lemma 7.10, with relative normalizers throughout. -/
public theorem action_maximal_admissibleQ_sylow
    (h : MinimalCounterexample Z M) (r : SimpleReduction Z M)
    (hc : ActionCounting Z M) (d : ActionMaximalCounterexample Z M)
    (h64 : ActionCorollary64 d.data)
    (h72 : Theorem4bProposition72 d.data.toTheorem4bSixA)
    {beta : G ⧸ M} (hb : beta ∈ d.data.toTheorem4bSixA.kFixedPoints)
    (hne : beta ≠ QuotientGroup.mk 1) :
    ∃ a : ActionAdmissibleQ d.data beta,
      (∀ b : ActionAdmissibleQ d.data beta,
        (Nat.card (actionNormalizerInD M beta b.Q)).factorization d.data.p ≤
          (Nat.card (actionNormalizerInD M beta a.Q)).factorization d.data.p) ∧
      ∃ R : Subgroup G,
        theorem4bIsSylowSubgroupOf d.data.p R (actionNormalizerInD M beta a.Q) ∧
        a.P₁ ≤ R ∧ a.t ∈ Subgroup.normalizer (R : Set G) ∧
        Nat.card a.P₁ < Nat.card R := by
  let : Fact d.data.p.Prime := ⟨d.data.hp⟩
  let h3 := actionSectionThree_of_minimalCounterexample h r
  obtain ⟨a₀, hinit⟩ := action_initial_admissibleQ h r hc d hb hne
  obtain ⟨a, hmax⟩ := action_exists_maximal_admissibleQ d.data beta ⟨a₀⟩
  have hP₀not : ¬ theorem4bIsSylowSubgroupOf d.data.p a₀.Q
      (theorem4bSection7D M beta) := fun hs =>
    action_no_invariant_sylow_of_firstStage h.disconnected hc d h64 h72 hb hne
      ⟨a₀.Q, hs, a₀.hzNormQ⟩
  have hgrowth := action_factorization_lt_normalizer_of_not_sylow d.data.hp
    a₀.hQp (a₀.hQE.trans inf_le_left) hP₀not
  have hcards : Nat.card a.P₁ = Nat.card a₀.Q := by
    rw [hinit]
    obtain ⟨S, hS⟩ := a.hP₁sylow
    obtain ⟨T, hT⟩ := a₀.hP₁sylow
    rw [hS, hT, Subgroup.card_map_of_injective (Subgroup.subtype_injective _),
      Subgroup.card_map_of_injective (Subgroup.subtype_injective _),
      S.card_eq_multiplicity, T.card_eq_multiplicity]
  have hfac : (Nat.card a.P₁).factorization d.data.p <
      (Nat.card (actionNormalizerInD M beta a.Q)).factorization d.data.p := by
    rw [hcards]
    exact hgrowth.trans_le (hmax a₀)
  let NDQ := actionNormalizerInD M beta a.Q
  have hP₁p : IsPGroup d.data.p a.P₁ := by
    obtain ⟨S, hS⟩ := a.hP₁sylow
    rw [hS]
    exact S.isPGroup'.map _
  have hP₁E : a.P₁ ≤ theorem4bSection7E M d.data.z beta := by
    obtain ⟨S, hS⟩ := a.hP₁sylow
    rw [hS]
    exact Subgroup.map_subtype_le _
  have htNormD : a.t ∈ Subgroup.normalizer (theorem4bSection7D M beta : Set G) := by
    have hn := theorem4b_mem_normalizer_tripleStabilizer
      (M := (⊤ : Subgroup G)) (z := a.t)
      (beta := (QuotientGroup.mk 1 : G ⧸ M))
      (h.disconnected.involutions a.t a.htZ) (Subgroup.mem_top _)
    simpa [theorem4bSection7D, baseCoset_stabilizer, a.htBase] using hn
  have htNormNDQ : a.t ∈ Subgroup.normalizer (NDQ : Set G) :=
    Subgroup.inf_normalizer_le_normalizer_inf
      ⟨htNormD, Subgroup.le_normalizer a.htNormQ⟩
  have htMove : a.t • (QuotientGroup.mk 1 : G ⧸ M) ≠ QuotientGroup.mk 1 := by
    rw [a.htBase]
    exact hne
  obtain ⟨R, hRsyl, hP₁R, htR, _⟩ := h3.swapping_sylow a.t a.htZ
    (QuotientGroup.mk 1 : G ⧸ M) htMove d.data.p d.data.hp d.data.hpOdd NDQ a.P₁
    (by
      rw [baseCoset_stabilizer, a.htBase]
      exact le_inf (inf_le_left.trans inf_le_left) (inf_le_left.trans inf_le_right))
    htNormNDQ hP₁p (le_inf (hP₁E.trans inf_le_left) a.hP₁NormQ) a.htNormP₁
  have hRcard : Nat.card R = d.data.p ^ (Nat.card NDQ).factorization d.data.p := by
    obtain ⟨S, hS⟩ := hRsyl
    rw [hS, Subgroup.card_map_of_injective NDQ.subtype_injective]
    exact S.card_eq_multiplicity
  refine ⟨a, hmax, R, hRsyl, hP₁R, htR, ?_⟩
  rw [hRcard, section8_card_eq_prime_pow_factorization_of_isPGroup hP₁p]
  exact Nat.pow_lt_pow_right d.data.hp.one_lt hfac

end BenderSuzuki.ZD
