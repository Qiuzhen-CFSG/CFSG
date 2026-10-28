module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicRemaining.Covers
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicRemaining.Rudvalis.Coverage
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.EvenRankTwo.Reduction
public import Theory.SpecificGroups.Rudvalis.Model.Basic
public import Theory.SpecificGroups.Rudvalis.Model.SylowOvergroups.Definitions
public import Theory.SpecificGroups.Rudvalis.Model.SylowOvergroups.Cardinality

/-!
# The Rudvalis Sylow-pair exclusion

A permuting pair RS from `PairInput` has order divisible by nine and has
only the prime divisors two and three. The checked element ab of order 13
in the fixed degree-4060 carrier makes RS proper, without using the order
or simplicity certification of the whole model. A maximal overgroup M of
RS has odd index because it contains the genuine Sylow two-subgroup S.

The exhaustive coverage theorem identifies M with one of the two concrete
ATLAS subgroups. Their certified orders, 344064 and 245760, are not divisible
by nine, a contradiction. The final exclusion discharges all three premises
of the retained conditional reduction. It uses only `PairInput` on the fixed
carrier; the central-cover reduction remains with the sporadic sieve owner.

Source: Aschbacher–Smith, proof of Proposition 1.3.4, printed p.511
(PDF p.528 of `refs/quasithin.pdf`), citing Aschbacher's 1986 Sylow-overgroup
analysis. The concrete subgroup programs are sourced in
`Theory.SpecificGroups.Rudvalis.Model.SylowOvergroups.Definitions`.
-/

public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicRemaining

variable {S : Sylow 2 Rudvalis.Model} {R : Subgroup Rudvalis.Model}

/-- The known element of order 13 excludes RS = Ru using only the pair
product formula, not the full Rudvalis order or a solvability theorem. -/
theorem rudvalis_pair_product_ne_top (h : PairInput S R) :
    R ⊔ (S : Subgroup Rudvalis.Model) ≠ ⊤ := by
  intro he
  have hd : 13 ∣ Nat.card (R ⊔ (S : Subgroup Rudvalis.Model) : Subgroup Rudvalis.Model) := by
    rw [he, card_top, ← Rudvalis.orderOf_ab]
    exact _root_.orderOf_dvd_natCard _
  have hp := EvenRankTwo.product_prime_divisors h (by norm_num : Nat.Prime 13) hd
  norm_num at hp

/-- Any hypothetical pair forces an odd-index maximal subgroup whose order
is divisible by nine. This existential consequence is unconditional. -/
theorem rudvalis_pair_maximal_overgroup (h : PairInput S R) :
    ∃ M : Subgroup Rudvalis.Model, IsCoatom M ∧ ¬ 2 ∣ M.index ∧
      R ≤ M ∧ (S : Subgroup Rudvalis.Model) ≤ M ∧ 9 ∣ Nat.card M := by
  obtain ⟨M, hM, hle⟩ :=
    (eq_top_or_exists_le_coatom (R ⊔ (S : Subgroup Rudvalis.Model))).resolve_left
      (rudvalis_pair_product_ne_top h)
  have hSM : (S : Subgroup Rudvalis.Model) ≤ M := le_sup_right.trans hle
  have hRM : R ≤ M := le_sup_left.trans hle
  have hodd : ¬ 2 ∣ M.index := fun hd =>
    S.not_dvd_index (hd.trans (index_dvd_of_le hSM))
  have hR : 9 ∣ Nat.card R := by
    rcases h.oddComplement with ⟨_, hc⟩ | ⟨_, hc, _⟩ <;> rw [hc] <;> norm_num
  exact ⟨M, hM, hodd, hRM, hSM, hR.trans (card_dvd_of_le hRM)⟩

/-- The exact numerical consequence of the exhaustive Sylow-overgroup
calculation that suffices for this source branch. It remains a premise. -/
theorem rudvalis_no_pair_of_maximal_bound
    (hmax : ∀ M : Subgroup Rudvalis.Model,
      IsCoatom M → ¬ 2 ∣ M.index → ¬ 9 ∣ Nat.card M)
    (h : PairInput S R) : False := by
  obtain ⟨M, hM, hodd, _, _, hnine⟩ := rudvalis_pair_maximal_overgroup h
  exact hmax M hM hodd hnine

/-- Exhaustive coverage and the two local cardinality bounds are independent
inputs. Merely exhibiting the two subgroups does not discharge coverage. -/
theorem rudvalis_no_pair_of_cover
    (hcover : Rudvalis.SylowOvergroups.OddIndexMaximalCover)
    (h4 : ¬ 9 ∣ Nat.card Rudvalis.SylowOvergroups.max4)
    (h6 : ¬ 9 ∣ Nat.card Rudvalis.SylowOvergroups.max6)
    (h : PairInput S R) : False := by
  apply rudvalis_no_pair_of_maximal_bound ?_ h
  intro M hM hodd hnine
  rcases hcover M hM hodd with he | he
  · obtain ⟨e⟩ := he
    exact h4 (Nat.card_congr e.toEquiv ▸ hnine)
  · obtain ⟨e⟩ := he
    exact h6 (Nat.card_congr e.toEquiv ▸ hnine)

/-- The Rudvalis branch of the source sieve: no genuine input pair exists
on the fixed degree-4060 model. Coverage and both local order bounds are proved. -/
theorem rudvalis_no_pair (h : PairInput S R) : False :=
  rudvalis_no_pair_of_cover (rudvalis_oddIndexMaximalCover h)
    Rudvalis.SylowOvergroups.not_nine_dvd_max4_card
    Rudvalis.SylowOvergroups.not_nine_dvd_max6_card h

/-- The local action exclusion required by the invariant-three sieve. -/
theorem rudvalis_pairReducible (h : PairInput S R) :
    PairReducible (S : Subgroup Rudvalis.Model) R :=
  (rudvalis_no_pair h).elim

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicRemaining
