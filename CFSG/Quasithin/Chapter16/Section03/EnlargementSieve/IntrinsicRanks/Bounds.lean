module

public import CFSG.Quasithin.Chapter16.Section03.EnlargementSieve.Rank
public import Theory.GroupTheory.PrimeRankInvolutionLift

/-!
# Consequences of the enlargement rank inequality

A doubled intrinsic rank contradicts the outside case when the automorphism
rank is no larger than the factor rank. In the exceptional cases, an
automorphism rank at most three excludes rank six and forces a rank-five
enlargement to contain t. A center of order two is then exactly ⟨t⟩.

These deductions isolate the numerical steps of Aschbacher–Smith, 16.3.9,
combined manuscript of 1 March 2004, printed pp.1180–1181. Their intrinsic
numerical premises must be supplied by the model calculations; this module
does not assert that those calculations or the case sieve are complete.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter16.EnlargementSieve.IntrinsicRanks
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {z t : G} {L : Subgroup G}

/-- The same upper bound holds for K before adjoining t. -/
theorem rank_le_aut (h : TerminalCounterexample T z L t)
    (hs : NonterminalCentralizerShape T z L t) :
    primeRank 2 (enlargement t L) ≤ primeRank 2 (MulAut L) + 2 := by
  exact (primeRank_le_of_injective 2 (inclusion (le_sup_left :
    enlargement t L ≤ enlargement t L ⊔ zpowers t))
      (inclusion_injective _)).trans (enlargement_rank_le h hs)

/-- The outside case is incompatible with doubled factor rank at least four. -/
theorem not_outside_of_doubled_rank (h : TerminalCounterexample T z L t)
    (hs : NonterminalCentralizerShape T z L t) {m : ℕ} (hm : 2 ≤ m)
    (hK : 2 * m ≤ primeRank 2 (enlargement t L))
    (hAut : primeRank 2 (MulAut L) ≤ m) : t ∈ enlargement t L := by
  by_contra ht
  have hr := enlargement_rank_succ_le_aut h hs ht
  omega

/-- A centerless model with doubled rank is excluded. -/
theorem exclude_centerless_doubled_rank (h : TerminalCounterexample T z L t)
    (hs : NonterminalCentralizerShape T z L t) {m : ℕ} (hm : 2 ≤ m)
    (hK : 2 * m ≤ primeRank 2 (enlargement t L))
    (hAut : primeRank 2 (MulAut L) ≤ m)
    (hZ : center (enlargement t L) = ⊥) : False :=
  center_ne_bot h (not_outside_of_doubled_rank h hs hm hK hAut) hZ

/-- Involutory lifts through an elementary center give the extra rank beyond
K/Z(K), whether t lies inside or outside K. This is the permitted-cover
comparison used for PSL₃(4); the actual cover must supply the lifting theorem. -/
theorem quotient_rank_succ_le (h : TerminalCounterexample T z L t)
    [IsElementaryAbelian 2 (center (enlargement t L))]
    (hlift : ∀ x : enlargement t L ⧸ center (enlargement t L), x ^ 2 = 1 →
      ∃ y : enlargement t L, QuotientGroup.mk' (center (enlargement t L)) y = x ∧ y ^ 2 = 1) :
    primeRank 2 (enlargement t L ⧸ center (enlargement t L)) + 1 ≤
      primeRank 2 (enlargement t L ⊔ zpowers t : Subgroup G) := by
  obtain ⟨n, hn⟩ := (IsElementaryAbelian.isPGroup 2 (center (enlargement t L))).exists_card_eq
  have he := two_rank_eq_quotient_add_of_central_involution_lifts
    (center (enlargement t L)) le_rfl hn hlift
  by_cases ht : t ∈ enlargement t L
  · have hnpos : 0 < n := by
      by_contra hc
      have hn0 : n = 0 := by omega
      have hc : Nat.card (center (enlargement t L)) = 1 := by simpa [hn0] using hn
      exact center_ne_bot h ht ((center (enlargement t L)).card_eq_one.mp hc)
    have hi := primeRank_le_of_injective 2 (inclusion (le_sup_left :
      enlargement t L ≤ enlargement t L ⊔ zpowers t)) (inclusion_injective _)
    omega
  · have hi := enlargement_rank_succ_le h ht
    omega

/-- The doubled-quotient contradiction also covers nonsimple PSL₃(4), once
its genuine involution-lifting input is supplied. -/
theorem exclude_lifted_doubled_rank (h : TerminalCounterexample T z L t)
    (hs : NonterminalCentralizerShape T z L t)
    [IsElementaryAbelian 2 (center (enlargement t L))]
    (hlift : ∀ x : enlargement t L ⧸ center (enlargement t L), x ^ 2 = 1 →
      ∃ y : enlargement t L, QuotientGroup.mk' (center (enlargement t L)) y = x ∧ y ^ 2 = 1)
    {m : ℕ} (hm : 2 ≤ m)
    (hK : 2 * m ≤ primeRank 2 (enlargement t L ⧸ center (enlargement t L)))
    (hAut : primeRank 2 (MulAut L) ≤ m) : False := by
  have hlower := quotient_rank_succ_le h hlift
  have hupper := enlargement_rank_le h hs
  omega

/-- The inequality (!!) excludes rank six; its automorphism premise is a
two-rank bound, not the printed three-rank assertion. -/
theorem exclude_rank_six (h : TerminalCounterexample T z L t)
    (hs : NonterminalCentralizerShape T z L t)
    (hK : 6 ≤ primeRank 2 (enlargement t L))
    (hAut : primeRank 2 (MulAut L) ≤ 3) : False := by
  have hr := rank_le_aut h hs
  omega

/-- The rank-five double-cover case forces the contrary involution into K. -/
theorem mem_of_rank_five (h : TerminalCounterexample T z L t)
    (hs : NonterminalCentralizerShape T z L t)
    (hK : 5 ≤ primeRank 2 (enlargement t L))
    (hAut : primeRank 2 (MulAut L) ≤ 3) : t ∈ enlargement t L := by
  by_contra ht
  have hr := enlargement_rank_succ_le_aut h hs ht
  omega

/-- In the rank-five double-cover branch the actual ambient image of Z(K)
is ⟨t⟩. This identifies the element to which the short-root lift squares. -/
theorem center_image_of_rank_five (h : TerminalCounterexample T z L t)
    (hs : NonterminalCentralizerShape T z L t)
    (hK : 5 ≤ primeRank 2 (enlargement t L))
    (hAut : primeRank 2 (MulAut L) ≤ 3)
    (hZ : Nat.card (center (enlargement t L)) = 2) :
    (center (enlargement t L)).map (enlargement t L).subtype = zpowers t := by
  have ht := mem_of_rank_five h hs hK hAut
  have hle : zpowers t ≤ (center (enlargement t L)).map (enlargement t L).subtype :=
    zpowers_le.mpr ⟨⟨t, ht⟩, involution_mem_center h ht, rfl⟩
  symm
  apply eq_of_le_of_card_ge hle
  rw [card_map_of_injective Subtype.val_injective, Nat.card_zpowers, h.involution, hZ]

end CFSG.Quasithin.Chapter16.EnlargementSieve.IntrinsicRanks
