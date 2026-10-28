module

public import CFSG.Quasithin.Chapter16.Section03.EnlargementSieve.Contracts
public import CFSG.Quasithin.Chapter16.Section03.EnlargementSieve.Geometry
public import CFSG.Quasithin.Chapter16.Section03.EnlargementSieve.Rank
public import CFSG.Quasithin.Chapter16.Section03.EnlargementSieve.IntrinsicRanks.Bounds
public import Theory.SpecificGroups.PSL2.RootTwoRank
public import Theory.SpecificGroups.PSL2.OuterSolvable.Models

/-!
# The rank-one field pair

The smaller endpoint at field order two is solvable, so cannot be the
central quotient of the quasisimple component. For the remaining parameters
the upper root subgroup in the larger PSL₂(2²ⁿ) supplies rank at least 2n.
The smaller-model rank and automorphism bound are the explicit numerical
inputs owned by the swapped-factor calculation. No rank bound for the
larger model is assumed.

Source: Aschbacher–Smith 16.1.7(3a) and 16.3.9, pp.1172 and 1180.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter16.EnlargementSieve.IntrinsicRanks.LiePairs

/-- The genuine PSL₂(2) derived endpoint is solvable and cannot occur. -/
theorem not_linearTwo_binary_derived_endpoint
    {L M : Type*} [Group L] [Group M] [Finite L] [Finite M] [IsQuasisimple L]
    (hM : ClassicalGroup.IsPSL M 2 2)
    (eL : (L ⧸ center L) ≃* commutator M) : False := by
  obtain ⟨F, _, _, hc, ⟨e⟩⟩ := hM
  let : Group.IsSolvable (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) :=
    Theory.PSL2.OuterSolvable.isSolvable_of_card_two hc
  let : Group.IsSolvable M := Group.isSolvable_of_isSolvable_injective
    (f := e.toMonoidHom) e.injective
  let : Group.IsSolvable (L ⧸ center L) := Group.isSolvable_of_isSolvable_injective
    (f := eL.toMonoidHom) eL.injective
  let : IsSimpleGroup (L ⧸ center L) := IsQuasisimple.simple
  exact Group.IsPerfect.not_isSolvable (L ⧸ center L) inferInstance

/-- Source quasisimplicity excludes the small derived endpoint before using
the rank-one numerical formula. -/
theorem linearTwo_field_parameter
    {L M : Type*} [Group L] [Group M] [Finite L] [Finite M] [IsQuasisimple L]
    {n : ℕ} (hn : 0 < n) (hM : ClassicalGroup.IsPSL M 2 (2 ^ n))
    (eL : (L ⧸ center L) ≃* commutator M) : 2 ≤ n := by
  by_contra hsmall
  have hn1 : n = 1 := by omega
  exact not_linearTwo_binary_derived_endpoint (by simpa only [hn1, pow_one] using hM) eL

/-- The root witness is transported through the actual larger quotient. -/
theorem linearTwo_large_rank
    {K : Type*} [Group K] [Finite K] {n : ℕ}
    (hK : ClassicalGroup.IsPSL (K ⧸ center K) 2 (2 ^ (2 * n))) :
    2 * n ≤ primeRank 2 (K ⧸ center K) := by
  obtain ⟨F, _, _, hc, ⟨e⟩⟩ := hK
  rw [primeRank_equiv 2 e]
  exact Theory.PSL2.root_two_rank_ge F hc

/-- Numerical comparison for the field pair, with only the smaller-model
rank supplied by the rank-one owner. -/
theorem linearTwo_field_comparison
    {K L M : Type*} [Group K] [Group L] [Group M]
    [Finite K] [Finite L] [Finite M] [IsQuasisimple L]
    {n : ℕ} (hn : 0 < n)
    (hK : ClassicalGroup.IsPSL (K ⧸ center K) 2 (2 ^ (2 * n)))
    (hM : ClassicalGroup.IsPSL M 2 (2 ^ n))
    (eL : (L ⧸ center L) ≃* commutator M)
    (hsmall : primeRank 2 (L ⧸ center L) = n) :
    2 ≤ primeRank 2 (L ⧸ center L) ∧
      2 * primeRank 2 (L ⧸ center L) ≤ primeRank 2 (K ⧸ center K) := by
  rw [hsmall]
  exact ⟨linearTwo_field_parameter hn hM eL, linearTwo_large_rank hK⟩

/-- The source centerless rank-one field alternative is impossible once
the smaller PSL₂ automorphism estimate is supplied. -/
theorem exclude_linearTwo_field
    {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {z t : G} {L : Subgroup G}
    (h : TerminalCounterexample T z L t)
    (hs : NonterminalCentralizerShape T z L t)
    {M : Type*} [Group M] [Finite M] {n : ℕ} (hn : 0 < n)
    (hK : ClassicalGroup.IsPSL
      (enlargement t L ⧸ center (enlargement t L)) 2 (2 ^ (2 * n)))
    (hM : ClassicalGroup.IsPSL M 2 (2 ^ n))
    (eL : (L ⧸ center L) ≃* commutator M)
    (hZ : center (enlargement t L) = ⊥)
    (hAut : primeRank 2 (MulAut L) ≤ n) : False := by
  let := h.localSetup.component.quasisimple
  have hn2 := linearTwo_field_parameter hn hM eL
  have hlarge := linearTwo_large_rank hK
  have he := primeRank_equiv 2
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot)
  exact exclude_centerless_doubled_rank h hs hn2 (by omega) hAut hZ

end CFSG.Quasithin.Chapter16.EnlargementSieve.IntrinsicRanks.LiePairs
