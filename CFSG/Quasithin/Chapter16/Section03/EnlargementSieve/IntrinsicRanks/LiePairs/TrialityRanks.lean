module

public import CFSG.Quasithin.Chapter16.Section03.EnlargementSieve.IntrinsicRanks.Bounds
public import Theory.SpecificGroups.Triality.StandardTwoRank.RankTable
public import Theory.GroupTheory.PrimeRankCentralCover

/-!
# The triality field pair in the enlargement sieve

The genuine models at exponents n and 2n have ranks 5n and 10n. Perfectness
identifies the smaller derived endpoint, and its automorphism rank is 5n.
Faithful automorphism descent bounds any actual smaller component by this
same number. These calculations discharge every numerical premise in the
triality branch of the ordinary Lie-pair comparison, including n = 1.

Both source quotient conventions are retained. The adapter from O₂ to the
center uses E1 and the proved component center/core equality. The quotient
exclusion keeps the earlier source assertion Z(K) = 1 explicit: this is the
triality specialization of 16.1.2(1), as used in the convention preceding
16.1.4. It is a covering-group assertion, not an unproved simplicity premise
on the standard model. The final Lie-pair owner supplies this earlier input.
The exclusion for an actual carrier model needs no such extra input.

Source: Aschbacher–Smith, 16.1.7(3a), printed pp.1171–1172, the ordinary
pairs in 16.3.9, p.1180, and the rank table on p.356 (`refs/quasithin.pdf`).
-/

public section
noncomputable section

open Subgroup Theory.GroupTheory Triality.Standard
namespace CFSG.Quasithin.Chapter16.EnlargementSieve.IntrinsicRanks.LiePairs

/-- The larger or smaller actual triality model has intrinsic rank 5n. -/
theorem triality_rank {M : Type*} [Group M] {n : ℕ}
    (hn : 0 < n) (hM : IsTrialityGroupAt (2 ^ n) M) :
    primeRank 2 M = 5 * n :=
  TwoRank.twoRank_eq_five_mul_of_model n hn hM

/-- The smaller derived endpoint in 16.1.7(3a) has rank 5n, including n = 1. -/
theorem triality_derived_rank {M : Type*} [Group M] {n : ℕ}
    (hn : 0 < n) (hM : IsTrialityGroupAt (2 ^ n) M) :
    primeRank 2 (commutator M) = 5 * n :=
  TwoRank.derived_twoRank_eq_five_mul_of_model n hn hM

/-- The actual smaller derived endpoint has automorphism rank exactly 5n. -/
theorem triality_derived_automorphism_rank {M : Type*} [Group M] {n : ℕ}
    (hn : 0 < n) (hM : IsTrialityGroupAt (2 ^ n) M) :
    primeRank 2 (MulAut (commutator M)) = 5 * n :=
  TwoRank.derived_automorphism_twoRank_eq_five_mul_of_model n hn hM

/-- The exact doubled comparison on the central quotients used in 16.3.9. -/
theorem triality_field_comparison {K L M : Type*}
    [Group K] [Group L] [Group M] [Finite K] [Finite L] [Finite M]
    {n : ℕ} (hn : 0 < n)
    (hK : IsTrialityGroupAt (2 ^ (2 * n)) (K ⧸ center K))
    (hM : IsTrialityGroupAt (2 ^ n) M)
    (eL : (L ⧸ center L) ≃* commutator M) :
    2 ≤ primeRank 2 (L ⧸ center L) ∧
      primeRank 2 (K ⧸ center K) = 2 * primeRank 2 (L ⧸ center L) := by
  have hsmall := (primeRank_equiv 2 eL).trans (triality_derived_rank hn hM)
  have hlarge := triality_rank (by omega : 0 < 2 * n) hK
  omega

/-- The same doubled comparison on the literal O₂ quotients of 16.1.7(3a). -/
theorem triality_field_twoCore_comparison {K L M : Type*}
    [Group K] [Group L] [Group M] [Finite K] [Finite L] [Finite M]
    {n : ℕ} (hn : 0 < n)
    (hK : IsTrialityGroupAt (2 ^ (2 * n)) (K ⧸ pCore 2 K))
    (hM : IsTrialityGroupAt (2 ^ n) M)
    (eL : (L ⧸ pCore 2 L) ≃* commutator M) :
    2 ≤ primeRank 2 (L ⧸ pCore 2 L) ∧
      primeRank 2 (K ⧸ pCore 2 K) = 2 * primeRank 2 (L ⧸ pCore 2 L) := by
  have hsmall := (primeRank_equiv 2 eL).trans (triality_derived_rank hn hM)
  have hlarge := triality_rank (by omega : 0 < 2 * n) hK
  omega

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G}
  {z t : G} {L : Subgroup G}

/-- The original component supplies perfectness for faithful descent; the
standard model supplies the entire automorphism estimate. -/
theorem triality_smaller_automorphism_rank_le
    (h : TerminalCounterexample T z L t)
    {M : Type*} [Group M] [Finite M] {n : ℕ} (hn : 0 < n)
    (hM : IsTrialityGroupAt (2 ^ n) M)
    (eL : (L ⧸ center L) ≃* commutator M) :
    primeRank 2 (MulAut L) ≤ 5 * n := by
  let := h.localSetup.component.quasisimple
  have hquotient := (primeRank_equiv 2 (MulAut.congr eL)).trans
    (triality_derived_automorphism_rank hn hM)
  exact (automorphism_primeRank_le_quotient_center (E := L) 2).trans_eq hquotient

/-- The field branch with an actual larger carrier contradicts the source
rank inequality, with no numerical or model-simplicity premise. -/
theorem exclude_triality_field_of_models
    (h : TerminalCounterexample T z L t)
    (hs : NonterminalCentralizerShape T z L t)
    {M : Type*} [Group M] [Finite M] {n : ℕ} (hn : 0 < n)
    (hK : IsTrialityGroupAt (2 ^ (2 * n)) (enlargement t L))
    (hM : IsTrialityGroupAt (2 ^ n) M)
    (eL : (L ⧸ center L) ≃* commutator M) : False := by
  have hlarge := triality_rank (by omega : 0 < 2 * n) hK
  have hAut := triality_smaller_automorphism_rank_le h hn hM eL
  have hupper := rank_le_aut h hs
  omega

/-- The quotient-model version retains precisely the earlier source
centerlessness assertion for the larger covering group. -/
theorem exclude_triality_field
    (h : TerminalCounterexample T z L t)
    (hs : NonterminalCentralizerShape T z L t)
    {M : Type*} [Group M] [Finite M] {n : ℕ} (hn : 0 < n)
    (hK : IsTrialityGroupAt (2 ^ (2 * n))
      (enlargement t L ⧸ center (enlargement t L)))
    (hM : IsTrialityGroupAt (2 ^ n) M)
    (eL : (L ⧸ center L) ≃* commutator M)
    (hZ : center (enlargement t L) = ⊥) : False := by
  let eK : (enlargement t L ⧸ center (enlargement t L)) ≃* enlargement t L :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  exact exclude_triality_field_of_models h hs hn (hK.of_mulEquiv eK.symm) hM eL

/-- Application to the literal source O₂ quotients. E1 and the actual two
component embeddings discharge both quotient-convention conversions. -/
theorem exclude_triality_field_of_twoCore_models
    (he : HasEvenTypeCentralizers G) (h : TerminalCounterexample T z L t)
    (hs : NonterminalCentralizerShape T z L t)
    (hcomponent : IsCentralizerComponent t (enlargement t L))
    {M : Type*} [Group M] [Finite M] {n : ℕ} (hn : 0 < n)
    (hK : IsTrialityGroupAt (2 ^ (2 * n))
      (enlargement t L ⧸ pCore 2 (enlargement t L)))
    (hM : IsTrialityGroupAt (2 ^ n) M)
    (eL : (L ⧸ pCore 2 L) ≃* commutator M)
    (hZ : center (enlargement t L) = ⊥) : False := by
  let eK := QuotientGroup.quotientMulEquivOfEq
    (he.component_center_eq_twoCore h.involution hcomponent)
  let eSmall := QuotientGroup.quotientMulEquivOfEq
    (he.component_center_eq_twoCore h.localSetup.involution h.localSetup.component)
  exact exclude_triality_field h hs hn (hK.of_mulEquiv eK) hM (eSmall.trans eL) hZ

end CFSG.Quasithin.Chapter16.EnlargementSieve.IntrinsicRanks.LiePairs
