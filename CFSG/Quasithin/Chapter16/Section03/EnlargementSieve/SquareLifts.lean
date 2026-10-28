module

public import CFSG.Quasithin.Chapter16.Section03.EnlargementSieve.SquareLifts.Local
public import CFSG.Quasithin.Chapter16.Section03.EnlargementSieve.SquareLifts.Core
public import CFSG.Quasithin.Chapter16.Section03.EnlargementSieve.SquareLifts.CoverExclusion
public import CFSG.Quasithin.Chapter16.Section03.EnlargementSieve.Nonfusion

/-!
# Square lifts in the enlargement sieve

The local fusion and normalizer-square obstruction of Aschbacher–Smith,
16.3.9–11 (printed pp.1180–1181), follow from the genuine uniform 16.3.8
shape statement. The nontrivial two-core in the proper component branch
is identified with the ambient subgroup ⟨t⟩ using the two Sylow centralizers.

The sporadic-cover exclusion is supplied by `CoverExclusion`: its inner and
outer branches use the literal earlier 16.1.5 and I.2.2 statements. In the
outer case, the fixed subgroup in K/⟨t⟩ is distinguished from the image of
C_K(z); the two-residual and normalization transports produce an actual
normalizer-square witness for the local obstruction.
-/

public section
namespace CFSG.Quasithin.Chapter16.EnlargementSieve
open Subgroup Theory.GroupTheory

/-- Local fusion discharges the conjugacy premise in the odd-rank nonfusion
argument. The intrinsic model ranks remain with the rank-sieve owner. -/
theorem nonfusion_of_rank_and_shape {G : Type*} [Group G] [Finite G]
    {𝒦 : GroupClass} {T : Sylow 2 G} {z t : G} {L : Subgroup G}
    (hG : Hypothesis1611 𝒦 G) (h : TerminalCounterexample T z L t)
    (balance : ComponentTransfer.OrdinaryBalanceAt (involutionCentralizer t) z)
    (hK : IsCentralizerComponent t (enlargement t L))
    (hK3 : 2 ≤ primeRank 3 (enlargement t L)) (hL3 : 3 ∣ Nat.card L)
    (hs : NonterminalCentralizerShape T z L t) :
    ¬ IsConj z t ∧ ¬ IsConj z (t * z) :=
  nonfusion_of_rank_and_local_conjugacy hG h balance hK hK3 hL3
    (isConj_mul_original h hs)

end CFSG.Quasithin.Chapter16.EnlargementSieve
