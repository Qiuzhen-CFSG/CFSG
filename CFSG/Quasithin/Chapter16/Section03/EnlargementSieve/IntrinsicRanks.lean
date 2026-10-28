module

public import CFSG.Quasithin.Chapter16.Section03.EnlargementSieve.IntrinsicRanks.Bounds
public import CFSG.Quasithin.Chapter16.Section03.EnlargementSieve.IntrinsicRanks.Odd
public import CFSG.Quasithin.Chapter16.Section03.EnlargementSieve.Nonfusion
public import Theory.GroupTheory.PrimeRankInvolutionLift
public import Theory.GroupTheory.PrimeRankProduct

/-!
# Intrinsic rank deductions for the enlargement sieve

The four genuine alternatives imply the odd-rank witnesses needed for
16.3.10: elementary nines in M₁₂ and J₂ lift through O₂(K), while the A₆
and A₈ smaller components suffice in the other cases. This discharges all
intrinsic odd-rank premises in the nonfusion implication below.

For 16.3.9, the general rank contradictions and the identification Z(K)=⟨t⟩
in the rank-five double-cover branch are available in `Bounds`. The reusable
central-cover formula requires actual involution lifts. The remaining
swapped-factor calculations, Lie-pair model ranks and exceptional normalizer
lift still have to be supplied before asserting the four-alternative sieve.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
16.3.9–10, printed pp.1180–1181. This module does not assert completion of
16.3.9 or replace its missing intrinsic cases by a conclusion certificate.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter16.EnlargementSieve.IntrinsicRanks
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {z t : G} {L : Subgroup G}

/-- Once the intrinsic sieve and the local conjugacy are proved, no further
model-rank premises are needed for either nonfusion assertion. -/
theorem nonfusion_of_fourAlternatives {𝒦 : GroupClass}
    (hG : Hypothesis1611 𝒦 G) (h : TerminalCounterexample T z L t)
    (balance : ComponentTransfer.OrdinaryBalanceAt (involutionCentralizer t) z)
    (hK : IsCentralizerComponent t (enlargement t L))
    (hc : FourAlternatives (enlargement t L) L z)
    (hfuse : IsConj t (t * z)) : ¬ IsConj z t ∧ ¬ IsConj z (t * z) := by
  obtain ⟨hr, hd⟩ := odd_rank_witnesses
    (ComponentTransfer.le_layerClosure (involutionCentralizer t) L) hc
  exact nonfusion_of_rank_and_local_conjugacy hG h balance hK hr hd hfuse

end CFSG.Quasithin.Chapter16.EnlargementSieve.IntrinsicRanks
