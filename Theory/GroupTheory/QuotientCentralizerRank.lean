module
public import Theory.GroupTheory.PrimeRankResidualCentralizer
public import Theory.GroupTheory.OddPrimeRankOneSylow
public import Theory.GroupTheory.PrimeRankCyclicSylow

/-!
# Rank one in a factor centralizer in a quotient

If a normal factor meets the full quotient kernel in its two-core, the
preimage of its quotient centralizer commutes with it modulo that core.
The residual-centralizer rank inequality bounds this preimage by rank one
when the ambient odd-prime rank is at most two and the factor contributes
one direction. Odd rank one makes its Sylow subgroups cyclic, so the
bound passes to the quotient centralizer without a coprime-kernel assumption.

Source application: Aschbacher–Smith 13.4.7(2), printed p.902.
-/

public noncomputable section
open Subgroup
namespace Theory.GroupTheory.ResidualCentralizerRank
variable {H Q : Type*} [Group H] [Finite H] [Group Q]

/-- If the kernel on a normal factor is its two-core, its complementary
centralizer in a quotient has odd rank at most one. The full quotient
kernel is retained and need not be a two-group. -/
theorem quotient_centralizer_rank_le_one {p : ℕ} [Fact p.Prime]
    (hp : Odd p) (K : Subgroup H) [K.Normal]
    (q : H →* Q) (hq : Function.Surjective q)
    (hk : K ⊓ q.ker = K.pCoreIn 2)
    (hz : Nat.Coprime p (Nat.card (center (K ⧸ pCore 2 K))))
    (hK : 1 ≤ primeRank p K) (hH : primeRank p H ≤ 2) :
    primeRank p (centralizer (K.map q : Set Q)) ≤ 1 := by
  let D := (centralizer (K.map q : Set Q)).comap q
  have hc : ⁅D,K⁆ ≤ K.pCoreIn 2 := by
    rw [←hk]
    refine le_inf (commutator_le_right D K) ?_
    rw [←Subgroup.map_eq_bot_iff, map_commutator]
    apply commutator_eq_bot_iff_le_centralizer.mpr
    exact map_comap_le _ _
  have hr := primeRank_sum_le_of_normalized_factor hp D K le_normalizer_of_normal
    ((commutator_mono (map_subtype_le (pResidual 2 D)) le_rfl).trans hc) hz
  have hb : primeRank p (D ⊔ K : Subgroup H) ≤ 2 :=
    (primeRank_subgroup_le p _).trans hH
  have hd : primeRank p D ≤ 1 := by omega
  let S : Sylow p D := Classical.choice inferInstance
  exact S.primeRank_le_one_of_surjective (S.isCyclic_of_odd_of_primeRank_le_one hp hd)
    (q.subgroupComap (centralizer (K.map q : Set Q)))
    (q.subgroupComap_surjective_of_surjective _ hq)
end Theory.GroupTheory.ResidualCentralizerRank
