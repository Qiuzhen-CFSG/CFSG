module

public import Theory.SpecificGroups.PSL2.ElevenConjugateBudget.Generation
public import Theory.SpecificGroups.PSL2.ElevenConjugateBudget.Coverage
public import Theory.Representation.BinaryOffender.ElementaryConjugateBudget.Transport
public import Theory.SpecificGroups.PSL2.OddAutomorphismRank
public import Theory.Representation.BinaryOffender.CubicConjugateBound

/-!
# The elementary inner conjugate budget for PSL₂(11)

All four representative generation calculations are proved in Generation.
The automorphism two-rank bound is two, while each cyclic representative
has rank at most one. Their three- and two-conjugate bounds therefore give
budget four. Automorphism transport keeps every conjugator in PSL₂, and a
coefficient-field equivalence extends the result to every field of order 11.

The exhaustive coverage theorem discharges the last premise in `budget`,
which supplies exactly the generation assumption of Chapter B's
`RankOneSmall.Eleven.two_lt_cubicRatio_of_elementary_generation`.
The source application is
Guralnick–Malle, Classification of 2F-modules I, Proposition 4.1, pp.8–9,
and Aschbacher–Smith K.2, printed p.453.
-/

public section

open Matrix Subgroup
namespace Theory.PSL2.ElevenConjugateBudget
local instance : Fact (Nat.Prime 11) := ⟨by decide⟩

open Representation.BinaryOffender

private theorem cyclic_rank_le_one {G : Type*} [_root_.Group G] (x : G)
    (hx : x ^ 2 = 1) : rank (zpowers x) ≤ 1 := by
  have hc : Nat.card (zpowers x) ≤ 2 := by
    rw [Nat.card_zpowers]
    exact orderOf_le_of_pow_eq_one (by decide) hx
  exact (Nat.log_mono_right hc).trans (by decide : Nat.log 2 2 ≤ 1)

theorem actor_spans (i : Fin 4) : ∃ c : Fin (count i) → S,
    (MulAut.conj : S →* MulAut S).range ≤
      ⨆ j, (actor i).map (MulAut.conj (MulAut.conj (c j))).toMonoidHom := by
  fin_cases i
  · exact ⟨triple, inner_cyclic_span⟩
  · exact ⟨triple, outer_cyclic_span⟩
  · exact ⟨pair, inner_four_span⟩
  · exact ⟨pair, outer_four_span⟩

theorem prime_budget_of_actor_coverage (hcov : ActorCoverage) :
    ElementaryInnerConjugateBudget S 4 := by
  intro A hA
  obtain ⟨i,a,rfl⟩ := hcov A hA
  obtain ⟨c,hc⟩ := actor_spans i
  refine ⟨count i, fun j => a (c j), ?_, inner_conjugate_span_map a (actor i) c hc⟩
  have hr : rank ((actor i).map (MulAut.congr a).toMonoidHom) ≤ 2 :=
    rank_le_of_primeRank_le hA (primeField_automorphism_two_rank (p := 11) (by decide))
  rw [rank_map_equiv]
  fin_cases i
  · have ht : MulAut.conj t ^ 2 = 1 := by rw [← map_pow, t_sq, map_one]
    have := cyclic_rank_le_one (MulAut.conj t) ht
    change 3 * rank (zpowers (MulAut.conj t)) ≤ 4
    omega
  · have := cyclic_rank_le_one d (by simpa only [pow_two] using d_sq)
    change 3 * rank (zpowers d) ≤ 4
    omega
  · rw [rank_map_equiv] at hr
    change 2 * rank innerFour ≤ 4
    change rank innerFour ≤ 2 at hr
    omega
  · rw [rank_map_equiv] at hr
    change 2 * rank outerFour ≤ 4
    change rank outerFour ≤ 2 at hr
    omega

/-- The prime-field calculation transports to every field carrier of cardinality eleven. -/
theorem budget_of_actor_coverage (hcov : ActorCoverage)
    (K : Type*) [Field K] [Finite K] (hK : Nat.card K = 11) :
    ElementaryInnerConjugateBudget (ProjectiveSpecialLinearGroup (Fin 2) K) 4 := by
  let : Fintype K := Fintype.ofFinite K
  let eF : F ≃+* K := FiniteField.ringEquivOfCardEq (by
    rw [ZMod.card, ← Nat.card_eq_fintype_card, hK])
  exact (prime_budget_of_actor_coverage hcov).map (GorensteinWalter.psl2RingEquiv eF)

/-- Every nontrivial elementary two-subgroup of Aut(PSL₂(K)), for |K| = 11,
has inner conjugates generating over Inn(PSL₂(K)) with budget four.
All conjugators belong to PSL₂(K), including for actors with outer elements. -/
theorem budget (K : Type*) [Field K] [Finite K] (hK : Nat.card K = 11) :
    ElementaryInnerConjugateBudget (ProjectiveSpecialLinearGroup (Fin 2) K) 4 :=
  budget_of_actor_coverage actor_coverage K hK

end Theory.PSL2.ElevenConjugateBudget
