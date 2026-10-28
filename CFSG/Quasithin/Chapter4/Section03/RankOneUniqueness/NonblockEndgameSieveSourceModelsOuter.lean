module
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockEndgameSieveSourceModelsCenter
public import Theory.GroupTheory.CComponent.FullRankOuterAction
public import Theory.SpecificGroups.Classical.SignedThreeCubicRank.Divisibility

/-!
# Outer torus action from corrected source geometry

Root faithfulness separates each prime-order torus element from the component.
At full component prime rank, the SQTK bound and coprimality of the full
quotient center force that element to act outerly. Its action therefore still
has prime order. This supplies nontrivial action without using radical movement.
Both exceptional models have cubic rank two, and at n=2 the torus has order
three, giving the entire outer-action clause of original 4.3.16(4).
Source: Aschbacher--Smith, A.3.18, pp.51--53, and 4.3.12--16, pp.617--618.
-/

@[expose] public section
noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock.EndgameSieve
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
variable {c : SourceConfiguration T L} {n : ℕ}

/-- Every prime-order source torus element acts outerly at component rank two. -/
theorem SecondarySourceData.torus_prime_action_not_inner_of_rank_two (s : SecondarySourceData c n)
    (D : Chapter12.Section02.ChosenModule T L V)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L)
    {p : ℕ} (hp : p.Prime) (ho : Odd p) (hd : p ∣ 2^n-1)
    (hr : 2 ≤ primeRank p s.component)
    (x : rootNormalizer c) (hxt : (x : G) ∈ s.torus) (hx : orderOf x=p) :
    s.action x ∉ MulAut.innerSubgroup (s.component ⧸ pCore 2 s.component) := by
  let : Fact p.Prime := ⟨hp⟩
  let := s.normal
  have hxn : x ∉ s.component := by
    intro hi
    have he : (x : G)=1 := mem_bot.mp ((SecondarySourceData.torus_disjoint_component s).le
      ⟨hxt,⟨x,hi,rfl⟩⟩)
    have hxone : x=1 := Subtype.ext he
    rw [hxone,orderOf_one] at hx
    exact hp.ne_one hx.symm
  exact CComponentPrimeRank.quotientAction_not_inner_of_outside s.component s.isComponent
    (SecondarySourceData.componentQuotient_center_coprime_of_torus_prime s D h hp ho hd)
    hr ((rootNormalizer_sqtk c D h).stronglyQuasithin p hp ho) ho x hx hxn

/-- Full rank gives the rank bound on the literal full quotient action image. -/
theorem SecondarySourceData.action_rank_le_two_of_component_rank_two (s : SecondarySourceData c n)
    (D : Chapter12.Section02.ChosenModule T L V)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L)
    {p : ℕ} (hp : p.Prime) (ho : Odd p) (hd : p ∣ 2^n-1)
    (hr : 2 ≤ primeRank p s.component) : primeRank p s.action.range ≤ 2 := by
  let : Fact p.Prime := ⟨hp⟩
  let := s.normal
  exact CComponentPrimeRank.quotientAction_rank_le_two s.component s.isComponent
    (SecondarySourceData.componentQuotient_center_coprime_of_torus_prime s D h hp ho hd)
    hr ((rootNormalizer_sqtk c D h).stronglyQuasithin p hp ho) ho

/-- A source torus element and its outer image both retain order p. -/
theorem SecondarySourceData.exists_outer_prime_torus_actor_of_rank_two (s : SecondarySourceData c n)
    (D : Chapter12.Section02.ChosenModule T L V)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L)
    {p : ℕ} (hp : p.Prime) (ho : Odd p) (hd : p ∣ 2^n-1)
    (hr : 2 ≤ primeRank p s.component) :
    ∃ x : rootNormalizer c, (x : G) ∈ s.torus ∧ orderOf x=p ∧
      orderOf (s.action x)=p ∧
      s.action x ∉ MulAut.innerSubgroup (s.component ⧸ pCore 2 s.component) := by
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨x,hxt,hx,_⟩ := SecondarySourceData.exists_outside_prime_actor s hp hd
  have hi := SecondarySourceData.torus_prime_action_not_inner_of_rank_two s D h hp ho hd hr x hxt hx
  refine ⟨x,hxt,hx,?_,hi⟩
  apply orderOf_eq_prime
  · rw [←map_pow,←hx,pow_orderOf_eq_one,map_one]
  · exact fun he => hi (he ▸ (MulAut.innerSubgroup _).one_mem)

/-- At n=2, cubic rank two makes the whole source torus image disjoint from inner automorphisms. -/
theorem SecondarySourceData.torusImage_inf_inner_eq_bot_of_cubic_rank_two
    (s : SecondarySourceData c n) (D : Chapter12.Section02.ChosenModule T L V)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hn : n=2) (hr : 2 ≤ primeRank 3 s.component) :
    SecondarySourceData.torusImage s ⊓ MulAut.innerSubgroup (s.component ⧸ pCore 2 s.component)=⊥ := by
  subst n
  apply eq_bot_iff.mpr
  rintro a ⟨⟨x,hxt,rfl⟩,hi⟩
  by_cases hx : x=1
  · simp only [hx,map_one,mem_bot]
  have hxorder : orderOf x=3 := by
    have ht : orderOf (⟨x,hxt⟩ : s.torus) ∣ 3 := by
      have hh := orderOf_dvd_natCard (⟨x,hxt⟩ : s.torus)
      norm_num [s.torus_card] at hh ⊢; exact hh
    have he : orderOf (⟨x,hxt⟩ : s.torus)=3 :=
      ((Nat.dvd_prime Nat.prime_three).mp ht).resolve_left (by
        intro he
        have hz := orderOf_eq_one_iff.mp he
        exact hx (Subtype.ext (congrArg (fun z : s.torus => (z : G)) hz)))
    exact ((rootNormalizer c).orderOf_coe x).symm.trans
      ((s.torus.orderOf_coe ⟨x,hxt⟩).trans he)
  exact (SecondarySourceData.torus_prime_action_not_inner_of_rank_two s D h Nat.prime_three
    (by decide) (by norm_num) hr x hxt hxorder hi).elim

/-- Both exceptional full quotient models have cubic rank two. -/
theorem SecondarySourceData.exceptional_model_cubic_rank_two (s : SecondarySourceData c n)
    (hm : ExceptionalModel (s.component ⧸ pCore 2 s.component) n) :
    2 ≤ primeRank 3 s.component := by
  rw [←primeRank_quotient_eq_of_isTwoGroup 3 (by decide) (pCore 2 s.component) pCore_isPGroup]
  rcases hm.2 with ⟨F,_,_,hF,⟨e⟩⟩ | ⟨F,_,_,J,hF,hc,⟨e⟩⟩
  · rw [primeRank_congr 3 e]
    exact Theory.SpecificGroups.SignedThreeCubicRank.linear_projective_of_three_dvd (by norm_num [hF])
  · rw [primeRank_congr 3 e]
    exact Theory.SpecificGroups.SignedThreeCubicRank.unitary_projective_of_three_dvd J
      (by decide : Nat.Prime 5) hF hc (by decide)

/-- The exceptional outer-action clause follows on the original torus from the actual full model. -/
theorem SecondarySourceData.exceptional_model_outer_torus (s : SecondarySourceData c n)
    (D : Chapter12.Section02.ChosenModule T L V)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hm : ExceptionalModel (s.component ⧸ pCore 2 s.component) n) :
    SecondarySourceData.torusImage s ⊓ MulAut.innerSubgroup (s.component ⧸ pCore 2 s.component)=⊥ :=
  SecondarySourceData.torusImage_inf_inner_eq_bot_of_cubic_rank_two s D h hm.1
    (SecondarySourceData.exceptional_model_cubic_rank_two s hm)

end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock.EndgameSieve
