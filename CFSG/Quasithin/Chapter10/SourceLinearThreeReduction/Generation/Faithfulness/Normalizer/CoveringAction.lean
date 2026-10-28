module
public import CFSG.Quasithin.ChapterC.Section04.A5FiniteNormality
public import Theory.GroupTheory.PerfectPairOrder

/-!
# Simple-seed action in the covering counterexample

A nontrivial action of the genuine C.2.8 span on a normal component retains
all its odd ranks: its kernel is a two-group. Full-rank characteristicity
then forces the original seed to be normalized when that image has rank at
most one at an odd divisor of the seed quotient. Burnside supplies a prime
outside three. No A₅ marking is required.

Source: Aschbacher--Smith C.4.5--8, pp.152--154, used in 4.4.6, p.620.
The literal covering and Hall-kernel applications are in CoveringSource.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC.HypothesisC28
variable {G : Type*} [Group G] [Finite G] {H M L R V : Subgroup G}

/-- A nontrivial normal-component action preserves every odd rank of the
original simple-seed span; its kernel is proved to be a two-group. -/
theorem nonnormal_simple_span_action_odd_rank
    (h : HypothesisC28 KnownSimple.IsKnownSimple H M L R V)
    [IsSimpleGroup (L ⧸ pCore 2 L)]
    (hn : ¬ M ≤ normalizer (L : Set G))
    (K : Subgroup H) [K.Normal]
    (hne : coreCentralActorImage K ((conjugateSpanBy L M).subgroupOf H) ≠ ⊥)
    {p : ℕ} [Fact p.Prime] (ho : Odd p) :
    primeRank p (coreCentralActorImage K ((conjugateSpanBy L M).subgroupOf H)) =
      primeRank p (conjugateSpanBy L M) := by
  let A := L.subgroupOf M
  let X := conjugateSpanBy A (⊤ : Subgroup M)
  let Y := conjugateSpanBy L M
  have hYM : Y ≤ M := conjugateSpanBy_le_self h.component_le
  have hYH : Y ≤ H := hYM.trans h.local_le
  have hmap : X.map M.subtype = Y := by
    change (conjugateSpanBy A ⊤).map M.subtype = Y
    rw [map_conjugateSpanBy, map_subgroupOf_eq_of_le h.component_le,
      ← MonoidHom.range_eq_map, range_subtype]
  have hM : IsSQTK KnownSimple.IsKnownSimple M :=
    (IsSQTK.equiv (subgroupOfEquivOfLe h.local_le)).mp (h.sqtk.subgroup (M.subgroupOf H))
  have hQ : IsSQTK KnownSimple.IsKnownSimple (M ⧸ pCore 2 M) := by
    refine ⟨?_,hM.isKGroup.quotient _⟩
    intro p hp ho
    let : Fact p.Prime := ⟨hp⟩
    exact (primeRank_quotient_le_of_isTwoGroup p ho _ pCore_isPGroup).trans
      (hM.stronglyQuasithin p hp ho)
  have hi : (normalizer (A : Set M)).index = 2 := by
    rcases Chapter1.Section02.proposition_1_2_1_three_orbit_source hQ h.component with hN | hi
    · let := hN
      apply (hn ?_).elim
      have hh := A.le_normalizer_map M.subtype
      simpa only [normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype, A,
        map_subgroupOf_eq_of_le h.component_le] using hh
    · exact hi
  let ae := subgroupOfEquivOfLe h.component_le
  let : IsSimpleGroup (A ⧸ pCore 2 A) :=
    (QuotientGroup.congr _ _ ae (pCore_map_iso 2 ae)).isSimpleGroup
  let j : H →* normalizer (K : Set H) :=
    { toFun := fun x => ⟨x, by rw [normalizer_eq_top]; exact mem_top x⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  let f := (normalizerCoreCentralAction K).comp j
  have himage (U : Subgroup H) : U.map f = coreCentralActorImage K U := by
    apply le_antisymm
    · rintro x ⟨u,hu,rfl⟩
      exact mem_map_of_mem (normalizerCoreCentralAction K) (show j u ∈ U.subgroupOf _ from hu)
    · rintro x ⟨u,hu,rfl⟩
      exact ⟨(u : H), hu, rfl⟩
  let i := inclusion h.local_le
  have hiX : X.map i = Y.subgroupOf H := by
    apply map_injective H.subtype_injective
    rw [map_map, map_subgroupOf_eq_of_le hYH]
    exact hmap
  have hfinal : X.map (f.comp i) = coreCentralActorImage K (Y.subgroupOf H) := by
    rw [← map_map, hiX, himage]
  have hr := pair_span_action_odd_rank A h.component hi (f.comp i)
    (hfinal.symm ▸ hne) ho
  rw [hfinal] at hr
  have heq : primeRank p X = primeRank p Y := by
    rw [← hmap]
    exact primeRank_equiv p (X.equivMapOfInjective M.subtype M.subtype_injective)
  exact hr.trans heq

/-- An action bound of one at an odd divisor of the seed quotient forces
normality of that original seed. -/
theorem normalizes_of_simple_component_action_rank_le_one
    (h : HypothesisC28 KnownSimple.IsKnownSimple H M L R V)
    [IsQuasisimple (L ⧸ pCore 2 L)] (hz : center (L ⧸ pCore 2 L) = ⊥)
    (K : Subgroup H) [K.Normal]
    (hne : coreCentralActorImage K ((conjugateSpanBy L M).subgroupOf H) ≠ ⊥)
    {p : ℕ} [Fact p.Prime] (ho : Odd p) (hd : p ∣ Nat.card (L ⧸ pCore 2 L))
    (hr : primeRank p (coreCentralActorImage K ((conjugateSpanBy L M).subgroupOf H)) ≤ 1) :
    M ≤ normalizer (L : Set G) := by
  by_contra hn
  let : IsSimpleGroup ((L ⧸ pCore 2 L) ⧸ center (L ⧸ pCore 2 L)) := IsQuasisimple.simple
  let : IsSimpleGroup (L ⧸ pCore 2 L) :=
    ((QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot).symm.isSimpleGroup
  have he := h.nonnormal_simple_span_action_odd_rank hn K hne ho
  have hpos : 0 < primeRank p (L ⧸ pCore 2 L) := by
    have hh : primeRank p (L ⧸ pCore 2 L) ≠ 0 :=
      fun hzero => PrimeRank.eq_zero_iff_not_dvd_card.mp hzero hd
    omega
  exact hn (h.normalizes_of_span_odd_rank ho hz hpos (by omega))

/-- The constrained component's cubic rank supplies its normality. The
remaining odd ranks force original-seed normality without an A₅ marking. -/
theorem normalizes_of_simple_constrained_central_ranks
    (h : HypothesisC28 KnownSimple.IsKnownSimple H M L R V)
    [IsQuasisimple (L ⧸ pCore 2 L)] (hz : center (L ⧸ pCore 2 L) = ⊥)
    (K : Subgroup H) (hK : K.IsCComponent) (hq : IsQuasisimple (K ⧸ pCore 2 K))
    (hout : ¬ K ≤ M.subgroupOf H) (hfK : generalizedFitting K = pCore 2 K)
    (hr3 : 2 ≤ primeRank 3 (coreCentralQuotient K))
    (hr : ∀ p : ℕ, p.Prime → Odd p → p ≠ 3 →
      primeRank p (coreCentralQuotient K) ≤ 1) :
    M ≤ normalizer (L : Set G) := by
  let : K.Normal := h.constrained_component_normal_of_central_threeRank K hK hq hout hfK hr3
  let : IsSimpleGroup ((L ⧸ pCore 2 L) ⧸ center (L ⧸ pCore 2 L)) := IsQuasisimple.simple
  let : Nontrivial (L ⧸ pCore 2 L) :=
    (QuotientGroup.mk'_surjective (center (L ⧸ pCore 2 L))).nontrivial
  obtain ⟨p,hp,ho,hp3,hd⟩ := Perfect.exists_odd_prime_ne_dvd_card
    (L ⧸ pCore 2 L) Nat.prime_three
  let : Fact p.Prime := ⟨hp⟩
  exact h.normalizes_of_simple_component_action_rank_le_one hz K
    (h.constrained_span_action_nontrivial K hK hq hout) ho hd
    ((h.constrained_span_action_rank_le_central_quotient K hK hq p).trans (hr p hp ho hp3))

/-- The order of the actual central quotient supplies every required
noncubic rank bound. -/
theorem normalizes_of_simple_constrained_central_order
    (h : HypothesisC28 KnownSimple.IsKnownSimple H M L R V)
    [IsQuasisimple (L ⧸ pCore 2 L)] (hz : center (L ⧸ pCore 2 L) = ⊥)
    (K : Subgroup H) (hK : K.IsCComponent) (hq : IsQuasisimple (K ⧸ pCore 2 K))
    (hout : ¬ K ≤ M.subgroupOf H) (hfK : generalizedFitting K = pCore 2 K)
    (hr3 : 2 ≤ primeRank 3 (coreCentralQuotient K))
    {a b c : ℕ} (hc : Squarefree c)
    (hcard : Nat.card (coreCentralQuotient K) ∣ 2 ^ a * 3 ^ b * c) :
    M ≤ normalizer (L : Set G) := by
  apply h.normalizes_of_simple_constrained_central_ranks hz K hK hq hout hfK hr3
  intro p hp ho hp3
  let : Fact p.Prime := ⟨hp⟩
  exact primeRank_le_one_of_card_dvd_two_prime_squarefree _ Nat.prime_three ho hp3 hc hcard
end CFSG.Quasithin.ChapterC.HypothesisC28
