module
public import Theory.GroupTheory.QuasithinBasic

/-!
# Prime rank of two-local subgroups

The invariant `twoLocalPrimeRank p G` is the supremum of the `p`-ranks of
normalizers of nontrivial 2-subgroups. For finite groups this is a bounded
supremum, and its upper-bound specification also covers the empty family.
It is bounded by ordinary prime rank and gives the fixed-prime form of the
quasithin condition.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
manuscript (1 March 2004), §A.2, in particular Lemma A.2.7, p. 34; this is
the invariant denoted `m₂,ₚ` there.
-/

@[expose] public section

/-- The maximal `p`-rank among all 2-local subgroups. -/
noncomputable def twoLocalPrimeRank (p : ℕ) (G : Type*) [Group G] : ℕ :=
  sSup {n : ℕ | ∃ M : Subgroup G, IsTwoLocal M ∧ n ≤ primeRank p M}

private theorem twoLocalPrimeRank_bddAbove (p : ℕ) (G : Type*) [Group G] [Finite G] :
    BddAbove {n : ℕ | ∃ M : Subgroup G, IsTwoLocal M ∧ n ≤ primeRank p M} := by
  obtain ⟨b, hb⟩ := (Set.finite_range (fun M : Subgroup G => primeRank p M)).bddAbove
  refine ⟨b, ?_⟩
  rintro n ⟨M, _, hn⟩
  exact hn.trans (hb (Set.mem_range_self M))

/-- Upper bounds on local prime rank are bounds on every 2-local. -/
theorem twoLocalPrimeRank_le_iff {G : Type*} [Group G] [Finite G] (p r : ℕ) :
    twoLocalPrimeRank p G ≤ r ↔ ∀ M : Subgroup G, IsTwoLocal M → primeRank p M ≤ r := by
  constructor
  · intro h M hM
    exact (le_csSup (twoLocalPrimeRank_bddAbove p G) ⟨M, hM, le_rfl⟩).trans h
  · intro h
    apply csSup_le'
    rintro n ⟨M, hM, hn⟩
    exact hn.trans (h M hM)

/-- The prime rank of each 2-local contributes to local prime rank. -/
theorem IsTwoLocal.primeRank_le {G : Type*} [Group G] [Finite G]
    {M : Subgroup G} (hM : IsTwoLocal M) (p : ℕ) :
    primeRank p M ≤ twoLocalPrimeRank p G :=
  (twoLocalPrimeRank_le_iff p _).mp le_rfl M hM

/-- With no 2-local subgroups, the local prime rank is zero. -/
theorem twoLocalPrimeRank_eq_zero_of_no_twoLocal {G : Type*} [Group G] [Finite G]
    (p : ℕ) (h : ∀ M : Subgroup G, ¬ IsTwoLocal M) : twoLocalPrimeRank p G = 0 := by
  apply Nat.eq_zero_of_le_zero
  exact (twoLocalPrimeRank_le_iff p 0).mpr fun M hM => (h M hM).elim

/-- Local prime rank is bounded by ordinary prime rank. -/
theorem twoLocalPrimeRank_le_primeRank {G : Type*} [Group G] [Finite G] (p : ℕ) :
    twoLocalPrimeRank p G ≤ primeRank p G :=
  (twoLocalPrimeRank_le_iff p _).mpr fun M _ =>
    Theory.GroupTheory.primeRank_le_of_injective p M.subtype M.subtype_injective

/-- Quasithinness bounds the local rank at every odd prime. -/
theorem isQuasithin_iff_twoLocalPrimeRank {G : Type*} [Group G] [Finite G] :
    IsQuasithin G ↔ ∀ p : ℕ, p.Prime → Odd p → twoLocalPrimeRank p G ≤ 2 := by
  rw [Theory.GroupTheory.isQuasithin_iff_twoLocal]
  constructor
  · intro h p hp ho
    exact (twoLocalPrimeRank_le_iff p 2).mpr fun M hM => h M hM p hp ho
  · intro h M hM p hp ho
    exact (hM.primeRank_le p).trans (h p hp ho)
