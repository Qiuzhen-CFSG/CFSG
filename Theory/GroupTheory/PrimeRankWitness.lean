module

public import Theory.PrimeRank
public import Mathlib.GroupTheory.Schreier

/-!
# Elementary abelian witnesses for prime rank

An injective homomorphism from an abelian group of exponent dividing `p` and
order `p^e` witnesses prime rank at least `e`. The cardinality divides `p` to
the generator rank by Schreier's generator bound, and the image is an abelian
`p`-subgroup. This is the rank calculation used for root groups in
Aschbacher–Smith, *The Classification of Quasithin Groups*, Lemma A.2.17.
-/

public section

open scoped IsMulCommutative

private theorem group_rank_le_nat_card (G : Type*) [Group G] [Finite G] :
    Group.rank G ≤ Nat.card G := by
  classical
  let := Fintype.ofFinite G
  simpa [Nat.card_eq_fintype_card] using
    (Group.rank_le (G := G) (S := Finset.univ) (by simp))

/-- Each abelian `p`-subgroup contributes its generator rank to the prime rank. -/
theorem Subgroup.rank_le_primeRank {G : Type*} [Group G] [Finite G]
    (p : ℕ) (A : Subgroup G) (hAp : IsPGroup p A) [IsMulCommutative A] :
    Group.rank A ≤ primeRank p G := by
  apply le_csSup
  · refine ⟨Nat.card G, ?_⟩
    rintro n ⟨B, _, _, hfg, hn⟩
    exact hn.trans ((group_rank_le_nat_card B).trans B.card_le_card_group)
  · exact ⟨A, hAp, inferInstance, inferInstance, le_rfl⟩

/-- An embedded elementary abelian group of order `p^e` witnesses rank at least `e`. -/
theorem primeRank_ge_of_elementary_embedding {G A : Type*} [Group G] [Finite G] [CommGroup A]
    [Finite A] {p e : ℕ} [Fact p.Prime]
    (hpow : ∀ a : A, a ^ p = 1) (hcard : Nat.card A = p ^ e)
    (f : A →* G) (hf : Function.Injective f) : e ≤ primeRank p G := by
  have hAp : IsPGroup p A := fun a => ⟨1, by simpa using hpow a⟩
  have hr : e ≤ Group.rank A := by
    apply (Nat.pow_dvd_pow_iff_le_right (Fact.out : p.Prime).one_lt).mp
    rw [← hcard]
    exact card_dvd_exponent_pow_rank' A hpow
  have hrange := Subgroup.rank_le_primeRank p f.range
    (hAp.of_surjective f.rangeRestrict f.rangeRestrict_surjective)
  rw [← Group.rank_congr (MonoidHom.ofInjective hf)] at hrange
  exact hr.trans hrange

