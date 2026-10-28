module

public import Theory.Alternating.PrimeRank
public import Theory.SpecificGroups.Alternating.BlockEmbeddings
public import Theory.GroupTheory.PrimeRankProduct
public import Theory.Quasithin.LocalRank
public import Theory.Quasithin.Rank

/-!
# The A₄ × A₆ obstruction in A₁₀

The disjoint-block A₄ × A₆ subgroup has 3-rank three and normalizes the
image of its normal subgroup V₄ × 1. That image is a nontrivial two-group,
so its actual ambient normalizer is a two-local subgroup with 3-rank at
least three. Thus A₁₀ is not quasithin. The degree embeddings and subgroup
inheritance of quasithinness exclude all larger alternating groups as well.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
Lemma A.2.16, printed p.38.
-/

public section

open scoped IsMulCommutative

namespace alternatingGroup

open GLS3.Chapter5.PRank

/-- The A₄ and A₆ factors contribute one and two independent 3-generators. -/
theorem four_prod_six_primeRank :
    primeRank 3 (alternatingGroup (Fin 4) × alternatingGroup (Fin 6)) = 3 := by
  rw [primeRank_prod_eq_add, alternating_primeRank_of_odd_prime 4 3 (by decide) (by decide),
    alternating_primeRank_of_odd_prime 6 3 (by decide) (by decide)]

/-- The actual normalizer of the embedded V₄ contains the disjoint-block A₄ × A₆. -/
theorem ten_contains_four_prod_six_twoLocal :
    ∃ M : Subgroup (alternatingGroup (Fin 10)), IsTwoLocal M ∧
      ∃ f : alternatingGroup (Fin 4) × alternatingGroup (Fin 6) →* M,
        Function.Injective f := by
  let K := kleinFour (Fin 4)
  let : K.Normal := normal_kleinFour (by simp)
  let Q : Subgroup (alternatingGroup (Fin 4) × alternatingGroup (Fin 6)) := K.prod ⊥
  have : Q.Normal := inferInstance
  have hQc : Nat.card Q = 4 := by
    rw [Nat.card_congr (Subgroup.prodEquiv _ _).toEquiv, Nat.card_prod,
      Subgroup.card_bot, mul_one]
    exact kleinFour_card_of_card_eq_four (by simp)
  have hQ : Q ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hQc
    contradiction
  have hpQ : IsPGroup 2 Q := IsPGroup.of_card (n := 2) hQc
  let f := sumEmbedding 4 6
  have hf := sumEmbedding_injective 4 6
  let R := Q.map f
  have hR : R ≠ ⊥ := fun h => hQ ((Q.map_eq_bot_iff_of_injective hf).mp h)
  let M := Subgroup.normalizer (R : Set (alternatingGroup (Fin 10)))
  have hm (x) : f x ∈ M := by
    apply Subgroup.le_normalizer_map f
    exact ⟨x, by rw [Q.normalizer_eq_top]; trivial, rfl⟩
  exact ⟨M, ⟨R, hR, hpQ.map f, rfl⟩, f.codRestrict M hm,
    fun a b h => hf (congrArg Subtype.val h)⟩

/-- The A₄ × A₆ subgroup witnesses the local 3-rank obstruction in A₁₀. -/
theorem three_le_ten_twoLocalPrimeRank :
    3 ≤ twoLocalPrimeRank 3 (alternatingGroup (Fin 10)) := by
  obtain ⟨M, hM, f, hf⟩ := ten_contains_four_prod_six_twoLocal
  exact four_prod_six_primeRank.symm.trans_le
    ((Theory.GroupTheory.primeRank_le_of_injective 3 f hf).trans (hM.primeRank_le 3))

/-- A₁₀ violates the defining bound on odd-prime ranks of two-locals. -/
theorem not_quasithin_ten : ¬ IsQuasithin (alternatingGroup (Fin 10)) := by
  intro h
  have hb := isQuasithin_iff_twoLocalPrimeRank.mp h 3 (by decide) (by decide)
  have hg := three_le_ten_twoLocalPrimeRank
  omega

/-- A quasithin alternating group has degree at most nine. -/
theorem degree_le_nine_of_quasithin {n : ℕ}
    (h : IsQuasithin (alternatingGroup (Fin n))) : n ≤ 9 := by
  by_contra hn
  have hn : 10 ≤ n := by omega
  let f := degreeEmbedding hn
  have hr := h.subgroup f.range
  exact not_quasithin_ten (Theory.GroupTheory.isQuasithin_of_equiv
    (MonoidHom.ofInjective (degreeEmbedding_injective hn)).symm hr)

end alternatingGroup

