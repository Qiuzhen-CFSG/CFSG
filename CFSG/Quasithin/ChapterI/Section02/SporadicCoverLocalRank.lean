module

public import Theory.Quasithin.CentralThreeLocalRank

/-!
# Local rank in sporadic three-covers: the lifting step

For a nontrivial three-group center, an elementary group of order nine
that embeds modulo the center and normalizes a nontrivial two-subgroup
produces rank at least three in that two-subgroup's normalizer. This module
specializes the central-product construction to the concrete E₉ carrier.

Source: Aschbacher--Smith, Lemma A.2.19, printed p. 41 (PDF p. 52), and the
argument of I.2.1, printed p. 409. The latter's statement only bounds ordinary
rank. Its use of A.1.31 does not itself put the resulting rank-three subgroup
in a two-local. In particular its J₃ centralizer-splitting clause must not be
silently promoted to the required two-local witness.

The results below are conditional tools, not the three sporadic cases of
A.2.19. Those cases still require concrete E₉ lifts and nontrivial two-subgroups
for covers whose central quotients are the actual O'Nan, J₃ and McL models.
The hypothesis that the center is nontrivial is essential.
-/

public section
namespace CFSG.Quasithin.ChapterI

private theorem e9_cube (a : Multiplicative (ZMod 3 × ZMod 3)) : a ^ 3 = 1 := by
  change (3 • a.toAdd) = 0
  apply Prod.ext
  · change 3 • a.toAdd.1 = (0 : ZMod 3)
    simp only [nsmul_eq_mul]
    exact zero_mul _
  · change 3 • a.toAdd.2 = (0 : ZMod 3)
    simp only [nsmul_eq_mul]
    exact zero_mul _

private theorem e9_card : Nat.card (Multiplicative (ZMod 3 × ZMod 3)) = 3 ^ 2 := by
  rw [Nat.card_congr Multiplicative.toAdd, Nat.card_prod]
  norm_num [Nat.card_zmod]

/-- A concrete E₉ lift supplies both the explicit local witness and the bound.
Existence of the input lift is not asserted here. -/
theorem sporadicCover_localRank_of_e9_lift
    {G : Type*} [Group G] [Finite G]
    (hZ : IsPGroup 3 (Subgroup.center G)) (hZne : Subgroup.center G ≠ ⊥)
    (Q : Subgroup G) (hQ : IsPGroup 2 Q) (hQne : Q ≠ ⊥)
    (f : Multiplicative (ZMod 3 × ZMod 3) →* G)
    (hf : Function.Injective ((QuotientGroup.mk' (Subgroup.center G)).comp f))
    (hn : ∀ a, f a ∈ Subgroup.normalizer (Q : Set G)) :
    3 ≤ primeRank 3 (Subgroup.normalizer (Q : Set G)) ∧
      3 ≤ twoLocalPrimeRank 3 G := by
  have hr := Theory.Quasithin.three_le_primeRank_normalizer_of_injective_central_projection
    hZ hZne Q f hf hn e9_cube e9_card
  exact ⟨hr, hr.trans ((show IsTwoLocal (Subgroup.normalizer (Q : Set G)) from
    ⟨Q, hQne, hQ, rfl⟩).primeRank_le 3)⟩

/-- The same concrete lift excludes quasithinness. -/
theorem sporadicCover_not_quasithin_of_e9_lift
    {G : Type*} [Group G] [Finite G]
    (hZ : IsPGroup 3 (Subgroup.center G)) (hZne : Subgroup.center G ≠ ⊥)
    (Q : Subgroup G) (hQ : IsPGroup 2 Q) (hQne : Q ≠ ⊥)
    (f : Multiplicative (ZMod 3 × ZMod 3) →* G)
    (hf : Function.Injective ((QuotientGroup.mk' (Subgroup.center G)).comp f))
    (hn : ∀ a, f a ∈ Subgroup.normalizer (Q : Set G)) : ¬ IsQuasithin G := by
  intro h
  have hle := isQuasithin_iff_twoLocalPrimeRank.mp h 3 (by decide) (by decide)
  have hge := (sporadicCover_localRank_of_e9_lift hZ hZne Q hQ hQne f hf hn).2
  omega

end CFSG.Quasithin.ChapterI
