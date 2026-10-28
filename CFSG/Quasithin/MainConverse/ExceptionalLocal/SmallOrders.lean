module

public import CFSG.Quasithin.Defs
public import CFSG.Quasithin.ClassificationModels.Families
public import Theory.GroupTheory.PrimeRankCubeFree
public import Theory.AtlasPort.LinearGroups.G2.Order
public import Theory.SpecificGroups.Tits.FiniteSimple

/-!
# Small exceptional models: all odd primes except three

The checked orders of G₂(3), full G₂(2), and the Tits presentation divide
2¹¹ · 3⁶ · 5² · 7 · 13. Away from three this integer has no odd prime cube,
so the prime-rank order bound gives rank at most two in each actual model.
For G₂(2)′, Lagrange's theorem applies to the actual commutator subgroup;
no exceptional isomorphism or unproved derived-group order is needed.

Consequently QT for these three models reduces to the 3-ranks of their
maximal 2-local subgroups. The final three theorems are conditional reductions:
their local 3-rank premises still require concrete normalizer calculations.
They do not assert QT or even characteristic unconditionally.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
1 March 2004 manuscript, Theorem 0.1.2(1,4), printed p.4, repeated on p.482.
The imported order proofs use the split-octonion automorphism construction and
the certified isomorphism from Parrott's presentation to its ATLAS image.
-/

namespace CFSG.Quasithin.MainConverse.ExceptionalLocal

private theorem odd_cube_not_dvd_bound {p : ℕ} (hp : p.Prime)
    (ho : Odd p) (hp3 : p ≠ 3) : ¬ p ^ 3 ∣ 3396556800 := by
  intro hd
  have hpd : p ∣ 2 ^ 11 * 3 ^ 6 * 5 ^ 2 * 7 * 13 := by
    norm_num
    exact (dvd_pow_self p (by decide : 3 ≠ 0)).trans hd
  have hprimes : p = 2 ∨ p = 3 ∨ p = 5 ∨ p = 7 ∨ p = 13 := by
    simpa only [hp.dvd_mul,
      hp.prime.dvd_pow_iff_dvd (by decide : 11 ≠ 0),
      hp.prime.dvd_pow_iff_dvd (by decide : 6 ≠ 0),
      hp.prime.dvd_pow_iff_dvd (by decide : 2 ≠ 0),
      Nat.prime_dvd_prime_iff_eq hp Nat.prime_two,
      Nat.prime_dvd_prime_iff_eq hp Nat.prime_three,
      Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 5),
      Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 7),
      Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 13), or_assoc] using hpd
  rcases hprimes with rfl | rfl | rfl | rfl | rfl
  · exact ho.not_two_dvd_nat (dvd_refl 2)
  · exact hp3 rfl
  all_goals norm_num at hd

private theorem odd_primeRank_le_two_of_card_dvd_bound
    {G : Type*} [Group G] [Finite G] (hc : Nat.card G ∣ 3396556800)
    {p : ℕ} (hp : p.Prime) (ho : Odd p) (hp3 : p ≠ 3) : primeRank p G ≤ 2 := by
  let : Fact p.Prime := ⟨hp⟩
  exact primeRank_le_two_of_cube_not_dvd (fun hd => odd_cube_not_dvd_bound hp ho hp3
    (hd.trans hc))

/-- Every odd prime other than three has rank at most two in G₂(3). -/
public theorem g2_three_odd_primeRank_le_two {G : Type*} [Group G] [Finite G]
    (hG : ClassificationModels.IsG2At G 3) {p : ℕ}
    (hp : p.Prime) (ho : Odd p) (hp3 : p ≠ 3) : primeRank p G ≤ 2 := by
  obtain ⟨F, hF, hfin, hq, ⟨e⟩⟩ := hG
  apply odd_primeRank_le_two_of_card_dvd_bound (p := p) _ hp ho hp3
  rw [Nat.card_congr e.toEquiv, Atlas.G2.card_Model, hq]
  norm_num

/-- The actual commutator of G₂(2) has the same rank bound away from three. -/
public theorem g2_binary_derived_odd_primeRank_le_two {G : Type*} [Group G] [Finite G]
    (e : G ≃* commutator (Atlas.G2.Model (ZMod 2))) {p : ℕ}
    (hp : p.Prime) (ho : Odd p) (hp3 : p ≠ 3) : primeRank p G ≤ 2 := by
  apply odd_primeRank_le_two_of_card_dvd_bound (p := p) _ hp ho hp3
  rw [Nat.card_congr e.toEquiv]
  apply (commutator (Atlas.G2.Model (ZMod 2))).card_subgroup_dvd_card.trans
  rw [Atlas.G2.card_Model, Nat.card_zmod]
  norm_num

/-- The bound applies to Parrott's presented Tits group and its isomorphic copies. -/
public theorem tits_odd_primeRank_le_two {G : Type*} [Group G] [Finite G]
    (e : G ≃* Tits.ParrottGroup) {p : ℕ}
    (hp : p.Prime) (ho : Odd p) (hp3 : p ≠ 3) : primeRank p G ≤ 2 := by
  apply odd_primeRank_le_two_of_card_dvd_bound (p := p) _ hp ho hp3
  rw [Nat.card_congr e.toEquiv, Tits.parrottGroup_card]
  norm_num

private theorem quasithin_of_three_local_rank
    {G : Type*} [Group G] [Finite G]
    (haway : ∀ p : ℕ, p.Prime → Odd p → p ≠ 3 → primeRank p G ≤ 2)
    (hthree : ∀ M : Subgroup G, IsMaximalTwoLocal M → primeRank 3 M ≤ 2) :
    IsQuasithin G := by
  apply Theory.GroupTheory.isQuasithin_iff_maximalTwoLocal.mpr
  intro M hM p hp ho
  by_cases h : p = 3
  · subst p
    exact hthree M hM
  · exact (Theory.GroupTheory.primeRank_le_of_injective p M.subtype
      M.subtype_injective).trans (haway p hp ho h)

/-- Conditional QT reduction for G₂(3); the local 3-rank bound remains an input. -/
public theorem g2_three_quasithin_of_three_local_rank
    {G : Type*} [Group G] [Finite G] (hG : ClassificationModels.IsG2At G 3)
    (hthree : ∀ M : Subgroup G, IsMaximalTwoLocal M → primeRank 3 M ≤ 2) :
    IsQuasithin G :=
  quasithin_of_three_local_rank (fun _ => g2_three_odd_primeRank_le_two hG) hthree

/-- Conditional QT reduction for the actual derived binary G₂ carrier. -/
public theorem g2_binary_derived_quasithin_of_three_local_rank
    {G : Type*} [Group G] [Finite G]
    (e : G ≃* commutator (Atlas.G2.Model (ZMod 2)))
    (hthree : ∀ M : Subgroup G, IsMaximalTwoLocal M → primeRank 3 M ≤ 2) :
    IsQuasithin G :=
  quasithin_of_three_local_rank (fun _ => g2_binary_derived_odd_primeRank_le_two e) hthree

/-- Conditional QT reduction for the Tits group, using its certified order. -/
public theorem tits_quasithin_of_three_local_rank
    {G : Type*} [Group G] [Finite G] (e : G ≃* Tits.ParrottGroup)
    (hthree : ∀ M : Subgroup G, IsMaximalTwoLocal M → primeRank 3 M ≤ 2) :
    IsQuasithin G :=
  quasithin_of_three_local_rank (fun _ => tits_odd_primeRank_le_two e) hthree

end CFSG.Quasithin.MainConverse.ExceptionalLocal
