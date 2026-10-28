module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Order.CosetDistribution.Normalizer.Sylow
public import Theory.GroupTheory.CharacteristicCentralizerFusion
public import Mathlib.GroupTheory.FixedPointFree

/-!
# The contrary seven-centralizer in Bender (4.3)

The centralizer of an order-seven subgroup has no prime divisor 2, 3,
or 5: an element of one of those orders would have a centralizer whose
order is divisible by seven, contrary to the involution and odd-prime
local data. A proper enlargement of the seven-subgroup therefore has
order at least 49. Every involution normalizing the seven-subgroup acts
without nonidentity fixed points on its centralizer, hence by inversion.

The final two records specify the remaining local structure and actual
coset counts in `N_G(C_G(S))`. They are intermediate contracts, not
assertions of existence or proofs of (4.3).

Source: H. Bender, *Finite groups with large subgroups*, Illinois J. Math.
18 (1974), (4.3), printed p.226.
-/

open Subgroup
namespace CFSG.Quasithin.Janko1CentralizerData
variable {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (h : Janko1CentralizerData G) {d : ℕ} (localData : BenderPrimeData G d)

omit [Finite G] [IsSimpleGroup G] in
private theorem seven_le_centralizer (S : Subgroup G) (hS : Nat.card S = 7) :
    S ≤ centralizer (S : Set G) := by
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  let : IsCyclic S := isCyclic_of_prime_card hS
  exact Subgroup.le_centralizer S

include h localData

/-- No small prime divides the centralizer of an order-seven subgroup. -/
public theorem seven_centralizer_small_primes (S : Subgroup G) (hS : Nat.card S = 7) :
    ¬ 2 ∣ Nat.card (centralizer (S : Set G)) ∧
    ¬ 3 ∣ Nat.card (centralizer (S : Set G)) ∧
    ¬ 5 ∣ Nat.card (centralizer (S : Set G)) := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  let A := centralizer (S : Set G)
  have hd (x : A) : 7 ∣ Nat.card (centralizer ({(x : G)} : Set G)) := by
    rw [← hS]
    apply card_dvd_of_le
    intro s hs
    exact mem_centralizer_singleton_iff.mpr (x.property s hs)
  have no (p : ℕ) [Fact p.Prime]
      (hc : ∀ x : G, orderOf x = p → ¬ 7 ∣ Nat.card (centralizer ({x} : Set G))) :
      ¬ p ∣ Nat.card A := by
    intro hp
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := A) p hp
    exact hc x ((orderOf_injective A.subtype A.subtype_injective x).trans hx) (hd x)
  refine ⟨no 2 ?_, no 3 ?_, no 5 ?_⟩
  · intro x hx
    rw [h.involution_centralizer_card x hx]
    decide
  · intro x hx
    rw [localData.centralizer_three x hx]
    split_ifs <;> decide
  · intro x hx
    rw [localData.centralizer_five x hx]
    rcases localData.d_cases with hd | hd <;> rw [hd] <;> decide

/-- The seven-centralizer is coprime to every involution centralizer. -/
public theorem seven_centralizer_coprime (S : Subgroup G) (hS : Nat.card S = 7) :
    Nat.Coprime (Nat.card (centralizer (S : Set G))) 120 := by
  obtain ⟨h2, h3, h5⟩ := h.seven_centralizer_small_primes localData S hS
  have c2 := (Nat.prime_two.coprime_iff_not_dvd.mpr h2).symm
  have c3 := ((show Nat.Prime 3 by decide).coprime_iff_not_dvd.mpr h3).symm
  have c5 := ((show Nat.Prime 5 by decide).coprime_iff_not_dvd.mpr h5).symm
  exact (c2.pow_right 3).mul_right (c3.mul_right c5)

/-- The contrary case in (4.3) has centralizer order at least 49. -/
public theorem seven_centralizer_card_ge (S : Subgroup G) (hS : Nat.card S = 7)
    (hne : centralizer (S : Set G) ≠ S) :
    49 ≤ Nat.card (centralizer (S : Set G)) := by
  have hs := seven_le_centralizer S hS
  have hd : 7 ∣ Nat.card (centralizer (S : Set G)) := hS ▸ card_dvd_of_le hs
  have hgt : 7 < Nat.card (centralizer (S : Set G)) := by
    have hle := card_le_of_le hs
    have hnecard : Nat.card (centralizer (S : Set G)) ≠ 7 := by
      intro he
      exact hne (eq_of_le_of_card_ge hs (by omega)).symm
    omega
  obtain ⟨h2, h3, h5⟩ := h.seven_centralizer_small_primes localData S hS
  obtain ⟨k, hk⟩ := hd
  have hk7 : 7 ≤ k := by
    by_contra hn
    have hklt : k < 7 := by omega
    interval_cases k <;> omega
  omega

/-- Every involution in the seven-subgroup normalizer inverts its centralizer. -/
public theorem seven_centralizer_inverted (S : Subgroup G) (hS : Nat.card S = 7)
    (t : G) (ht : orderOf t = 2) (htN : t ∈ normalizer (S : Set G)) :
    (∀ x : G, x ∈ centralizer (S : Set G) → t * x * t⁻¹ = x⁻¹) ∧
      IsMulCommutative (centralizer (S : Set G)) := by
  let A := centralizer (S : Set G)
  let f : MulAut A := A.normalizerMonoidHom
    ⟨t, Subgroup.normalizer_le_normalizer_centralizer S htN⟩
  have hdisj : Disjoint A (centralizer ({t} : Set G)) := by
    apply disjoint_of_coprime_natCard
    rw [h.involution_centralizer_card t ht]
    exact h.seven_centralizer_coprime localData S hS
  have hfree : MonoidHom.FixedPointFree f := by
    intro x hx
    apply Subtype.ext
    apply hdisj.le_bot
    refine ⟨x.property, mem_centralizer_singleton_iff.mpr ?_⟩
    have he : t * (x : G) * t⁻¹ = x := congrArg Subtype.val hx
    exact (mul_inv_eq_iff_eq_mul.mp he).symm
  have hf2 : Function.Involutive f := by
    intro x
    apply Subtype.ext
    change t * (t * (x : G) * t⁻¹) * t⁻¹ = x
    have ht2 : t * t = 1 := by simpa only [pow_two] using (show t ^ 2 = 1 from ht ▸ pow_orderOf_eq_one t)
    calc
      _ = (t * t) * (x : G) * (t * t)⁻¹ := by group
      _ = x := by rw [ht2]; simp
  refine ⟨?_, ⟨⟨fun x y => (hfree.commute_all_of_involutive hf2 x y).eq⟩⟩⟩
  intro x hx
  exact congrArg Subtype.val (congrFun (hfree.coe_eq_inv_of_involutive hf2) ⟨x, hx⟩)

omit h localData in
/-- The actual local structure used to count in the normalizer of the
seven-centralizer. The complement is literally `N_G(C_G(S)) ∩ C_G(t)`;
no abstract group-family label replaces these embeddings. -/
public structure BenderSevenStructure (h : Janko1CentralizerData G) (S : Subgroup G) where
  t : G
  involution : orderOf t = 2
  normalizes : t ∈ normalizer (S : Set G)
  centralizers : ∀ x : G, x ∈ centralizer (S : Set G) → x ≠ 1 →
    centralizer ({x} : Set G) = centralizer (S : Set G)
  factorization : ∀ n : G,
    n ∈ normalizer (centralizer (S : Set G) : Set G) →
    ∃ a ∈ centralizer (S : Set G),
      ∃ c ∈ normalizer (centralizer (S : Set G) : Set G) ⊓ centralizer ({t} : Set G),
        n = a * c
  complement_card :
    Nat.card (normalizer (centralizer (S : Set G) : Set G) ⊓
      centralizer ({t} : Set G) : Subgroup G) = 6
  complement_cyclic : IsCyclic (normalizer (centralizer (S : Set G) : Set G) ⊓
    centralizer ({t} : Set G) : Subgroup G)
  three_in_sylow_normalizer : ∃ x : G,
    x ∈ normalizer (h.sylow : Set G) ∧
    x ∈ normalizer (centralizer (S : Set G) : Set G) ∧ orderOf x = 3

omit h localData in
/-- The literal counts in the contrary-case normalizer of (4.3).
Writing `a = |C_G(S)|`, the non-base fibers have sizes 0, 1, 2, 3, 6;
`b₂ = 12a`, `b₃ = 4a`, `b₆ = a`, and `b₁ ≥ 4a`.
The centralizer and all quotient fibers are actual subgroups and sets in G. -/
public structure BenderSevenCountData (S : Subgroup G) : Prop where
  normalizer_card : Nat.card (normalizer (centralizer (S : Set G) : Set G)) =
    6 * Nat.card (centralizer (S : Set G))
  base_fiber : Nat.card (BenderFiber (normalizer (centralizer (S : Set G) : Set G))
    (benderBaseCoset (normalizer (centralizer (S : Set G) : Set G)))) =
      Nat.card (centralizer (S : Set G))
  fiber_sizes : ∀ ω : G ⧸ normalizer (centralizer (S : Set G) : Set G),
    ω ≠ benderBaseCoset (normalizer (centralizer (S : Set G) : Set G)) →
    Nat.card (BenderFiber (normalizer (centralizer (S : Set G) : Set G)) ω) = 0 ∨
    Nat.card (BenderFiber (normalizer (centralizer (S : Set G) : Set G)) ω) = 1 ∨
    Nat.card (BenderFiber (normalizer (centralizer (S : Set G) : Set G)) ω) = 2 ∨
    Nat.card (BenderFiber (normalizer (centralizer (S : Set G) : Set G)) ω) = 3 ∨
    Nat.card (BenderFiber (normalizer (centralizer (S : Set G) : Set G)) ω) = 6
  single_lower : 4 * Nat.card (centralizer (S : Set G)) ≤
    benderCosetCount (normalizer (centralizer (S : Set G) : Set G)) 1
  double_cosets : benderCosetCount (normalizer (centralizer (S : Set G) : Set G)) 2 =
    12 * Nat.card (centralizer (S : Set G))
  triple_cosets : benderCosetCount (normalizer (centralizer (S : Set G) : Set G)) 3 =
    4 * Nat.card (centralizer (S : Set G))
  sextuple_cosets : benderCosetCount (normalizer (centralizer (S : Set G) : Set G)) 6 =
    Nat.card (centralizer (S : Set G))

end CFSG.Quasithin.Janko1CentralizerData

