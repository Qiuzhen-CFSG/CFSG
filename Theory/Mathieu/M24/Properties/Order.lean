module

public import Mathlib.Data.Set.Card
public import Mathlib.Algebra.Group.Subgroup.Actions
public import Mathlib.Tactic.NormNum
public import Theory.Mathieu.M23.Properties.PointStabilizer
public import Theory.Mathieu.M23.Properties.Order

/-!
# Exact order of M24 from its M23 point stabilizer

The natural M24 action is transitive because its point-24 stabilizer is M23,
which is transitive on the other twenty-three points, while the first standard
generator moves point 24 into that complement.  Orbit--stabilizer then gives
the order of M24 directly from the established order of M23.
-/

set_option maxHeartbeats 800000
set_option maxRecDepth 100000

namespace Sporadic.Mathieu

/-- Every point of the natural M24 action is reachable from Atlas point 24. -/
private theorem m24_reaches_from_twentyFour (y : Fin 24) :
    ∃ g : M24, g • (24 : Fin 24) = y := by
  by_cases hy : y = (24 : Fin 24)
  · subst y
    exact ⟨1, one_smul M24 (24 : Fin 24)⟩
  · obtain ⟨i, hi⟩ := m23PointEquiv.surjective
      (⟨20, by decide +kernel⟩ : {x : Fin 24 // x ≠ (24 : Fin 24)})
    obtain ⟨j, hj⟩ := m23PointEquiv.surjective
      (⟨y, hy⟩ : {x : Fin 24 // x ≠ (24 : Fin 24)})
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq M23 i j
    refine ⟨⟨m23ExtendHom g * m24GeneratorA,
      M24.mul_mem (m23Extend_mem_M24 g) m24GeneratorA_mem⟩, ?_⟩
    change (m23ExtendHom g * m24GeneratorA) (24 : Fin 24) = y
    rw [Equiv.Perm.mul_apply]
    have hA : m24GeneratorA (24 : Fin 24) = (20 : Fin 24) := by decide +kernel
    rw [hA]
    have hi20 : m23PointEmbedding i = (20 : Fin 24) := congrArg Subtype.val hi
    have hjy : m23PointEmbedding j = y := congrArg Subtype.val hj
    rw [← hi20, m23ExtendHom_apply_embedded]
    change ((g : Equiv.Perm (Fin 23)) i) = j at hg
    rw [hg, hjy]

/-- The natural M24 action on its twenty-four points is transitive. -/
public noncomputable instance : MulAction.IsPretransitive M24 (Fin 24) where
  exists_smul_eq := by
    intro x y
    obtain ⟨gx, hgx⟩ := m24_reaches_from_twentyFour x
    obtain ⟨gy, hgy⟩ := m24_reaches_from_twentyFour y
    refine ⟨gy * gx⁻¹, ?_⟩
    calc
      (gy * gx⁻¹) • x = (gy * gx⁻¹) • (gx • (24 : Fin 24)) := by rw [hgx]
      _ = gy • (24 : Fin 24) := by simp [mul_smul]
      _ = y := hgy

/-- The point-24 stabilizer has the established order of M23. -/
private theorem m24PointStabilizerTwentyFour_card :
    Nat.card (MulAction.stabilizer M24 (24 : Fin 24)) = 10200960 := by
  calc
    Nat.card (MulAction.stabilizer M24 (24 : Fin 24)) = Nat.card M23 :=
      (Nat.card_congr m23EquivM24PointStabilizer).symm
    _ = 10200960 := m23_order

/-- The full automorphism group of the Witt design S(5,8,24) has order 244823040. -/
public theorem m24_order : Nat.card M24 = 244823040 := by
  have hmul := Subgroup.card_mul_index
    (MulAction.stabilizer M24 (24 : Fin 24))
  rw [m24PointStabilizerTwentyFour_card,
    MulAction.index_stabilizer_of_transitive M24 (24 : Fin 24),
    Nat.card_fin] at hmul
  omega

/-- Prime-power factorization of the order of `M24`. -/
public theorem m24_order_factorization :
    Nat.card M24 = 2 ^ 10 * 3 ^ 3 * 5 * 7 * 11 * 23 := by
  rw [m24_order]
  norm_num

/-- The prime divisors of the order of `M24` are exactly `2`, `3`, `5`, `7`, `11`, and `23`. -/
public theorem m24_prime_dvd_order_iff (p : ℕ) [Fact (Nat.Prime p)] :
    p ∣ Nat.card M24 ↔
      p = 2 ∨ p = 3 ∨ p = 5 ∨ p = 7 ∨ p = 11 ∨ p = 23 := by
  rw [m24_order,
    show 244823040 =
      2 * 2 * 2 * 2 * 2 * 2 * 2 * 2 * 2 * 2 * 3 * 3 * 3 * 5 * 7 * 11 * 23 by
      norm_num]
  have hp : Nat.Prime p := Fact.out
  simp only [hp.dvd_mul,
    Nat.prime_dvd_prime_iff_eq hp (by decide +kernel : Nat.Prime 2),
    Nat.prime_dvd_prime_iff_eq hp (by decide +kernel : Nat.Prime 3),
    Nat.prime_dvd_prime_iff_eq hp (by decide +kernel : Nat.Prime 5),
    Nat.prime_dvd_prime_iff_eq hp (by decide +kernel : Nat.Prime 7),
    Nat.prime_dvd_prime_iff_eq hp (by decide +kernel : Nat.Prime 11),
    Nat.prime_dvd_prime_iff_eq hp (by decide +kernel : Nat.Prime 23)]
  aesop

/-- The prime spectrum of `M24`. -/
public theorem m24_prime_spectrum :
    Nat.primeFactors (Nat.card M24) = {2, 3, 5, 7, 11, 23} := by
  ext p
  rw [Nat.mem_primeFactors]
  simp only [Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨hp, hdiv, _⟩
    let : Fact (Nat.Prime p) := ⟨hp⟩
    exact (m24_prime_dvd_order_iff p).mp hdiv
  · intro h
    rw [m24_order]
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact ⟨by decide +kernel, by norm_num, by norm_num⟩

end Sporadic.Mathieu
