module

public import Theory.AtlasPort.LinearGroups.G2.BinaryParabolicPair.ThreeSylowContainment.SolvableOrder
public import Theory.AtlasPort.LinearGroups.G2.DerivedEvenOrder
public import Theory.GroupTheory.NormalCoreIndexFactorial
public import Theory.GroupTheory.TwoThreeSolvable

/-!
# Reducing the binary derived Sylow-overgroup problem to index nine

The actual derived octonion group has order 6048, and its Sylow two-subgroups
have order 32. A proper overgroup has index dividing 189. Simplicity excludes
indices three and seven by the faithful coset action. For indices 27, 63 and
189, the normal core of its Sylow subgroup is nontrivial by the factorial
bound. At index 21 the overgroup has order 288: two-prime solvability and the
proved small-order Fitting argument give a nontrivial two-core.

Only index nine remains. Its exclusion is deliberately an explicit hypothesis
here; the numerical reduction does not assert a maximal-subgroup catalogue.
This isolates the small-derived case needed in Aschbacher--Smith, proof of
B.1.13, printed p.74 (PDF p.85), and GLS III, §2.6. The concrete carrier and
its order use the licensed ATLAS port; see LICENSES/ATLAS.txt.
-/

public section

namespace Atlas.G2.BinarySylowCoreReduction
open Subgroup

local notation "D" => commutator (Model (ZMod 2))

private theorem card_derived : Nat.card D = 6048 :=
  DerivedEvenOrder.card_derived_binary (by simp)

private theorem card_sylow (Q : Sylow 2 D) : Nat.card Q = 32 := by
  rw [Q.card_eq_multiplicity, card_derived]
  rw [show 6048 = 2 ^ 5 * 189 from rfl,
    Nat.factorization_mul (by decide) (by decide), Nat.factorization_pow]
  norm_num [Nat.prime_two.factorization,
    Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 2 ∣ 189)]

private theorem card_dvd_factorial {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (H : Subgroup G) (hH : H ≠ ⊤) : Nat.card G ∣ H.index.factorial := by
  have hb : H.normalCore = ⊥ := by
    rcases (inferInstance : H.normalCore.Normal).eq_bot_or_eq_top with h | h
    · exact h
    · exact False.elim (hH (top_unique (h ▸ H.normalCore_le)))
  have hd : H.normalCore.index ∣ H.index.factorial := by
    rw [normalCore_eq_ker, index_ker, index_eq_card, ← Nat.card_perm]
    exact card_subgroup_dvd_card (MulAction.toPermHom G (G ⧸ H)).range
  simpa only [hb, index_bot] using hd

private theorem core_of_small_sylow_index (Q : Sylow 2 D) (H : Subgroup D)
    (hQH : (Q : Subgroup D) ≤ H)
    (hc : Nat.card H = 32 ∨ Nat.card H = 96 ∨ Nat.card H = 224) :
    pCore 2 H ≠ ⊥ := by
  let P := Q.subtype hQH
  have hp : Nat.card P = 32 := by
    change Nat.card ((Q : Subgroup D).subgroupOf H) = 32
    rw [Nat.card_congr (subgroupOfEquivOfLe hQH).toEquiv]
    exact card_sylow Q
  apply Theory.GroupTheory.pCore_ne_bot_of_not_card_dvd_factorial_index
    (P : Subgroup H) P.isPGroup'
  have he := (P : Subgroup H).card_mul_index
  rw [hp] at he
  rcases hc with hc | hc | hc
  · have hi : (P : Subgroup H).index = 1 := by omega
    rw [hc, hi]; decide
  · have hi : (P : Subgroup H).index = 3 := by omega
    rw [hc, hi]; decide
  · have hi : (P : Subgroup H).index = 7 := by omega
    rw [hc, hi]; decide

private theorem core_of_card_288 (H : Subgroup D) (hc : Nat.card H = 288) :
    pCore 2 H ≠ ⊥ := by
  apply BinaryParabolicPair.ThreeSylowContainment.twoCore_ne_bot_of_card_288 H ?_ hc
  apply Theory.GroupTheory.isSolvable_of_prime_dvd_card_eq_two_or_three
  intro p hp hd
  rw [hc, show (288 : ℕ) = 2^5 * 3^2 from rfl] at hd
  rcases hp.dvd_mul.mp hd with h | h
  · exact Or.inl ((Nat.dvd_prime Nat.prime_two).mp (hp.dvd_of_dvd_pow h)
      |>.resolve_left hp.ne_one)
  · exact Or.inr ((Nat.dvd_prime Nat.prime_three).mp (hp.dvd_of_dvd_pow h)
      |>.resolve_left hp.ne_one)

private theorem divisors_189 (n : ℕ) (hn : n ∣ 189) :
    n ∈ [1, 3, 7, 9, 21, 27, 63, 189] := by
  have hbound := Nat.le_of_dvd (by decide : 0 < 189) hn
  exact (by decide +kernel : ∀ i : Fin 190, i.val ∣ 189 →
    i.val ∈ [1, 3, 7, 9, 21, 27, 63, 189]) ⟨n, by omega⟩ hn

/-- All proper Sylow overgroups except the possible index-nine case have
a nontrivial intrinsic two-core. -/
theorem twoCore_ne_bot_of_index_ne_nine [IsSimpleGroup D]
    (Q : Sylow 2 D) (H : Subgroup D) (hH : H ≠ ⊤)
    (hQH : (Q : Subgroup D) ≤ H) (h9 : H.index ≠ 9) :
    pCore 2 H ≠ ⊥ := by
  have h32 : 32 ∣ Nat.card H := by
    rw [← card_sylow Q]
    exact card_dvd_of_le hQH
  obtain ⟨k, hk⟩ := h32
  have he := H.card_mul_index
  rw [card_derived, hk] at he
  have hi189 : H.index ∣ 189 := by
    refine ⟨k, ?_⟩
    nlinarith
  have hi := divisors_189 H.index hi189
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  have hf := card_dvd_factorial H hH
  rw [card_derived] at hf
  have hproper := H.one_lt_index_of_ne_top hH
  rcases hi with hi | hi | hi | hi | hi | hi | hi | hi
  · omega
  · norm_num [hi] at hf
  · norm_num [hi] at hf
  · exact False.elim (h9 hi)
  · apply core_of_card_288 H
    have h := H.card_mul_index
    rw [hi, card_derived] at h
    omega
  · apply core_of_small_sylow_index Q H hQH
    right; right
    have h := H.card_mul_index
    rw [hi, card_derived] at h
    omega
  · apply core_of_small_sylow_index Q H hQH
    right; left
    have h := H.card_mul_index
    rw [hi, card_derived] at h
    omega
  · apply core_of_small_sylow_index Q H hQH
    left
    have h := H.card_mul_index
    rw [hi, card_derived] at h
    omega

/-- Any remaining counterexample must be an index-nine subgroup. -/
theorem index_eq_nine_of_twoCore_eq_bot [IsSimpleGroup D]
    (Q : Sylow 2 D) (H : Subgroup D) (hH : H ≠ ⊤)
    (hQH : (Q : Subgroup D) ≤ H) (hcore : pCore 2 H = ⊥) : H.index = 9 := by
  by_contra h9
  exact twoCore_ne_bot_of_index_ne_nine Q H hH hQH h9 hcore

end Atlas.G2.BinarySylowCoreReduction
