module

public import Theory.Character.ModularBlock.PrimeChange
public import Theory.Character.ModularBlock.PrimeIntersection
public import Theory.Character.ModularBlock.PrimePowerDegree
public import Theory.Character.Cyclotomic
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.NormNum

/-!
# The seven-row Brauer--Tuan intersection calculation

In a block with degrees `1, 27, 12, 16, 16, 16, 16`, an intersecting block
whose degrees are divisible by three contains only the degree-27 and possibly
the degree-12 row. If their values at the chosen element are `1` and `-1`,
the degree-weighted intersection sum is `27` or `15`. Divisibility by `27`
in the algebraic integers excludes `15`; divisibility by `81` then fails.

The final theorem applies degree divisibility (Brauer--Tuan Lemma 2) to the
three-block of the degree-27 row, and integral quotients of the intersection
sum (Lemma 3) to this block and the given principal thirteen-block. It accepts
the seven-row witness explicitly, independently of cyclic-block construction.

Source: Brauer--Tuan, *On simple groups of finite order I*, Bull. AMS 51
(1945), Lemmas 2--3, pp.761--765, DOI 10.1090/S0002-9904-1945-08441-9.
-/

public section
noncomputable section
open scoped BigOperators
namespace BrauerTuan
open ModularBlock.PrimeBlockConstruction
variable {G : Type*} [Group G] [Finite G]

/-- The degree-weighted sum over the intersection with the given principal block. -/
@[expose] def intersectionSum (d : PrimeCongruenceBlockData 13 G)
    (B : Finset d.I) (u : G) : ℂ :=
  ∑ i ∈ d.block ∩ B, d.chi i (ConjClasses.mk 1) * d.chi i (ConjClasses.mk u)

/-- Only the two degrees divisible by three can contribute to the intersection. -/
theorem intersectionSum_eq
    (d : PrimeCongruenceBlockData 13 G)
    (row : Fin 7 ≃ {i : d.I // i ∈ d.block})
    (hdegree : ∀ i, d.chi (row i).val (ConjClasses.mk 1) =
      (![1, 27, 12, 16, 16, 16, 16] : Fin 7 → ℂ) i)
    (B : Finset d.I) (hmem : (row 1).val ∈ B)
    (hB : ∀ i ∈ B, ∃ n : ℕ, d.chi i (ConjClasses.mk 1) = (n : ℂ) ∧ 3 ∣ n)
    (u : G) (hvalue₁ : d.chi (row 1).val (ConjClasses.mk u) = 1)
    (hvalue₂ : d.chi (row 2).val (ConjClasses.mk u) = -1) :
    intersectionSum d B u = if (row 2).val ∈ B then 15 else 27 := by
  classical
  have hrows : ∀ j : Fin 7, (row j).val ∈ B → j = 1 ∨ j = 2 := by
    intro j hj
    obtain ⟨n, hn, hdiv⟩ := hB _ hj
    have heq := (hdegree j).symm.trans hn
    fin_cases j <;> norm_num [Fin.ext_iff] at heq ⊢
    all_goals
      have hn' : n = 1 ∨ n = 16 := by
        first
        | exact Or.inl (by exact_mod_cast heq.symm)
        | exact Or.inr (by exact_mod_cast heq.symm)
      rcases hn' with rfl | rfl <;> norm_num at hdiv
  have hexcluded (j : Fin 7) (h₁ : j ≠ 1) (h₂ : j ≠ 2) : (row j).val ∉ B := by
    intro hj
    exact (hrows j hj).elim h₁ h₂
  have hsum : intersectionSum d B u =
      ∑ j : Fin 7, if (row j).val ∈ B then
        d.chi (row j).val (ConjClasses.mk 1) * d.chi (row j).val (ConjClasses.mk u)
        else 0 := by
    rw [intersectionSum, show d.block ∩ B = d.block.filter (· ∈ B) from by ext; simp,
      Finset.sum_filter]
    rw [← Finset.sum_attach]
    exact (Equiv.sum_comp row _).symm
  rw [hsum]
  simp only [Fin.sum_univ_succ]
  simp only [Fin.succ_zero_eq_one]
  simp [hexcluded, hmem, hdegree, hvalue₁, hvalue₂]
  split_ifs <;> norm_num

/-- The known factor `27` in the group order rules out the intersection sum `15`. -/
theorem intersectionSum_eq_twentySeven
    (d : PrimeCongruenceBlockData 13 G)
    (row : Fin 7 ≃ {i : d.I // i ∈ d.block})
    (hdegree : ∀ i, d.chi (row i).val (ConjClasses.mk 1) =
      (![1, 27, 12, 16, 16, 16, 16] : Fin 7 → ℂ) i)
    (B : Finset d.I) (hmem : (row 1).val ∈ B)
    (hB : ∀ i ∈ B, ∃ n : ℕ, d.chi i (ConjClasses.mk 1) = (n : ℂ) ∧ 3 ∣ n)
    (u : G) (hvalue₁ : d.chi (row 1).val (ConjClasses.mk u) = 1)
    (hvalue₂ : d.chi (row 2).val (ConjClasses.mk u) = -1)
    (hintegral : IsIntegral ℤ (intersectionSum d B u / 27)) :
    intersectionSum d B u = 27 := by
  rw [intersectionSum_eq d row hdegree B hmem hB u hvalue₁ hvalue₂] at hintegral ⊢
  split_ifs at hintegral ⊢ with h
  · have hdiv := integer_division_of_integral_quotient
      (a := 15) (b := 27) (by norm_num) (by simpa using hintegral)
    norm_num at hdiv
  · rfl

/-- Assembly of the three-part bound from degree divisibility and Lemma 3's
integral quotients. The block-theoretic premises are explicit. -/
theorem not_eightyOne_dvd_of_intersection
    (d : PrimeCongruenceBlockData 13 G)
    (row : Fin 7 ≃ {i : d.I // i ∈ d.block})
    (hdegree : ∀ i, d.chi (row i).val (ConjClasses.mk 1) =
      (![1, 27, 12, 16, 16, 16, 16] : Fin 7 → ℂ) i)
    (B : Finset d.I) (hmem : (row 1).val ∈ B)
    (hB : ∀ i ∈ B, ∃ n : ℕ, d.chi i (ConjClasses.mk 1) = (n : ℂ) ∧ 3 ∣ n)
    (u : G) (hvalue₁ : d.chi (row 1).val (ConjClasses.mk u) = 1)
    (hvalue₂ : d.chi (row 2).val (ConjClasses.mk u) = -1)
    (h27 : 27 ∣ Nat.card G)
    (hintegral : ∀ b : ℕ, 3 ^ b ∣ Nat.card G →
      IsIntegral ℤ (intersectionSum d B u / (3 ^ b : ℕ))) :
    ¬ 81 ∣ Nat.card G := by
  have hs := intersectionSum_eq_twentySeven d row hdegree B hmem hB u hvalue₁ hvalue₂
    (by simpa using hintegral 3 (by simpa using h27))
  intro h81
  have hi := hintegral 4 (by simpa using h81)
  rw [hs] at hi
  have hdiv := integer_division_of_integral_quotient
    (a := 27) (b := 81) (by norm_num) (by simpa using hi)
  norm_num at hdiv

/-- The seven-row principal thirteen-block forces the three-part of the group
order to be exactly `27`, given that `27` divides it and no element has order
`39`. The row witness and the two values are supplied explicitly. -/
theorem not_eightyOne_dvd_of_thirteen_block [IsSimpleGroup G]
    (d : PrimeCongruenceBlockData 13 G)
    (row : Fin 7 ≃ {i : d.I // i ∈ d.block})
    (hdegree : ∀ i, d.chi (row i).val (ConjClasses.mk 1) =
      (![1, 27, 12, 16, 16, 16, 16] : Fin 7 → ℂ) i)
    (h27 : 27 ∣ Nat.card G) (hno : ∀ x : G, orderOf x ≠ 39)
    (u : G) (hu : orderOf u = 13)
    (hvalue₁ : d.chi (row 1).val (ConjClasses.mk u) = 1)
    (hvalue₂ : d.chi (row 2).val (ConjClasses.mk u) = -1) :
    ¬ 81 ∣ Nat.card G := by
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  let : Fact (Nat.Prime 13) := ⟨by decide⟩
  let e := d.atPrime 3
  have hB := e.degree_dvd_of_prime_power_degree (row 1).val 3 (by norm_num)
    (by simpa [e] using hdegree 1)
  apply not_eightyOne_dvd_of_intersection d row hdegree
    (e.blockOf (row 1).val) (e.self_mem_blockOf _) hB u hvalue₁ hvalue₂ h27
  intro b hb
  exact isIntegral_block_intersection_sum_div_prime_pow (by norm_num : 13 ≠ 3)
    d d.principal (row 1).val (by simpa using hno) u (by simp [hu]) b hb

end BrauerTuan
