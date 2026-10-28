module

public import Theory.SpecificGroups.Tits.ThreeSylowContainment.Checked
public import Theory.SpecificGroups.Tits.OuterOddSubgroups.OverlapCentralizers.FirstCover
public import Mathlib.Dynamics.PeriodicPts.Lemmas

/-!
# Interpreting the Tits point-orbit witnesses

The packed point maps are the original Parrott permutations. A point returned
after a prime number of iterations, but moved after one, has that minimal
period. The order of any subgroup containing the permutation is therefore
divisible by this prime. Thus a subgroup with only primes two and three cannot
contain a representative with one of the certified five- or thirteen-cycles.
The remaining words use only the second-parabolic generators.

Source: Parrott (1972), p.683; the finite witness data and its checks are in
`Data` and `Checked`. No solvability or parabolic-core assertion is used.
-/

namespace Tits.ThreeSylowContainment.Certificate
open Theory.GroupTheory.CosetEnumeration OuterOddSubgroups.OverlapCentralizers

private theorem packed_code (a : ParrottGenerator) :
    Packed.perm (code a) = Atlas1600ParrottData.permutation a := by
  cases a <;> simp [Packed.perm_eq, Packed.generator, code, Atlas1600ParrottData.permutation]

private theorem generator_fourth (a : ParrottGenerator) :
    Atlas1600ParrottData.permutation a ^ 4 = 1 := by
  cases a
  case r1 =>
    have h : Atlas1600ParrottData.permutation .r1 ^ 2 = 1 := by
      simpa only [parrottRelator, map_pow, FreeGroup.lift_apply_of]
        using Atlas1600ParrottData.relations .i_r1
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, h, one_pow]
  case r8 =>
    have h : Atlas1600ParrottData.permutation .r8 ^ 2 = 1 := by
      simpa only [parrottRelator, map_pow, FreeGroup.lift_apply_of]
        using Atlas1600ParrottData.relations .i_r8
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, h, one_pow]
  case s1 =>
    have h : Atlas1600ParrottData.permutation .s1 ^ 2 = 1 := by
      simpa only [parrottRelator, map_pow, FreeGroup.lift_apply_of]
        using Atlas1600ParrottData.relations .i_s1
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, h, one_pow]
  case s2 =>
    have h : Atlas1600ParrottData.permutation .s2 ^ 2 = 1 := by
      simpa only [parrottRelator, map_pow, FreeGroup.lift_apply_of]
        using Atlas1600ParrottData.relations .i_s2
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, h, one_pow]
  case s3 =>
    simpa only [parrottRelator, map_pow, FreeGroup.lift_apply_of]
      using Atlas1600ParrottData.relations .i_s3
  case s4 =>
    have h : Atlas1600ParrottData.permutation .s4 ^ 2 = 1 := by
      simpa only [parrottRelator, map_pow, FreeGroup.lift_apply_of]
        using Atlas1600ParrottData.relations .i_s4
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, h, one_pow]
  case s5 =>
    simpa only [parrottRelator, map_pow, FreeGroup.lift_apply_of]
      using Atlas1600ParrottData.relations .i_s5
  case s6 =>
    have h : Atlas1600ParrottData.permutation .s6 ^ 2 = 1 := by
      simpa only [parrottRelator, map_pow, FreeGroup.lift_apply_of]
        using Atlas1600ParrottData.relations .i_s6
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, h, one_pow]
  case s7 =>
    simpa only [parrottRelator, map_pow, FreeGroup.lift_apply_of]
      using Atlas1600ParrottData.relations .i_s7
  case s8 =>
    have h : Atlas1600ParrottData.permutation .s8 ^ 2 = 1 := by
      simpa only [parrottRelator, map_pow, FreeGroup.lift_apply_of]
        using Atlas1600ParrottData.relations .i_s8
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, h, one_pow]

private theorem fastEval_eq (w : Word ParrottGenerator) :
    fastEval w = eval Atlas1600ParrottData.permutation w := by
  unfold fastEval eval
  congr 1
  apply List.map_congr_left
  rintro ⟨a, b⟩ _
  cases b
  · simp only [Bool.false_eq_true, ↓reduceIte, letterValue, packed_code]
    apply eq_inv_of_mul_eq_one_left
    rw [← pow_succ]
    exact generator_fourth a
  · simp only [↓reduceIte, letterValue, packed_code]

private theorem mapped_eval (w : Word ParrottGenerator) :
    (eval atlas1600ParrottAssignment w).val = eval Atlas1600ParrottData.permutation w := by
  change atlas1600Subgroup.subtype (eval atlas1600ParrottAssignment w) = _
  simp only [eval, map_list_prod, List.map_map]
  congr 1
  apply List.map_congr_left
  rintro ⟨a, b⟩ _
  cases b
  · change (atlas1600ParrottAssignment a).val⁻¹ = _
    rw [atlas1600ParrottAssignment_val]
    rfl
  · exact atlas1600ParrottAssignment_val a

private theorem fastNormalForm_eq (n : Fin 2048) :
    fastNormalForm n = (atlas1600SylowTwoNormalForm n).val := by
  simp [fastNormalForm, Packed.perm_eq, Packed.generator, atlas1600SylowTwoNormalForm_val]

private theorem generator_mem_second (a : ParrottGenerator) (ha : a ≠ .r1) :
    atlas1600ParrottAssignment a ∈ ExceptionalParabolics.second := by
  by_cases h8 : a = .r8
  · subst a
    exact ExceptionalParabolics.reflection_mem_second
  · apply ExceptionalParabolics.sylow_le_second
    rw [ExceptionalParabolics.S, atlas1600SylowTwoSubgroup_eq]
    apply Subgroup.subset_closure
    cases a <;> simp_all

private theorem inSecond_sound (w : Word ParrottGenerator) (j : Fin 5)
    (h : inSecond w j = true) :
    firstRotation ^ j.val * eval atlas1600ParrottAssignment w ∈
      ExceptionalParabolics.second := by
  simp only [inSecond, Bool.and_eq_true, beq_iff_eq] at h
  rcases h with ⟨rfl, hw⟩
  simp only [Fin.val_zero, pow_zero, one_mul]
  apply Subgroup.list_prod_mem
  intro x hx
  obtain ⟨⟨a,b⟩, ha, rfl⟩ := List.mem_map.mp hx
  have ha1 : a ≠ .r1 := by simpa using List.all_eq_true.mp hw (a,b) ha
  have hm := generator_mem_second a ha1
  cases b <;> simp only [letterValue, Bool.false_eq_true, ↓reduceIte]
  · exact ExceptionalParabolics.second.inv_mem hm
  · exact hm

private theorem cycle_dvd (H : Subgroup Atlas1600Group) (x : H)
    (p : Fin 1600) (q : ℕ) (hq : q.Prime)
    (hper : (x.val.val ^ q) p = p) (hne : x.val.val p ≠ p) :
    q ∣ Nat.card H := by
  let : Fact q.Prime := ⟨hq⟩
  have hp : Function.IsPeriodicPt x.val.val q p := by
    change (x.val.val)^[q] p = p
    rw [← Equiv.Perm.coe_pow]
    exact hper
  have hperiod := Function.minimalPeriod_eq_prime hp hne
  have hcard : Function.IsPeriodicPt x.val.val (Nat.card H) p := by
    change (x.val.val)^[Nat.card H] p = p
    rw [← Equiv.Perm.coe_pow]
    have he := congrArg (fun y : H => y.val.val) (pow_card_eq_one' (x := x))
    change x.val.val ^ Nat.card H = 1 at he
    rw [he]
    rfl
  rw [← hperiod]
  exact hcard.minimalPeriod_dvd

private theorem test_sound (w : Word ParrottGenerator) (j : Fin 5) (c : ℕ)
    (h : test w j c = true) :
    firstRotation ^ j.val * eval atlas1600ParrottAssignment w ∈ ExceptionalParabolics.second ∨
      ∃ (n : Fin 2048) (p : Fin 1600) (q : ℕ),
        q.Prime ∧ q ≠ 2 ∧ q ≠ 3 ∧
        let x := firstRotation ^ j.val * eval atlas1600ParrottAssignment w *
          atlas1600SylowTwoNormalForm n
        (x.val ^ q) p = p ∧ x.val p ≠ p := by
  simp only [test, Bool.or_eq_true] at h
  rcases h with hsecond | hcycle
  · exact Or.inl (inSecond_sound w j hsecond)
  · right
    refine ⟨witnessSylow c, witnessPoint c, witnessPrime c, ?_, ?_, ?_, ?_⟩
    · unfold witnessPrime
      split <;> decide
    · unfold witnessPrime
      split <;> decide
    · unfold witnessPrime
      split <;> decide
    · have hv : firstRotation.val = Packed.perm 2 * Packed.perm 0 := by
        change (atlas1600ParrottAssignment .s1).val *
          (atlas1600ParrottAssignment .r1).val = _
        simp [Packed.perm_eq, Packed.generator, atlas1600ParrottAssignment_val,
          Atlas1600ParrottData.permutation]
      change (((firstRotation.val ^ j.val * (eval atlas1600ParrottAssignment w).val *
          (atlas1600SylowTwoNormalForm (witnessSylow c)).val) ^ witnessPrime c)
          (witnessPoint c) = witnessPoint c) ∧
        (firstRotation.val ^ j.val * (eval atlas1600ParrottAssignment w).val *
          (atlas1600SylowTwoNormalForm (witnessSylow c)).val) (witnessPoint c) ≠ witnessPoint c
      simpa only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne,
        hv, mapped_eval, ← fastEval_eq, ← fastNormalForm_eq] using hcycle

/-- In a two-and-three-prime Sylow overgroup, every admitted representative
lies in the second parabolic. -/
public theorem representative_mem_second (H : Subgroup Atlas1600Group)
    (hS : atlas1600SylowTwoSubgroup ≤ H)
    (hprimes : ∀ p : ℕ, p.Prime → p ∣ Nat.card H → p = 2 ∨ p = 3)
    (i : ℕ) (j : Fin 5)
    (ht : firstRotation ^ j.val *
      eval atlas1600ParrottAssignment (R1Certificate.input.reps.getD i []) ∈ H) :
    firstRotation ^ j.val *
      eval atlas1600ParrottAssignment (R1Certificate.input.reps.getD i []) ∈
        ExceptionalParabolics.second := by
  obtain ⟨c, hc⟩ := representative_test i j
  rcases test_sound _ j c hc with hs | ⟨n, p, q, hq, h2, h3, hp, hne⟩
  · exact hs
  · have hm := H.mul_mem ht (hS (atlas1600SylowTwoNormalForm_mem n))
    have hd := cycle_dvd H ⟨_, hm⟩ p q hq hp hne
    exact False.elim ((hprimes q hq hd).elim h2 h3)

end Tits.ThreeSylowContainment.Certificate
