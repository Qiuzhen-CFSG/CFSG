module

public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.Construction

/-!
# Unique binary parameters in the D4 restricted range

A weight is its four integral simple-coroot coordinates. Taking parity and
dividing by two gives exactly one length-`n` binary word for each weight with
coordinates in `[0, 2^n)`. The recursive expression equals the usual weighted
sum. Fixing the length removes the ambiguity from terminal zero digits.

This is the arithmetic step of GLS3, Corollary 2.8.6(a), with the restricted
range of Definition 2.8.1(a), `refs/KGroup/GLS3/chapter2.tex`. It makes no
assertion about existence or irreducibility of representations.
-/

@[expose] public noncomputable section

open Theory.AlgebraicGroup.StandardRootSystem.D4RestrictedWeight
namespace Triality.RestrictedWeights.SteinbergTensors.AlgebraicTensor

/-- The integral highest-weight coordinates of a fixed-length binary word. -/
def wordWeight : (n : ℕ) → (Fin n → BasicWeight) → Weight
  | 0, _ => 0
  | n + 1, a => coefficient (a 0) + (2 : ℤ) • wordWeight n (fun i => a i.succ)

/-- The restricted range for ordinary characteristic-two Frobenius. -/
def InRestrictedRange (n : ℕ) (x : Weight) : Prop :=
  ∀ i, 0 ≤ x i ∧ x i < (2 : ℤ) ^ n

private theorem coefficient_bounds (a : BasicWeight) (i : Fin 4) :
    0 ≤ coefficient a i ∧ coefficient a i < 2 := by
  cases h : a i <;> simp [coefficient, h]

/-- Parity distinguishes the first binary digit from the remaining coordinates. -/
theorem prependWeight_injective {a b : BasicWeight} {x y : Weight}
    (h : coefficient a + (2 : ℤ) • x = coefficient b + (2 : ℤ) • y) : a = b ∧ x = y := by
  have hab : a = b := by
    apply coefficient_injective
    funext i
    have hi := congrFun h i
    have ha := coefficient_bounds a i
    have hb := coefficient_bounds b i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hi
    omega
  refine ⟨hab, ?_⟩
  funext i
  have hi := congrFun h i
  rw [hab] at hi
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hi
  omega

/-- Fixed length removes the ambiguity from terminal zero digits. -/
theorem wordWeight_injective (n : ℕ) : Function.Injective (wordWeight n) := by
  induction n with
  | zero => intro a b _; exact Subsingleton.elim _ _
  | succ n ih =>
    intro a b h
    obtain ⟨hhead, htail⟩ := prependWeight_injective h
    have ht := ih htail
    funext i
    exact Fin.cases hhead (fun j => congrFun ht j) i

/-- Every word has coordinates in the source restricted range. -/
theorem wordWeight_mem_range (n : ℕ) (a : Fin n → BasicWeight) :
    InRestrictedRange n (wordWeight n a) := by
  induction n with
  | zero => intro i; simp [wordWeight]
  | succ n ih =>
    intro i
    have ht := ih (fun j => a j.succ) i
    have hh := coefficient_bounds (a 0) i
    simp only [wordWeight, Pi.add_apply, Pi.smul_apply, smul_eq_mul, pow_succ]
    omega

/-- Extracting parity and dividing by two gives every restricted weight. -/
theorem exists_wordWeight (n : ℕ) (x : Weight) (hx : InRestrictedRange n x) :
    ∃ a, wordWeight n a = x := by
  induction n generalizing x with
  | zero =>
    refine ⟨Fin.elim0, ?_⟩
    funext i
    have hi := hx i
    simp only [pow_zero] at hi
    change 0 = x i
    omega
  | succ n ih =>
    let a : BasicWeight := fun i => decide (x i % 2 = 1)
    let y : Weight := fun i => x i / 2
    have ha (i : Fin 4) : coefficient a i = x i % 2 := by
      have hr := Int.emod_nonneg (x i) (by decide : (2 : ℤ) ≠ 0)
      have hl := Int.emod_lt_of_pos (x i) (by decide : (0 : ℤ) < 2)
      by_cases h : x i % 2 = 1
      · simp [coefficient, a, h]
      · have heq : x i % 2 = 0 := by omega
        simp [coefficient, a, heq]
    have hy : InRestrictedRange n y := by
      intro i
      have hi := hx i
      rw [pow_succ] at hi
      change 0 ≤ x i / 2 ∧ x i / 2 < (2 : ℤ) ^ n
      omega
    obtain ⟨b, hb⟩ := ih y hy
    refine ⟨Fin.cases a b, ?_⟩
    change coefficient a + (2 : ℤ) • wordWeight n b = x
    rw [hb]
    funext i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, ha, y]
    omega

/-- Exactly one length-`n` word represents each restricted weight. -/
theorem existsUnique_wordWeight (n : ℕ) (x : Weight) (hx : InRestrictedRange n x) :
    ∃! a, wordWeight n a = x := by
  obtain ⟨a, ha⟩ := exists_wordWeight n x hx
  exact ⟨a, ha, fun b hb => wordWeight_injective n (hb.trans ha.symm)⟩

/-- The recursive digit expression is the usual sum of powers of two. -/
theorem wordWeight_eq_sum (n : ℕ) (a : Fin n → BasicWeight) :
    wordWeight n a = ∑ i : Fin n, (2 : ℤ) ^ i.val • coefficient (a i) := by
  induction n with
  | zero => simp [wordWeight]
  | succ n ih =>
    rw [wordWeight, Fin.sum_univ_succ, ih]
    simp only [Fin.val_zero, pow_zero, one_smul, Fin.val_succ, pow_succ]
    congr 1
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [smul_smul, mul_comm]

@[simp] theorem wordWeight_one (a : Fin 1 → BasicWeight) :
    wordWeight 1 a = coefficient (a 0) := by simp [wordWeight]

end Triality.RestrictedWeights.SteinbergTensors.AlgebraicTensor
