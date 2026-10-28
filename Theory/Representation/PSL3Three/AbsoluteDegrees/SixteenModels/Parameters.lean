module

public import Theory.Representation.PSL3Three.AbsoluteDegrees.SixteenModels.Data
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.Algebra.CharP.Reduced
public import Mathlib.Algebra.CharP.Two
import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Tauto

/-!
# Four coefficient parameters and trace separation

Every algebraically closed field contains a root of `X⁴-X-1`. In
characteristic two its four binary Frobenius conjugates are distinct roots.
The trace parameter `s=t³+t+1` recovers `t` by `s+s²=t`, so the same four
parameters also have distinct traces. This supplies the field-independent
separation argument for the ATLAS generator matrices in `Data`.

Source: the degree-sixteen constructions underlying GM02, Proposition 4.2,
manuscript pp.9–10. The polynomial and trace identities are proved directly;
no character table or field-of-definition obstruction is assumed.
-/

public section
open Polynomial
namespace Representation.PSL3Three.AbsoluteDegrees.SixteenModels
variable {F : Type*} [Field F] [CharP F 2]

omit [CharP F 2] in
theorem exists_parameter [IsAlgClosed F] : ∃ t : F, t ^ 4 = t + 1 := by
  have hd : (X ^ 4 - X - 1 : F[X]).natDegree = 4 := by compute_degree; exact one_ne_zero
  obtain ⟨t, ht⟩ := IsAlgClosed.exists_root (X ^ 4 - X - 1 : F[X]) (by
    intro h
    have hz : (X ^ 4 - X - 1 : F[X]).natDegree = 0 :=
      Polynomial.natDegree_eq_of_degree_eq_some h
    omega)
  refine ⟨t, ?_⟩
  have h : t ^ 4 - t - 1 = 0 := by simpa only [IsRoot, eval_sub, eval_pow, eval_X,
    eval_one] using ht
  linear_combination h

theorem square_parameter (t : F) (ht : t ^ 4 = t + 1) :
    (t ^ 2) ^ 4 = t ^ 2 + 1 := by
  calc
    (t ^ 2) ^ 4 = (t ^ 4) ^ 2 := by ring
    _ = (t + 1) ^ 2 := by rw [ht]
    _ = t ^ 2 + 1 := by rw [add_pow_char, one_pow]

theorem sixteenth_parameter (t : F) (ht : t ^ 4 = t + 1) : t ^ 16 = t := by
  calc
    t ^ 16 = (t ^ 4) ^ 4 := by ring
    _ = (t + 1) ^ (2 ^ 2)  := by rw [ht]; norm_num
    _ = t ^ 4 + 1 := by rw [add_pow_char_pow, one_pow]; norm_num
    _ = t := by rw [ht]; simp [add_assoc, CharTwo.add_self_eq_zero]

omit [CharP F 2] in
theorem square_ne_self (t : F) (ht : t ^ 4 = t + 1) : t ^ 2 ≠ t := by
  intro h
  have h4 : t ^ 4 = t := by calc
    _ = (t ^ 2) ^ 2 := by ring
    _ = t := by rw [h, h]
  have hn : t + (1 : F) = t + 0 := by simpa using ht.symm.trans h4
  exact one_ne_zero (add_left_cancel hn)

omit [CharP F 2] in
theorem fourth_ne_self (t : F) (ht : t ^ 4 = t + 1) : t ^ 4 ≠ t := by
  intro h
  have hn : t + (1 : F) = t + 0 := by simpa using ht.symm.trans h
  exact one_ne_zero (add_left_cancel hn)

theorem eighth_ne_self (t : F) (ht : t ^ 4 = t + 1) : t ^ 8 ≠ t := by
  intro h
  apply square_ne_self t ht
  calc
    t ^ 2 = (t ^ 8) ^ 2 := by rw [h]
    _ = t ^ 16 := by ring
    _ = t := sixteenth_parameter t ht

theorem orbit_injective (t : F) (ht : t ^ 4 = t + 1) :
    Function.Injective (fun i : Fin 4 => t ^ (2 ^ i.val)) := by
  have hs : Function.Injective (fun x : F => x ^ 2) := frobenius_inj F 2
  have h1 := square_ne_self t ht
  have h2 := fourth_ne_self t ht
  have h3 := eighth_ne_self t ht
  have h12 : t ^ 2 ≠ t ^ 4 := by
    intro h
    apply h1
    apply hs
    simpa only [← pow_mul] using h.symm
  have h13 : t ^ 2 ≠ t ^ 8 := by
    intro h
    apply h2
    apply hs
    simpa only [← pow_mul] using h.symm
  have h23 : t ^ 4 ≠ t ^ 8 := by
    intro h
    apply h12
    apply hs
    simpa only [← pow_mul] using h
  intro i j hij
  fin_cases i <;> fin_cases j <;> norm_num at hij ⊢ <;> tauto

theorem traceParameter_recover (t : F) (ht : t ^ 4 = t + 1) :
    traceParameter t + (traceParameter t) ^ 2 = t := by
  unfold traceParameter
  rw [add_pow_char, add_pow_char, one_pow]
  have h6 : t ^ 6 = t ^ 3 + t ^ 2 := by
    calc
      t ^ 6 = t ^ 2 * t ^ 4 := by ring
      _ = t ^ 3 + t ^ 2 := by rw [ht]; ring
  rw [← pow_mul, h6]
  ring_nf
  simp [CharTwo.two_eq_zero]

theorem orbit_parameter (t : F) (ht : t ^ 4 = t + 1) (i : Fin 4) :
    (t ^ (2 ^ i.val)) ^ 4 = t ^ (2 ^ i.val) + 1 := by
  calc
    (t ^ (2 ^ i.val)) ^ 4 = (t ^ 4) ^ (2 ^ i.val) := by ring
    _ = (t + 1) ^ (2 ^ i.val) := by rw [ht]
    _ = t ^ (2 ^ i.val) + 1 := by rw [add_pow_char_pow, one_pow]


theorem traceParameter_orbit_injective (t : F) (ht : t ^ 4 = t + 1) :
    Function.Injective (fun i : Fin 4 => traceParameter (t ^ (2 ^ i.val))) := by
  intro i j h
  apply orbit_injective t ht
  change t ^ (2 ^ i.val) = t ^ (2 ^ j.val)
  change traceParameter (t ^ (2 ^ i.val)) = traceParameter (t ^ (2 ^ j.val)) at h
  rw [← traceParameter_recover _ (orbit_parameter t ht i),
    ← traceParameter_recover _ (orbit_parameter t ht j), h]

end Representation.PSL3Three.AbsoluteDegrees.SixteenModels
