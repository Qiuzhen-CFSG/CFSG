module
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.NativeSubquotient.Packed
public import Mathlib.LinearAlgebra.Matrix.ToLin
/-!
# Rank from distinct leading positions

Binary column vectors with distinct leading nonzero positions are independent:
strong induction on the leading position eliminates every coefficient in a
vanishing linear combination. Packed columns need only a remainder certificate
to identify their leading bit. The actual consumer is the saved 1474-dimensional
source of the native degree-1242 subquotient, avoiding a large inverse product.
-/

@[expose] public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.NativeSubquotient.Leading
open Matrix
-- Distinct leading positions prove rank without a giant inverse certificate.
theorem injective_of_leading {m n : ℕ} (E : Matrix (Fin m) (Fin n) (ZMod 2))
    (p : Fin n → Fin m) (hp : Function.Injective p)
    (hone : ∀ j, E (p j) j = 1)
    (hzero : ∀ i j, i < p j → E i j = 0) : Function.Injective (Matrix.toLin' E) := by
  apply LinearMap.ker_eq_bot.mp
  apply (Submodule.eq_bot_iff _).mpr
  intro x hx
  have he : E.mulVec x = 0 := hx
  have hz : ∀ k : ℕ, ∀ j : Fin n, (p j).val = k → x j = 0 := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro j hj
      have hv := congrFun he (p j)
      change (∑ t, E (p j) t * x t) = 0 at hv
      have hs : (∑ t, E (p j) t * x t) = x j := by
        rw [Finset.sum_eq_single j]
        · rw [hone, one_mul]
        · intro t _ ht
          by_cases hlt : p t < p j
          · rw [ih (p t).val (by simpa [← hj] using hlt) t rfl, mul_zero]
          · have hne : p t ≠ p j := fun h => ht (hp h)
            rw [hzero (p j) t (lt_of_le_of_ne (le_of_not_gt hlt) (Ne.symm hne)), zero_mul]
        · simp
      exact hs.symm.trans hv
  exact funext (fun j => hz (p j).val j rfl)

open Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree220Pair.NativeActions.CertificatePacked
open Thompson.BinaryMatrix

/-- A single remainder calculation specifies the leading nonzero bit. -/
theorem leading_bit (x k : ℕ) (h : x % 2^(k+1) = 2^k) :
    bit x k = 1 ∧ ∀ i < k, bit x i = 0 := by
  have ht (i : ℕ) (hi : i < k+1) : x.testBit i = (2^k).testBit i := by
    have he := congrArg (fun z : ℕ => z.testBit i) h
    simpa [Nat.testBit_mod_two_pow, hi] using he
  constructor
  · simp [bit, ht k (by omega)]
  · intro i hi
    simp [bit, ht i (by omega), Nat.ne_of_gt hi]

def checkLeading : List ℕ → List ℕ → Bool
  | [], [] => true
  | x::xs, k::ks => (x % 2^(k+1) == 2^k) && checkLeading xs ks
  | _, _ => false

theorem checkLeading_sound (xs ks : List ℕ) (h : checkLeading xs ks = true)
    (i : ℕ) (hi : i < xs.length) : xs[i]! % 2^(ks[i]!+1) = 2^ks[i]! := by
  induction xs generalizing ks i with
  | nil => simp at hi
  | cons x xs ih =>
    cases ks with
    | nil => simp [checkLeading] at h
    | cons k ks =>
      simp only [checkLeading, Bool.and_eq_true, beq_iff_eq] at h
      cases i with
      | zero => exact h.1
      | succ i => exact ih _ h.2 i (by simpa using hi)

/-- A bitset certifies distinct natural positions in one pass. -/
def checkDistinct : List ℕ → ℕ → Bool
  | [], _ => true
  | k::ks, seen => (!seen.testBit k) && checkDistinct ks (seen ||| 2^k)

theorem checkDistinct_sound (xs : List ℕ) (seen : ℕ)
    (h : checkDistinct xs seen = true) :
    xs.Nodup ∧ ∀ k ∈ xs, seen.testBit k = false := by
  induction xs generalizing seen with
  | nil => simp
  | cons x xs ih =>
    simp only [checkDistinct, Bool.and_eq_true] at h
    obtain ⟨hn, hs⟩ := ih _ h.2
    constructor
    · apply List.nodup_cons.mpr
      refine ⟨?_, hn⟩
      intro hx
      have hh := hs x hx
      simp [Nat.testBit_or] at hh
    · intro k hk
      rcases List.mem_cons.mp hk with he | hk
      · simpa [he] using h.1
      · have hh := hs k hk
        rw [Nat.testBit_or, Bool.or_eq_false_iff] at hh
        exact hh.1

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.NativeSubquotient.Leading
