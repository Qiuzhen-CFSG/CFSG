module

public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.KernelUpper.Data.Basic
public import Mathlib.Algebra.Group.Subgroup.Defs

/-!
# Interpreting the third-stage word witnesses

A word stores one generator index in each hexadecimal digit, starting with
its leftmost factor in the low digit. The length is explicit, so zero digits
are genuine generators. Pointwise evaluation agrees with group multiplication;
words in subgroup elements remain in the subgroup. This interprets the orbit
representatives and the Schreier factors used in the Fi23 prefix certificate.

Source application: ATLAS F23G1-p31671B0 and GLS3 Table 5.3u.
-/

@[expose] public section
namespace Sporadic.Fischer.Fi23.CentralizerSection.KernelUpperThird

/-- Interpret hexadecimal digits as generator indices. -/
def wordValue {n : Nat} [NeZero n] {G : Type*} [Group G]
    (gen : Fin n → G) : Nat → Nat → G
  | 0, _ => 1
  | k + 1, w => gen (Fin.ofNat n (w % 16)) * wordValue gen k (w / 16)

/-- The corresponding evaluator on letters, in left-action order. -/
def wordRun {n : Nat} [NeZero n] {X : Type*}
    (gen : Fin n → X → X) : Nat → Nat → X → X
  | 0, _, x => x
  | k + 1, w, x => gen (Fin.ofNat n (w % 16)) (wordRun gen k (w / 16) x)

theorem wordRun_eq {n : Nat} [NeZero n] {X : Type*}
    (gen : Fin n → Equiv.Perm X) (f : Fin n → X → X)
    (hf : ∀ i x, f i x = gen i x) (k w : Nat) (x : X) :
    wordRun f k w x = wordValue gen k w x := by
  induction k generalizing w with
  | zero => rfl
  | succ k ih =>
    simp only [wordRun, wordValue, Equiv.Perm.mul_apply, hf, ih]

theorem wordValue_mem {n : Nat} [NeZero n] {G : Type*} [Group G]
    (K : Subgroup G) (gen : Fin n → G) (hgen : ∀ i, gen i ∈ K) (k w : Nat) :
    wordValue gen k w ∈ K := by
  induction k generalizing w with
  | zero => exact K.one_mem
  | succ k ih => exact K.mul_mem (hgen _) (ih _)

end Sporadic.Fischer.Fi23.CentralizerSection.KernelUpperThird
