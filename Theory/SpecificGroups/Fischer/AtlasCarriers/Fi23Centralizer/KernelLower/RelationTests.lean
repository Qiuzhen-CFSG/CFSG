module

public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.KernelLower.Data.AfterFour
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.GeneratorLiftCertificate.Data

/-!
# Numerical contracts for the last Fi23 suffix group

These tests cover all 31671 letters via the existing balanced Boolean checker.
Their soundness supplies precisely the commutation and candidate-map premises
of the binary collection argument in `KernelLower.Tail`. The closed Boolean
equalities are not asserted here and still require kernel certificates.

The product uses generators 1 and 3 in Lean's left-action order. Comparison
with `candidateMap` is comparison with the literal ATLAS candidate once the
existing word and source-action certificates are applied by `Tail`.
Source application: GLS3 Table 5.3u, ATLAS F23G1-p31671B0.
-/

@[expose] public section
namespace Sporadic.Fischer.Fi23.CentralizerSection.KernelLowerData
open Fi24Prime.Fi23Lift.Certificate

def commutationTest (i j : Fin 6) (x : Nat) : Bool :=
  decide (afterFourGenerator i (afterFourGenerator j (Fin.ofNat 31671 x)) =
    afterFourGenerator j (afterFourGenerator i (Fin.ofNat 31671 x)))

def candidateTest (x : Nat) : Bool :=
  decide (afterFourGenerator 1 (afterFourGenerator 3 (Fin.ofNat 31671 x)) =
    GeneratorLiftCertificate.candidateMap (Fin.ofNat 31671 x))

theorem commute_of_checked (i j : Fin 6)
    (h : checkPow (commutationTest i j) 0 15 = true) :
    afterFourGenerator i * afterFourGenerator j =
      afterFourGenerator j * afterFourGenerator i := by
  apply Equiv.ext
  intro x
  have hx := checkPow_sound (commutationTest i j) 15 0 h x.val (Nat.zero_le _)
    (Nat.lt_trans x.isLt (by decide))
  have he : Fin.ofNat 31671 x.val = x := by simp
  simpa only [commutationTest, he, decide_eq_true_eq, Equiv.Perm.mul_apply] using hx

theorem candidate_eq_of_checked (h : checkPow candidateTest 0 15 = true)
    (x : Fin 31671) : afterFourGenerator 1 (afterFourGenerator 3 x) =
      GeneratorLiftCertificate.candidateMap x := by
  have hx := checkPow_sound candidateTest 15 0 h x.val (Nat.zero_le _)
    (Nat.lt_trans x.isLt (by decide))
  have he : Fin.ofNat 31671 x.val = x := by simp
  simpa only [candidateTest, he, decide_eq_true_eq] using hx

end Sporadic.Fischer.Fi23.CentralizerSection.KernelLowerData
