module

public import CFSG.Quasithin.Chapter8.Section02.Normalizer.SmallOvergroups.FourSpaceInspection.MatrixInspection.Data
/-!
# Checked commuting cubic words for all fourteen representatives

Kernel reduction verifies the proposed inverse matrices, evaluates each
short word, and checks that its value and (012) are independent commuting
cubic elements. No group-order table or native evaluation is used. This
proves the exclusion for every listed representative; exhaustive coverage
is the separate `DoubleCosetCoverage` obligation.

Source: Aschbacher–Smith, proof of 8.2.8(1), printed p.719/PDF p.736.
The candidate words come from the search data documented in `Data`.
A representative length-nine word was measured before the whole family.
-/

public section
namespace CFSG.Quasithin.Chapter8.Section02.Normalizer.SmallOvergroups.FourSpaceInspection.MatrixInspection

local instance : DecidableEq (Function.End Bits) :=
  inferInstanceAs (DecidableEq (Bits → Bits))

theorem cycles_even : Equiv.Perm.sign cycleA = 1 ∧ Equiv.Perm.sign cycleB = 1 := by
  decide +kernel

theorem representative_inverse : ∀ i x,
    applyMatrix (representative i) (applyMatrix (representativeInverse i) x) = x := by
  decide +kernel

theorem witness_word : ∀ i, evaluateWord i (witnessWord i) = applyMatrix (witnessColumns i) := by
  decide +kernel

theorem witness_cubics : ∀ i, CubicPair (permuteBits cycleA) (applyMatrix (witnessColumns i)) := by
  unfold CubicPair
  decide +kernel

end CFSG.Quasithin.Chapter8.Section02.Normalizer.SmallOvergroups.FourSpaceInspection.MatrixInspection
