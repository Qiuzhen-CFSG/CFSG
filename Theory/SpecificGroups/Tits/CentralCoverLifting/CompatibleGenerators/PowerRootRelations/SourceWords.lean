module

public import Theory.SpecificGroups.Tits.CentralCoverLifting.CompatibleGenerators.PowerRootRelations.WordCalculus
import Mathlib.Algebra.Group.TypeTags.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Group
/-!
# Literal source words for the central-error calculation

Each signed list below is checked against the original `parrottRelator`.
The equality records its actual central value, without asserting that this
value vanishes. All subsequent rewrite certificates start from these checks.

Source: Parrott (1972), §5, p.683.
-/

public section

namespace Tits.CentralCoverLifting.CompatibleGenerators.PowerRootWords
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
open Tits
open scoped IsMulCommutative
macro "central_nf" : tactic => `(tactic|
  (apply Additive.ofMul.injective
   simp only [ofMul_mul, ofMul_inv, ofMul_pow, ofMul_zpow, ofMul_one]
   abel))
theorem source0 : value [1, 1] = ((normalizedRelatorError .i_r1 : C) : E) := by
  simp [value, letter, numbered, normalizedRelatorError, parrottRelator,
    parrottCommutator, parrottR3, parrottR5, parrottR7, pow_succ]

theorem source1 : value [2, 2] = ((normalizedRelatorError .i_r8 : C) : E) := by
  simp [value, letter, numbered, normalizedRelatorError, parrottRelator,
    parrottCommutator, parrottR3, parrottR5, parrottR7, pow_succ]

theorem source2 : value [3, 3] = ((normalizedRelatorError .i_s1 : C) : E) := by
  simp [value, letter, numbered, normalizedRelatorError, parrottRelator,
    parrottCommutator, parrottR3, parrottR5, parrottR7, pow_succ]

theorem source3 : value [4, 4] = ((normalizedRelatorError .i_s2 : C) : E) := by
  simp [value, letter, numbered, normalizedRelatorError, parrottRelator,
    parrottCommutator, parrottR3, parrottR5, parrottR7, pow_succ]

theorem source4 : value [6, 6] = ((normalizedRelatorError .i_s4 : C) : E) := by
  simp [value, letter, numbered, normalizedRelatorError, parrottRelator,
    parrottCommutator, parrottR3, parrottR5, parrottR7, pow_succ]

theorem source5 : value [8, 8] = ((normalizedRelatorError .i_s6 : C) : E) := by
  simp [value, letter, numbered, normalizedRelatorError, parrottRelator,
    parrottCommutator, parrottR3, parrottR5, parrottR7, pow_succ]

theorem source6 : value [10, 10] = ((normalizedRelatorError .i_s8 : C) : E) := by
  simp [value, letter, numbered, normalizedRelatorError, parrottRelator,
    parrottCommutator, parrottR3, parrottR5, parrottR7, pow_succ]

theorem source7 : value [5, 5, 5, 5] = ((normalizedRelatorError .i_s3 : C) : E) := by
  simp [value, letter, numbered, normalizedRelatorError, parrottRelator,
    parrottCommutator, parrottR3, parrottR5, parrottR7, pow_succ]
  group

theorem source8 : value [7, 7, 7, 7] = ((normalizedRelatorError .i_s5 : C) : E) := by
  simp [value, letter, numbered, normalizedRelatorError, parrottRelator,
    parrottCommutator, parrottR3, parrottR5, parrottR7, pow_succ]
  group

theorem source9 : value [9, 9, 9, 9] = ((normalizedRelatorError .i_s7 : C) : E) := by
  simp [value, letter, numbered, normalizedRelatorError, parrottRelator,
    parrottCommutator, parrottR3, parrottR5, parrottR7, pow_succ]
  group

theorem source10 : value [-3, -4, 3, 4] = ((normalizedRelatorError .ii_s1_s2 : C) : E) := by
  simp [value, letter, numbered, normalizedRelatorError, parrottRelator,
    parrottCommutator, parrottR3, parrottR5, parrottR7, pow_succ]
  group

theorem source11 : value [-3, -5, 3, 5] = ((normalizedRelatorError .ii_s1_s3 : C) : E) := by
  simp [value, letter, numbered, normalizedRelatorError, parrottRelator,
    parrottCommutator, parrottR3, parrottR5, parrottR7, pow_succ]
  group

theorem source12 : value [-3, -7, 3, 7] = ((normalizedRelatorError .ii_s1_s5 : C) : E) := by
  simp [value, letter, numbered, normalizedRelatorError, parrottRelator,
    parrottCommutator, parrottR3, parrottR5, parrottR7, pow_succ]
  group

theorem source13 : value [-3, -8, 3, 8, -5, -5, -4, -3] = ((normalizedRelatorError .iii_s1_s6 : C) : E) := by
  simp [value, letter, numbered, normalizedRelatorError, parrottRelator,
    parrottCommutator, parrottR3, parrottR5, parrottR7, pow_succ]
  group

theorem source14 : value [-3, -9, 3, 9, -7, -7, -3, -5, -5, -4, -3, -4] = ((normalizedRelatorError .iii_s1_s7 : C) : E) := by
  simp [value, letter, numbered, normalizedRelatorError, parrottRelator,
    parrottCommutator, parrottR3, parrottR5, parrottR7, pow_succ]
  group

theorem source15 : value [-3, -10, 3, 10, -3, -5, -5, -4, -3, -9, -9] = ((normalizedRelatorError .iii_s1_s8 : C) : E) := by
  simp [value, letter, numbered, normalizedRelatorError, parrottRelator,
    parrottCommutator, parrottR3, parrottR5, parrottR7, pow_succ]
  group

theorem source16 : value [-4, -6, 4, 6] = ((normalizedRelatorError .iv_s2_s4 : C) : E) := by
  simp [value, letter, numbered, normalizedRelatorError, parrottRelator,
    parrottCommutator, parrottR3, parrottR5, parrottR7, pow_succ]
  group

theorem source17 : value [-4, -8, 4, 8] = ((normalizedRelatorError .iv_s2_s6 : C) : E) := by
  simp [value, letter, numbered, normalizedRelatorError, parrottRelator,
    parrottCommutator, parrottR3, parrottR5, parrottR7, pow_succ]
  group

theorem source18 : value [-4, -10, 4, 10, -8, -6] = ((normalizedRelatorError .iv_s2_s8 : C) : E) := by
  simp [value, letter, numbered, normalizedRelatorError, parrottRelator,
    parrottCommutator, parrottR3, parrottR5, parrottR7, pow_succ]
  group

theorem source19 : value [-9, -4, 9, 4, -7, -7, -3, -6] = ((normalizedRelatorError .iv_s7_s2 : C) : E) := by
  simp [value, letter, numbered, normalizedRelatorError, parrottRelator,
    parrottCommutator, parrottR3, parrottR5, parrottR7, pow_succ]
  group

theorem source20 : value [-9, -6, 9, 6, -7, -7, -3, -5, -5, -4, -3] = ((normalizedRelatorError .v_s7_s4 : C) : E) := by
  simp [value, letter, numbered, normalizedRelatorError, parrottRelator,
    parrottCommutator, parrottR3, parrottR5, parrottR7, pow_succ]
  group

theorem source21 : value [-5, -7, 5, 7, -6, -5, -5, -4, -3, -4] = ((normalizedRelatorError .v_s3_s5 : C) : E) := by
  simp [value, letter, numbered, normalizedRelatorError, parrottRelator,
    parrottCommutator, parrottR3, parrottR5, parrottR7, pow_succ]
  group

theorem source22 : value [-7, -6, 7, 6, -5, -5, -4, -3] = ((normalizedRelatorError .v_s5_s4 : C) : E) := by
  simp [value, letter, numbered, normalizedRelatorError, parrottRelator,
    parrottCommutator, parrottR3, parrottR5, parrottR7, pow_succ]
  group

theorem source23 : value [1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2] = ((normalizedRelatorError .vi_r1_r8 : C) : E) := by
  simp [value, letter, numbered, normalizedRelatorError, parrottRelator,
    parrottCommutator, parrottR3, parrottR5, parrottR7, pow_succ]
  group

theorem source24 : value [3, 1, 3, 1, 3, 1, 3, 1, 3, 1] = ((normalizedRelatorError .vi_s1_r1 : C) : E) := by
  simp [value, letter, numbered, normalizedRelatorError, parrottRelator,
    parrottCommutator, parrottR3, parrottR5, parrottR7, pow_succ]
  group

theorem source25 : value [2, 10, 2, 10, 2, 10] = ((normalizedRelatorError .vi_r8_s8 : C) : E) := by
  simp [value, letter, numbered, normalizedRelatorError, parrottRelator,
    parrottCommutator, parrottR3, parrottR5, parrottR7, pow_succ]
  group

theorem source26 : value [1, 4, 1, -10] = ((normalizedRelatorError .vii_s2 : C) : E) := by
  simp [value, letter, numbered, normalizedRelatorError, parrottRelator,
    parrottCommutator, parrottR3, parrottR5, parrottR7, pow_succ]
  group

theorem source27 : value [1, 6, 1, -8] = ((normalizedRelatorError .vii_s4 : C) : E) := by
  simp [value, letter, numbered, normalizedRelatorError, parrottRelator,
    parrottCommutator, parrottR3, parrottR5, parrottR7, pow_succ]
  group

theorem source28 : value [1, 7, 1, -7, -1, -3, -1, -3] = ((normalizedRelatorError .vii_s5 : C) : E) := by
  simp [value, letter, numbered, normalizedRelatorError, parrottRelator,
    parrottCommutator, parrottR3, parrottR5, parrottR7, pow_succ]
  group

theorem source29 : value [1, 5, 1, -9, -7, -5, -5, -5, -4, -3, -1, -3, -1, -3] = ((normalizedRelatorError .vii_s3 : C) : E) := by
  simp [value, letter, numbered, normalizedRelatorError, parrottRelator,
    parrottCommutator, parrottR3, parrottR5, parrottR7, pow_succ]
  group

theorem source30 : value [1, 3, 4, 5, 5, 1, -9, -7, -5, -5, -5, -4, -3, -9] = ((normalizedRelatorError .vii_r3 : C) : E) := by
  simp [value, letter, numbered, normalizedRelatorError, parrottRelator,
    parrottCommutator, parrottR3, parrottR5, parrottR7, pow_succ]
  group

theorem source31 : value [2, 4, 2, -8] = ((normalizedRelatorError .viii_s2 : C) : E) := by
  simp [value, letter, numbered, normalizedRelatorError, parrottRelator,
    parrottCommutator, parrottR3, parrottR5, parrottR7, pow_succ]
  group

theorem source32 : value [2, 6, 2, -6] = ((normalizedRelatorError .viii_s4 : C) : E) := by
  simp [value, letter, numbered, normalizedRelatorError, parrottRelator,
    parrottCommutator, parrottR3, parrottR5, parrottR7, pow_succ]
  group

theorem source33 : value [2, 3, 2, -9, -7, -5, -5, -5, -4, -3, -9] = ((normalizedRelatorError .viii_s1 : C) : E) := by
  simp [value, letter, numbered, normalizedRelatorError, parrottRelator,
    parrottCommutator, parrottR3, parrottR5, parrottR7, pow_succ]
  group

theorem source34 : value [2, 9, 2, 9] = ((normalizedRelatorError .viii_s7 : C) : E) := by
  simp [value, letter, numbered, normalizedRelatorError, parrottRelator,
    parrottCommutator, parrottR3, parrottR5, parrottR7, pow_succ]
  group

theorem source35 : value [2, 5, 2, -7, -9] = ((normalizedRelatorError .viii_s3 : C) : E) := by
  simp [value, letter, numbered, normalizedRelatorError, parrottRelator,
    parrottCommutator, parrottR3, parrottR5, parrottR7, pow_succ]
  group

theorem source36 : value [2, 3, 4, 5, 5, 2, -7, -7, -3] = ((normalizedRelatorError .viii_r3 : C) : E) := by
  simp [value, letter, numbered, normalizedRelatorError, parrottRelator,
    parrottCommutator, parrottR3, parrottR5, parrottR7, pow_succ]
  group

end Tits.CentralCoverLifting.CompatibleGenerators.PowerRootWords
