module

public import CFSG.Quasithin.ChapterC.Section01.BlockStructure.Commutation.CubicSetup
public import CFSG.Quasithin.ChapterC.Section01.BlockStructure.Commutation.Cubic.Normalized

/-!
# Commutation reductions for cubic blocks

Mutually normalizing cubic blocks with different embedded two-cores commute:
the alternative from the four-element commutator dichotomy would identify
those cores. A commutator bound modulo the ambient two-core also suffices,
since the residual characterization of subnormal two-perfect subgroups
lifts quotient commutation to mutual normalization.

These are conditional reductions. The unconditional cubic branch of C.1.9
still needs core uniqueness under the upper-core guard and the subnormal
argument establishing normalization. It is not asserted here.

Source: Aschbacher--Smith, combined manuscript of 1 March 2004, C.1.9,
printed p.123, citing Aschbacher (1981), §3.4.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC.BlockCommutation
variable {G : Type*} [Group G] [Finite G]

/-- The normalizing cubic case after excluding the shared-core obstruction. -/
theorem cubic_blocks_commute_of_normalizes_of_core_ne (X Y : Subgroup G)
    (hX : IsBlock X) (hY : IsBlock Y)
    (hqX : Nat.card (X ⧸ pCore 2 X) = 3)
    (hqY : Nat.card (Y ⧸ pCore 2 Y) = 3)
    (hnX : Y ≤ normalizer X) (hnY : X ≤ normalizer Y)
    (hne : X.pCoreIn 2 ≠ Y.pCoreIn 2) : ⁅X, Y⁆ = ⊥ := by
  rcases cubic_normalizing_dichotomy X Y hX hY hqX hqY hnX hnY with hc | hc
  · exact hc
  · exact (hne hc.2).elim

/-- Apply the cubic dichotomy after the actual ambient quotient commutator bound. -/
theorem cubic_blocks_commute_of_quotient_bound_of_core_ne (X Y : Subgroup G)
    (hX : IsBlock X) (hY : IsBlock Y)
    (hqX : Nat.card (X ⧸ pCore 2 X) = 3)
    (hqY : Nat.card (Y ⧸ pCore 2 Y) = 3)
    (hc : ⁅X, Y⁆ ≤ pCore 2 G) (hne : X.pCoreIn 2 ≠ Y.pCoreIn 2) :
    ⁅X, Y⁆ = ⊥ := by
  obtain ⟨hnX, hnY, _⟩ := pair_core_bound X Y hX hY hc
  exact cubic_blocks_commute_of_normalizes_of_core_ne X Y hX hY hqX hqY hnX hnY hne

end CFSG.Quasithin.ChapterC.BlockCommutation
