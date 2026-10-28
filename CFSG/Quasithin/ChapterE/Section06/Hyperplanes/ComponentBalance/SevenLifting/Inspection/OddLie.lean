module

public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance.SevenLifting.Inspection
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance.SevenLifting.Inspection.OddLie.LinearTwo
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance.SevenLifting.Inspection.OddLie.LinearThreeFixed
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance.SevenLifting.Inspection.OddLie.UnitaryThreeFixed

/-!
# Odd-characteristic branches of the seven inspection

The PSL₂ branch is proved by the subgroup exclusion in `OddLie.LinearTwo`.
The same order argument handles PSL₃(3). The remaining linear-three and
unitary-three branches require the concrete derived-fixed-group rank bounds;
`OddLie.Reduction` proves their implication for an arbitrary two-subgroup
of the full automorphism group, preserving the intrinsic component input.
Those model calculations are discharged in the imported modules.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), E.6.18,
printed p.252 (PDF p.263), and Theorem C, printed p.33.
-/

public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance.OddLie
variable {G : Type*} [Group G]

/-- PSL₃(3) has order 5616, so no seven group can embed in any fixed subgroup. -/
theorem sevenActionInspection_linear_three_three (hG : ClassicalGroup.IsPSL G 3 3) :
    SevenActionInspection G := by
  obtain ⟨F, hfield, hfinite, hF, ⟨f⟩⟩ := hG
  have hc := Atlas.ExceptionalSupport.card_psl_mul (F := F) 3
  rw [hF] at hc
  norm_num [Fin.prod_univ_succ] at hc
  have hcard : Nat.card G = 5616 := by
    rw [Nat.card_congr f.toEquiv]
    omega
  intro P hP L hLF hLc hL
  exact not_isSeven_of_seven_not_dvd (by rw [hcard]; decide) L hL |>.elim

/-- The complete odd-prime PSL₃ branch. The field of order three is handled
by its exact order; all other odd primes use the involution fixed-group
three-rank calculation. -/
theorem sevenActionInspection_linear_three_odd
    [Finite G] [IsSimpleGroup G] (hnc : ¬ IsMulCommutative G)
    {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hG : ClassicalGroup.IsPSL G 3 p) : SevenActionInspection G := by
  by_cases hp3 : p = 3
  · subst p
    exact sevenActionInspection_linear_three_three hG
  · exact sevenActionInspection_of_involutionDerivedThreeRank
      (involutionDerivedThreeRank_linear_three hnc hp ho hp3 hG)

/-- The complete odd-prime PSU₃ branch, including characteristic three. The
genuine projective unitary model and its field convention are retained by
`ClassicalGroup.IsPSU`. -/
theorem sevenActionInspection_unitary_three_odd
    [Finite G] [IsSimpleGroup G] {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hG : ClassicalGroup.IsPSU G 3 p) : SevenActionInspection G := by
  exact sevenActionInspection_of_involutionDerivedThreeRank
    (involutionDerivedThreeRank_unitary hp ho hG)

/-- The signed degree-three constructor of Theorem C. `unitary = false` is
the genuine PSL₃ branch and `unitary = true` is the genuine PSU₃ branch. -/
theorem sevenActionInspection_three_odd
    [Finite G] [IsSimpleGroup G] (hnc : ¬ IsMulCommutative G)
    {p : ℕ} (hp : p.Prime) (ho : Odd p) (unitary : Bool)
    (hG : Chapter1.Section02.LocalModels.IsPSLSign G unitary 3 p) :
    SevenActionInspection G := by
  cases unitary with
  | false =>
      exact sevenActionInspection_linear_three_odd hnc hp ho hG
  | true =>
      exact sevenActionInspection_unitary_three_odd hp ho hG

end CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance.OddLie
