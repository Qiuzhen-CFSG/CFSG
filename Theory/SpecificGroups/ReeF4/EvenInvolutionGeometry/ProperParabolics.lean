module

public import Theory.SpecificGroups.ReeF4.SectionGeometry.CoreFree.LinearRadical.Normality
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.RadicalOrders
public import Mathlib.GroupTheory.IsPerfect
public import Mathlib.GroupTheory.Subgroup.Simple
public import Mathlib.GroupTheory.Nilpotent

/-!
# Properness of the two root-defined Ree parabolics

Each full parabolic normalizes its root-defined radical. The radical is a
nontrivial two-group by the checked root-coordinate order calculation.
If the parabolic were the whole simple group, its radical would be the
whole group; perfectness excludes that finite nilpotent group.

The simplicity and perfectness hypotheses are on the original carrier,
as inherited from the component in Aschbacher–Smith 16.1.4(1), printed
p.1171 of `refs/quasithin.pdf`. No independent simplicity theorem or
maximal-subgroup classification is used.
-/

public section

namespace ReeF4.EvenInvolutionGeometry
open Parabolics LargeLocalSeeds Subgroup

theorem radical_ne_bot (m : ℕ) (s : Side) : radical m s ≠ ⊥ := by
  have hq : 1 < 2 ^ (2 * m + 1) := Nat.one_lt_pow (by omega) (by omega)
  have hc : 1 < Nat.card (radical m s) := by
    cases s with
    | suzuki => rw [card_radical_suzuki]; exact Nat.one_lt_pow (by decide) hq
    | linear => rw [card_radical_linear]; exact Nat.one_lt_pow (by decide) hq
  intro h
  simp [h] at hc

theorem parabolic_ne_top (m : ℕ) [IsSimpleGroup (Model m)] [Group.IsPerfect (Model m)]
    (s : Side) : parabolic m s ≠ ⊤ := by
  intro hP
  have hn : (radical m s).Normal := normalizer_eq_top_iff.mp (top_unique (by
    simpa only [hP] using SectionGeometry.LinearRadical.parabolic_le_radical_normalizer m s))
  rcases hn.eq_bot_or_eq_top with h | h
  · exact radical_ne_bot m s h
  · have hp := radical_isPGroup m s
    rw [h] at hp
    exact Group.IsPerfect.not_isNilpotent (Model m) (hp.of_equiv Subgroup.topEquiv).isNilpotent
end ReeF4.EvenInvolutionGeometry
