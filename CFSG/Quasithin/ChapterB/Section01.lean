module

public import CFSG.Quasithin.ChapterB.Defs
public import Theory.Representation.BinaryOffender.Stability
public import Theory.Representation.BinaryOffender.Ratio

/-!
# B.1: representations and FF-modules

The basic offender theory is re-exported from
`Representation.BinaryOffender`. The results below give the source's ratio
statements for B.1.4(1) and (6). The imported elementary theory also proves
B.1.4(2), (4) and (5)(i) iff (ii), and existence of equal-weight minimal best
offenders. The ratio module proves (5)(iii) implies (i) by attainment of a
finite minimum. The stability module proves B.1.7 under the necessary
nonemptiness hypothesis (an FF-module), and normality of the generated groups
used in B.1.9. These arguments use finite maximization, rank-nullity and
conjugacy transport of fixed subspaces.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
1 March 2004 manuscript, §B.1. The later structural results B.1.5–B.1.13
and Thompson replacement B.1.4(3) remain to be assembled.
-/

namespace CFSG.Quasithin.ChapterB

open Representation.BinaryOffender

variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V]
  [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

/-- B.1.4(1): an FF-star offender has action ratio at most one. -/
public theorem bestOffender_actionRatio_le_one {A : Subgroup G} (hA : IsBestOffender ρ A) :
    actionRatio ρ A ≤ 1 :=
  (actionRatio_le_one_iff ρ hA.1).2 (hA.isOffender ρ).2

/-- B.1.4(6): in the absence of strong FF-modules, the best offenders are
exactly the nontrivial elementary abelian subgroups of action ratio one. -/
public theorem bestOffender_iff_actionRatio_eq_one
    (h : ¬ IsStrongFFModule ρ) (A : Subgroup G) :
    IsBestOffender ρ A ↔ IsElementaryTwo A ∧ actionRatio ρ A = 1 := by
  rw [isBestOffender_iff_of_not_strong ρ h A]
  exact and_congr_right (fun hA => (actionRatio_eq_one_iff ρ hA).symm)

end CFSG.Quasithin.ChapterB
