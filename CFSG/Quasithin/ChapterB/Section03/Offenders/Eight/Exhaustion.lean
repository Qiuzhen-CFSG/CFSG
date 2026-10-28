module

public import CFSG.Quasithin.ChapterB.Section03.Offenders.Eight.Exhaustion.Full
public import CFSG.Quasithin.ChapterB.Section03.Offenders.Eight.Exhaustion.OrbitDefect
public import CFSG.Quasithin.ChapterB.Section03.Offenders.Eight.Exhaustion.QuotientReduction

/-!
# Degree-eight structural exhaustion

Best offenders on the full and deleted permutation modules belong to case (a).
On the even-weight core they belong to case (b), and on the natural module
there is the additional possibility of a regular elementary abelian subgroup
of order eight in the alternating group. Each family uses actual ambient
conjugacy to the concrete source representatives.

The full-module argument uses the equality case of the abelian orbit bound.
For the core, a common fixed coordinate gives case (a); otherwise the
augmentation bound gives full fixed codimension at most rank plus one, and
the orbit-defect classification gives case (b). Constant-displacement
characters give the quotient reductions: the deleted case reduces to the full
module, and the natural case reduces to the same defect-one classification
or to the regular action. All hypotheses of these structural reductions are
discharged here. The reductions in fact prove necessity for every offender,
and hence for every best offender.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
1 March 2004 manuscript, the necessity directions of Proposition B.3.2(4)–(6)
in degree eight, printed pp. 83–84. The full and deleted results are
re-exported from `Exhaustion.Full` and `Exhaustion.QuotientReduction`.
-/

public section

namespace CFSG.Quasithin.ChapterB.Offenders.EightExhaustion

open BinaryPermutation Representation.BinaryOffender

/-- Every core offender belongs to the case-(b) family in degree eight. -/
theorem caseBFamily_of_isOffender_core {A : Subgroup (Equiv.Perm (Fin 8))}
    (hA : IsOffender (coreRepresentation (Fin 8)) A) :
    CaseBFamily 8 (by decide) A := by
  by_cases hc : CaseAFamily 8 A
  · exact Or.inl hc
  exact caseBFamily_of_defect_le_one A hA.1
    (no_fixed_point_of_isOffender_core_of_not_caseA hA hc)
    (full_fixedCodim_le_rank_add_one_of_isOffender_core hA)

/-- B.3.2(5), necessity on the core in degree eight. -/
theorem caseBFamily_of_isBestOffender_core {A : Subgroup (Equiv.Perm (Fin 8))}
    (hA : IsBestOffender (coreRepresentation (Fin 8)) A) :
    CaseBFamily 8 (by decide) A :=
  caseBFamily_of_isOffender_core (hA.isOffender _)

/-- Every natural-module offender belongs to case (b) or is a regular
elementary abelian subgroup of order eight in the alternating group. -/
theorem caseBFamily_or_isRegularEight_of_isOffender_natural
    {A : Subgroup (Equiv.Perm (Fin 8))}
    (hA : IsOffender (naturalRepresentation (Fin 8)) A) :
    CaseBFamily 8 (by decide) A ∨ IsRegularEight A := by
  rcases caseAFamily_or_isRegularEight_or_defect_one_of_isOffender_natural hA with
    hc | hr | ⟨hmove, hdef⟩
  · exact Or.inl (Or.inl hc)
  · exact Or.inr hr
  · exact Or.inl (caseBFamily_of_defect_le_one A hA.1 hmove hdef)

/-- B.3.2(6), necessity on the natural module in degree eight. -/
theorem caseBFamily_or_isRegularEight_of_isBestOffender_natural
    {A : Subgroup (Equiv.Perm (Fin 8))}
    (hA : IsBestOffender (naturalRepresentation (Fin 8)) A) :
    CaseBFamily 8 (by decide) A ∨ IsRegularEight A :=
  caseBFamily_or_isRegularEight_of_isOffender_natural (hA.isOffender _)

end CFSG.Quasithin.ChapterB.Offenders.EightExhaustion
