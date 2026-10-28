module

public import CFSG.Quasithin.Chapter15.Section02.Preliminaries.OmegaSourceQuotients
public import CFSG.Quasithin.Chapter15.Section02.SourceChosenCriticalPair.ResidualDirectAssembly

/-!
# The original chosen Omega contradiction without a global residual prior

The Omega overgroup theorem and direct wreath quotient theorem supply every
premise of the existing literal residual-input contradiction. This retains
both full and proper chosen modules and requires no 15.1.14 assumption.

Source: Aschbacher--Smith 15.2.5--8 and 15.2.27--28,
printed pp.1107--1110 and 1119--1120.
-/

public section
open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section02
open Section01 Section03 ChapterD ChapterD.UniqueFactor
variable {G : Type*} [Group G] [Finite G]

/-- The original full-or-proper Omega source is impossible without adding
any earlier global residual, quotient-recognition or plane premise. -/
theorem source_chosen_omega_contradiction
    {T : Sylow 2 G} {M Mc V : Subgroup G} (h : ChosenSmallSource T M Mc V)
    (ho : letI := h.prepared.elementary
      SourceCases.Omega (imageRepresentation M V h.prepared.normalized)) : False :=
  source_chosen_contradiction_of_wreath_quotients h (h.maximal_overgroups_of_omega ho)
    (h.HStar_wreath_of_omega ho)

end CFSG.Quasithin.Chapter15.Section02
