module
public import CFSG.Quasithin.Chapter3.Section01.ChiefAction.SeedOffender
/-!
# Literal residual comparison with the essential source actor

In the nonsolvable original minimal parabolic, every irreducible FF action
has the canonical core as its kernel. This applies both to each original
chief factor and to the essential seed action. The same original subgroup
therefore maps into the two-residual in one action exactly when it does in
the other. Possible odd parts of the common kernel are retained.

Source: Aschbacher–Smith3.1.9(5), printed p.578.
-/
public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory NoncentralChiefRefinement Stellmacher
open scoped IsMulCommutative ENNReal
universe u
namespace CFSG.Quasithin.Chapter3
open ChapterB ChapterD ChapterD.UniqueFactor
variable {G : Type u} [Group G] [Finite G] {H V : Subgroup G}
  [IsElementaryAbelian 2 ((conjugateSpan H V).subgroupOf H)]
  {S : Sylow 2 H} {hVH : V ≤ H}

theorem EssentialSeedAction.kernel_eq_core
    (a : EssentialSeedAction H V S hVH)
    (hD : IsSQTK KnownSimple.IsKnownSimple H) (hs : ¬ Group.IsSolvable H)
    (hff : IsFFModule a.imageRepresentation) :
    a.representation.ker = minimalParabolicCore S a.original_minimal := by
  let := a.irreducible
  exact minimalParabolic_nonsolvable_chief_kernel a.representation hD S a.original_minimal hs hff

theorem EssentialSeedAction.chief_residual_membership_iff
    (a : EssentialSeedAction H V S hVH)
    (hD : IsSQTK KnownSimple.IsKnownSimple H) (hs : ¬ Group.IsSolvable H)
    (hff : IsFFModule a.imageRepresentation)
    (s : SeriesOn ((conjugateSpan H V).subgroupOf H)) (i : Fin s.series.length)
    (hsi : IsFFModule (Representation.BinaryOffender.imageRepresentation (s.factorRepresentation i)))
    (A : Subgroup H) :
    actionSubgroup (s.factorRepresentation i) A ≤
        pResidual 2 (actionImage (s.factorRepresentation i)) ↔
      A.map a.projection ≤ pResidual 2 a.Actor := by
  let := s.factorRepresentation_irreducible i
  apply actionSubgroup_residual_iff_of_kernel_eq
  exact (minimalParabolic_nonsolvable_chief_kernel (s.factorRepresentation i)
    hD S a.original_minimal hs hsi).trans (a.kernel_eq_core hD hs hff).symm
end CFSG.Quasithin.Chapter3
