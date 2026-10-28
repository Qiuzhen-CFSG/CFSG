module
public import CFSG.Quasithin.ChapterE.Section02.ThompsonAction.PairResidualImages
public import Theory.SpecificGroups.SymmetricFiveProduct.AlternatingCentralizers

/-!
# Centralizers of the original paired residual images

Under the same marked product as E.2.3, the image of either original
factor residual is its alternating axis. Its centralizer inside the
actual offender subgroup is exactly the other full symmetric factor.
The literal quotient map, offender subgroup, and factor inclusions are
retained in these identities.

Source: Aschbacher–Smith E.2.3 and 10.2.1, pp.216–217 and742–743.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterE.ThompsonAction
open ChapterB ChapterB.SourceInduction
variable {G H : Type*} [Group G] [Finite G] [Group H] [Finite H]
  {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) H V) (q : G →* H) (hq : Function.Surjective q)
  (d : SourceTwoFactorCase (ρ.comp (offenderSubgroup ρ).subtype))
  (c : d.MarkedProduct (BinaryPermutation.naturalRepresentation (Fin 5)))

include hq c in
theorem paired_symmetric_first_residual_centralizer :
    offenderSubgroup ρ ⊓ centralizer
      ((factorResidual q (offenderSubgroup ρ) d.first).map q : Set H) =
      d.second.map (offenderSubgroup ρ).subtype := by
  rw [paired_symmetric_first_residual_image ρ q hq d c,
    Theory.SymmetricFiveProduct.marked_left_alternating_centralizer,
    ←Subgroup.map_map,c.second_eq]

include hq c in
theorem paired_symmetric_second_residual_centralizer :
    offenderSubgroup ρ ⊓ centralizer
      ((factorResidual q (offenderSubgroup ρ) d.second).map q : Set H) =
      d.first.map (offenderSubgroup ρ).subtype := by
  rw [paired_symmetric_second_residual_image ρ q hq d c,
    Theory.SymmetricFiveProduct.marked_right_alternating_centralizer,
    ←Subgroup.map_map,c.first_eq]

end CFSG.Quasithin.ChapterE.ThompsonAction
