module
public import CFSG.Quasithin.ChapterE.Section02.ThompsonAction.LinearBlockSource.Nonsolvable
public import CFSG.Quasithin.ChapterE.Section02.ThompsonAction.SolvableBaumann
/-!
# Original-source block selection in the Baumann Sylow branch

The intrinsic linear-branch reduction and its nonsolvable specialization are
re-exported here. The solvable action-quotient consumer derives the required
Baumann Sylow conclusion from the original reduced module, so no block or
characteristic-control witness is supplied as an input.

Source: Aschbacher--Smith E.2.3(4), pp.216--217.
-/
public section
open Subgroup Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.ThompsonAction.LinearBlockSource
open ChapterB ChapterC
variable {G : Type*} [Group G] [Finite G]

/-- The original solvable action-quotient branch, retaining the possible A3 block. -/
theorem chiZero_block_of_solvable_action
    (hG : IsSQTK KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hP : IsMinimalParabolicOver T ⊤)
    (hf : generalizedFitting G = pCore 2 G)
    (U : Subgroup G) (hU : IsPReduced 2 U)
    (hJ : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (U : Set G))
    (hsolv : letI := hU.normal; Group.IsSolvable (G ⧸ centralizer (U : Set G)))
    (hno : ∀ C : Subgroup (baumann (T : Subgroup G)), C.Characteristic →
      (C.map (baumann (T : Subgroup G)).subtype).Normal → C = ⊥) :
    ∃ L : Subgroup G, IsChiZeroBlockIn L ∧
      L = ⁅L,elementaryAbelianMaxJ (T : Subgroup G)⁆ ∧
      L ⊔ (T : Subgroup G) = ⊤ ∧ ¬L ≤ minimalParabolicMax T hP := by
  exact chiZero_block_of_baumann_sylow hG T hP hf hno
    (source_solvable_baumann_sylow_and_alpha T hP U hU hJ
      (hG.stronglyQuasithin 3 (by decide) (by decide)) hsolv).1

end CFSG.Quasithin.ChapterE.ThompsonAction.LinearBlockSource
