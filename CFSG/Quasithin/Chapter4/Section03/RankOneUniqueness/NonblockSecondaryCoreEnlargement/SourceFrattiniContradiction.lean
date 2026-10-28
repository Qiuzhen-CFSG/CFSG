module

public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockSecondaryCoreEnlargement.SourceCoreFrattiniFixed
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockGraphAdjointApplication

/-!
# The marked Frattini fixed-point contradiction

The original component-core Frattini quotient has at most sixteen fixed
points under the selected cubic.  A fully marked ordinary adjoint extension
with a split diagonal cubic has at least 256.  This module assembles those
two checked bounds on the same literal quotient and the same literal action.

The split diagonal actor is retained as an explicit source premise.  The
available projective-diagonal predicate gives only inner-diagonal membership;
it does not imply this split normal form.
-/

public noncomputable section
open Matrix Subgroup Representation
open scoped MatrixGroups
open Representation.SL3.AdjointCubicCentralizer
open Representation.SL3.AdjointCubicCentralizer.GraphExtension
open Representation.SL3.AdjointCubicCentralizer.GraphExtension.FrattiniDescent
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock.SourceEndgame
attribute [local instance] ZMod.algebra SecondaryActionData.normal SecondarySourceData.normal
set_option linter.style.haveILetI false
variable {G F : Type*} [Group G] [Finite G] [Field F] [Finite F] [CharP F 2]
  {T : Sylow 2 G} {L V : Subgroup G} {c : SourceConfiguration T L}

/-- The literal upper and lower fixed-point bounds are incompatible once the
source cubic actor is supplied in split diagonal form. -/
theorem marked_frattini_false_of_split_diagonal
    {d : MSData c 2} (m : Nonblock.RootCoordinates d)
    (D : Chapter12.Section02.ChosenModule T L V)
    (s : SecondarySourceData c 2)
    (X : Subgroup G) (hX3 : Nat.card X = 3)
    (hXK : X ≤ (K c).coreCenterIn 2) (hXr : X ≤ rootNormalizer c)
    (hfix : Q c ⊓ Subgroup.centralizer (X : Set G) = ⊥)
    (dF : SourceFrattiniGraphData (F := F) s X)
    (hF : Nat.card F = 4) (x : X) (hx : x ≠ 1) (ω : Fˣ)
    (hdiag : dF.projection (sourceCubicInclusion s X hXr x) =
      ProjGenLinGroup.mk (diagonalUnit F ω)) : False := by
  have hcomponent : s.toActionData.component = s.component := rfl
  cases hcomponent
  let actionUpper : MulDistribMulAction X (Frattini s.component) :=
    MulDistribMulAction.compHom _ ((coreAction s.component).comp (inclusion hXr))
  let actionLower : MulDistribMulAction X (Frattini s.component) :=
    MulDistribMulAction.compHom _ ((coreAction s.component).comp
      ((cubicExtension s X).subtype.comp (sourceCubicInclusion s X hXr)))
  have hcomp :
      (cubicExtension s X).subtype.comp (sourceCubicInclusion s X hXr) =
        inclusion hXr := by
    ext y
    rfl
  have hcore : coreAction s.toActionData.component = coreAction s.component := rfl
  have hact : actionLower = actionUpper := by
    apply MulDistribMulAction.ext
    funext a v
    change (coreAction s.component)
        (((cubicExtension s X).subtype.comp (sourceCubicInclusion s X hXr)) a) v =
      (coreAction s.component) (inclusion hXr a) v
    rw [hcomp]
  let U : Subgroup (Frattini s.component) := by
    letI := actionUpper
    exact FixedPoints.subgroup X (Frattini s.component)
  let L : Subgroup (Frattini s.component) := by
    letI := actionLower
    exact FixedPoints.subgroup X (Frattini s.component)
  have hu : Nat.card U ≤ 16 := by
    letI := actionUpper
    have hu0 :=
      SourceActionEndgame.component_frattini_fixed_card_le m D s.toActionData X hX3 hXK hXr hfix
    dsimp at hu0
    simp only [SecondarySourceData.toActionData] at hu0
    rw [hcore] at hu0
    change Nat.card (FixedPoints.subgroup X (Frattini s.component)) ≤ 16
    exact hu0
  have hl : 256 ≤ Nat.card L := by
    letI := actionLower
    have hl0 := source_frattini_fixed_card_ge s X hX3 hXr dF hF x hx ω hdiag
    change 256 ≤ Nat.card (FixedPoints.subgroup X (Frattini s.component))
    exact hl0
  have hUL : U = L := by
    dsimp [U, L]
    rw [hact]
  have hl' : 256 ≤ Nat.card U := by simpa [hUL] using hl
  omega

end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock.SourceEndgame
