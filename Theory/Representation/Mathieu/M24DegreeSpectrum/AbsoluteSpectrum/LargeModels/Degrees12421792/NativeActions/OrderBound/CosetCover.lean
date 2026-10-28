module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.OrderBound.CosetCover.PointSchreier
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.OrderBound.CosetCover.NativeLower
public import Theory.GroupTheory.PresentedGroupBounds.IndexCover

/-!
# The max8 cover from a smaller Schreier order problem

The seven source relators give an actual 24-coset cover by the subgroup
presented in `PointSchreier`. A finite bound of 10200960 for that independent
presentation would therefore bound the ambient group by 244823040. The literal
max8 subgroup has at least 6072 elements, as its marked permutation image is
transitive of degree 24 and contains elements of orders 11 and 23. Lagrange's
theorem then bounds its index by 40320; a section of the coset quotient supplies
actual subgroup-witness equations for both signed transitions.

The smaller presentation bound is still an explicit, unproved premise here.
These declarations do not assert the requested unconditional cover, and do not
use the ambient order bound or faithfulness as assumptions. The remaining
premise must be established before defining `boundCosetCover`.

Sources: ATLAS M24G1-P1 and M24G1-max8W1. See `CosetCover/source/README.md`.
-/

@[expose] public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Presentation.OrderBound

private theorem index_arithmetic (n : ℕ) (h : n * 6072 ≤ 244823040) : n ≤ 40320 := by
  omega

/-- Concrete index application to the literal source subgroup. The remaining
finite-order premise concerns the independent 25-generator Schreier group. -/
theorem boundSubgroup_index_le_of_pointBound
    (hpoint : Finite CosetCover.PointSchreier.Presented ∧
      Nat.card CosetCover.PointSchreier.Presented ≤ 10200960) :
    boundSubgroup.index ≤ 40320 := by
  have hG := CosetCover.PointSchreier.ambient_bound_of_presented_bound hpoint
  let : Finite UniversalGroup := hG.1
  have hl := CosetCover.NativeLower.boundSubgroup_card_ge
  have hu := (Nat.mul_le_mul_left boundSubgroup.index hl).trans
    (boundSubgroup.index_mul_card.le.trans hG.2)
  exact index_arithmetic _ hu

/-- The final assembly of the alternative route, retaining its one outstanding
order problem rather than asserting it as a fact. -/
noncomputable def boundCosetCover_of_pointBound
    (hpoint : Finite CosetCover.PointSchreier.Presented ∧
      Nat.card CosetCover.PointSchreier.Presented ≤ 10200960) :
    Subgroup.GeneratorCosetCover boundSubgroup generator (Fin 40320) := by
  let : Finite UniversalGroup :=
    (CosetCover.PointSchreier.ambient_bound_of_presented_bound hpoint).1
  exact Subgroup.GeneratorCosetCover.of_index_le boundSubgroup generator 40320
    (boundSubgroup_index_le_of_pointBound hpoint)

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Presentation.OrderBound
