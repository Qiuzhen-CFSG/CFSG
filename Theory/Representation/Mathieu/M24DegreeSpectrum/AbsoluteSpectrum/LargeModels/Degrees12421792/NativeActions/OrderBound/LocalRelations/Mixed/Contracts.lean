module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.OrderBound.LocalRelations.Contracts

/-!
# Two source inputs for the mixed max8 words

The cyclic trace reduces all six mixed identities to the first mixed identity
and the order-23 equation for `xyxyxy⁻¹`, with `x,y` the literal reversed max8
pair. These are explicit proof obligations in the original seven-relator group.
Source: John Bray's ATLAS M24G1-P1 and M24G1-max8W1; see `source/README.md`.
-/

@[expose] public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Presentation.OrderBound.LocalRelations.Mixed
open Subgroup.CosetWordCertificate

/-- The first of the six fixed mixed identities. -/
def FirstRelation : Prop := eval boundGenerator (localRelatorLetters 3) = 1

/-- A short word whose cyclic subgroup is used by the checked trace. -/
def cycleLetters : Word (Fin 2) :=
  [(0, true), (1, true), (0, true), (1, true), (0, true), (1, false)]

def cycleElement : UniversalGroup := eval boundGenerator cycleLetters

/-- This power equation must hold in the original abstract source group. -/
def CyclePowerRelation : Prop := cycleElement ^ 23 = 1

/-- The word is the specified product in the literal subgroup pair. -/
theorem cycleElement_eq : cycleElement =
    boundGenerator 0 * boundGenerator 1 * boundGenerator 0 * boundGenerator 1 *
      boundGenerator 0 * (boundGenerator 1)⁻¹ := by
  simp [cycleElement, cycleLetters, eval_cons, mul_assoc]

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Presentation.OrderBound.LocalRelations.Mixed
