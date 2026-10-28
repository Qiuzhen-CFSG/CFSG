module

public import CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.ExceptionalAction.Recognition.ActionRecognition.OrdinaryExclusions.G2.Actor
public import Theory.GroupTheory.SylowKernelCore
public import Theory.GroupTheory.PResidual.FiniteImage

/-!
# The marked first residual inside the actual offender actor

Restricting the image of Y_F to the offender actor loses no elements.
Its intrinsic two-core is exactly the marked core used in the source
fixed-space argument. The source residual identity also survives the
literal core projection. These transports isolate the subgroup-recognition
obligation from the independent natural-coordinate calculation.

Source: Aschbacher–Smith, final proof of 15.3.1, printed p.1155.
-/

@[expose] public section

open Subgroup Representation.BinaryOffender
open scoped IsMulCommutative

namespace CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.ExceptionalAction.ActionRecognition.OrdinaryExclusions.G2.LocalCalculation

variable {H : Type*} [Group H] [Finite H] {V : Subgroup H}
  [IsElementaryAbelian 2 (moduleClosure V)] (d : SourceInput V)

/-- The actual first local factor, restricted along its proved containment
in the offender actor. -/
noncomputable abbrev markedFactor : Subgroup d.offenderGroup :=
  (d.YF.map coreProjection).subgroupOf d.offenderGroup

/-- Inclusion into the quotient recovers the original first factor. -/
theorem markedFactor_map :
    (markedFactor d).map d.offenderGroup.subtype = d.YF.map coreProjection :=
  map_subgroupOf_eq_of_le d.first_image_le

/-- Taking the core commutes with this faithful restriction. -/
theorem firstCore_eq_factorCore : d.firstCoreInOffender = (markedFactor d).pCoreIn 2 := by
  apply map_injective d.offenderGroup.subtype_injective
  rw [d.firstCoreInOffender_map, map_pCoreIn_of_injective 2 _ _
    d.offenderGroup.subtype_injective, markedFactor_map]

/-- The marked factor is still the literal two-residual of the first
local image after quotienting by the global two-core. -/
theorem markedFactor_map_eq_residual :
    (markedFactor d).map d.offenderGroup.subtype =
      (pResidual 2 (d.G1.map coreProjection)).map (d.G1.map coreProjection).subtype := by
  rw [markedFactor_map, ← map_embedded_pResidual, d.first_residual]

end CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.ExceptionalAction.ActionRecognition.OrdinaryExclusions.G2.LocalCalculation
