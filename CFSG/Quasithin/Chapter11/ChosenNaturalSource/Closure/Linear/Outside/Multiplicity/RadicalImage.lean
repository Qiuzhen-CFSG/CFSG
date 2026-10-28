module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Linear.Outside.Multiplicity.RadicalImage.Comparison

/-!
# The original radical lies in the multiplicity-action kernel

The source point is a genuine field line in the given natural SL₃ action.
The original solvable residual and its actual outer action give the radical
comparison modulo O₂(LT). With the authorized SL₃ block outputs and T_L
splitting, the existing Sylow argument now needs no radical-image premise.

Source: Aschbacher--Smith, 11.5.7, printed pp.781--782. The block structure,
two-copy marking and splitting remain the separate block owner's outputs.
-/

public noncomputable section
open Subgroup Representation
open CFSG.Quasithin.Chapter12.Section02 CFSG.Quasithin.ChapterB.QuasisimpleSource
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Linear.Outside
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {D : ChosenModule T L V} (E : Geometry D)

/-- Apply the source radical comparison to the literal W/V₁ action.
The former `himage` premise is discharged through the actual projective action. -/
theorem radical_le_actionCentralizer_of_source
    (m : ActionEquiv D.centralQuotientAction (linearNatural E.input.field 3))
    (n : NaturalPair E)
    (P : Submodule E.input.field.Carrier (Fin 3 → E.input.field.Carrier))
    (hdim : Module.finrank E.input.field.Carrier P = 1)
    (hpoint : E.point = (LocalGeometry.Coordinates.sl3 m).binarySubspace P)
    (hTG : (T : Subgroup G) ≤ E.G₁) (hKL : E.K = E.L₁)
    (hCG : C E ≤ E.G₁) (hWK : E.W = E.K.pCoreIn 2)
    (hLV : L.pCoreIn 2 = V)
    (hsplit : LocalGeometry.sourceTL T L = ((T : Subgroup G) ⊓ L) ⊔
      ((T : Subgroup G) ⊓ centralizer (L : Set G))) :
    E.R₁.subgroupOf (C E) ≤ actionCentralizer E (C E) hCG := by
  have hWL : E.W ≤ L := by rw [hWK,hKL]; exact (pCoreIn_le 2 E.L₁).trans E.L₁_le
  exact radical_le_actionCentralizer E n hCG hWK hWL hLV
    (RadicalImage.radical_le_closure_join_core E m n P hdim hpoint hTG hKL hWK) hsplit

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Linear.Outside
