module

public import Theory.SpecificGroups.SymplecticFour.LocalStructure.Nonbinary
public import Theory.SpecificGroups.SymplecticFour.LocalStructure.ParabolicCores
public import CFSG.Quasithin.ChapterF.Section01.GreenBook.LieModels.SymplecticFour.Blocks

/-!
# Residual data for the nonbinary `Sp₄` parabolics

This file records the concrete residual and core information used when a
marked `Sp₄(2^m)` model is pulled back to the source group.  Every subgroup in
the statements is one of the literal point or plane parabolics; in particular
the residual is embedded with the corresponding subtype map.  The quotient
statements use the natural extensions, so no splitting of either parabolic is
being assumed.

Source: Aschbacher--Smith, F.1.12(I)(2), printed pp.262--264, and the
maximal-parabolic step in 13.6.19, printed pp.930--931.
-/

@[expose] public section
noncomputable section
namespace Theory.SpecificGroups.SymplecticFour

open Subgroup
open CFSG.Quasithin.ChapterF.GreenBook.LieModels.SymplecticFour
open CFSG.Quasithin.ChapterC

variable {F : Type} [Field F] [Finite F] [CharP F 2]
variable {n : ℕ} (hcard : Nat.card F = 2 ^ n) (hn : 1 < n)

/-- The defining `Sp₄` block predicate exposes an actual quotient model.  In
particular, the model is not merely the name of a group family: its
equivalence is the quotient isomorphism carried by the concrete module
model. -/
theorem isSp4FourBlock_quotient_model {L : Type*} [Group L]
    (h : CFSG.Quasithin.ChapterC.IsSp4FourBlock L) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F),
      Nat.card F = 4 ∧
      Nonempty ((L ⧸ pCore 2 L) ≃* Sp F) := by
  rcases h with ⟨_, F, _, _, hF, rho, ⟨model⟩, _⟩
  exact ⟨F, inferInstance, inferInstance, hF, ⟨model.quotientIso⟩⟩

include hcard hn

/-- The point-parabolic residual, viewed in the ambient symplectic group. -/
abbrev pointResidual : Subgroup (Sp F) :=
  (solvableResidual (pointParabolic (F := F))).map pointParabolic.subtype

/-- The plane-parabolic residual, viewed in the ambient symplectic group. -/
abbrev planeResidual : Subgroup (Sp F) :=
  (solvableResidual (planeParabolic (F := F))).map planeParabolic.subtype

theorem pointResidual_eq_local : pointResidual (F := F) = pointLocal := by
  exact pointParabolic_solvableResidual_eq hcard hn

theorem planeResidual_eq_local : planeResidual (F := F) = planeLocal := by
  exact planeParabolic_solvableResidual_eq hcard hn

theorem pointResidual_relative :
    solvableResidual (pointParabolic (F := F)) =
      (pointLocal (F := F)).subgroupOf pointParabolic := by
  exact pointParabolic_solvableResidual_relative hcard hn

theorem planeResidual_relative :
    solvableResidual (planeParabolic (F := F)) =
      (planeLocal (F := F)).subgroupOf planeParabolic := by
  exact planeParabolic_solvableResidual_relative hcard hn

theorem pointResidual_core_map :
    (pCore 2 (pointParabolic (F := F))).map pointParabolic.subtype =
      (pointRadical (F := F)).map pointLocal.subtype := by
  exact pointParabolic_core_map_eq_radical hcard hn

theorem planeResidual_core_map :
    (pCore 2 (planeParabolic (F := F))).map planeParabolic.subtype =
      (Plane.radical (F := F)).map planeLocal.subtype := by
  exact planeParabolic_core_map_eq_radical hcard hn

/-- The literal core quotient is the projective rank-one group required by
13.6.19.  The displayed equivalence is the one induced by the concrete
natural extension, rather than a family tag. -/
theorem pointLocal_core_quotient_isPSL :
    ClassicalGroup.IsPSL
      (pointLocal (F := F) ⧸ pCore 2 (pointLocal (F := F))) 2 (2 ^ n) := by
  exact isPSL_of_specialLinearEquiv hcard
    (pointLocalCoreQuotientEquiv hcard hn)

theorem planeLocal_core_quotient_isPSL :
    ClassicalGroup.IsPSL
      (planeLocal (F := F) ⧸ pCore 2 (planeLocal (F := F))) 2 (2 ^ n) := by
  exact isPSL_of_specialLinearEquiv hcard
    (planeLocalCoreQuotientEquiv hcard hn)

theorem pointResidual_isL2EvenBlock :
    IsL2EvenBlock (pointResidual (F := F)) n := by
  rw [pointResidual_eq_local hcard hn]
  exact pointLocal_isL2EvenBlock hcard hn

theorem planeResidual_isL2EvenBlock :
    IsL2EvenBlock (planeResidual (F := F)) n := by
  rw [planeResidual_eq_local hcard hn]
  exact planeLocal_isL2EvenBlock hcard hn

end Theory.SpecificGroups.SymplecticFour
end
