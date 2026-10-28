module
public import CFSG.Quasithin.Chapter14.Section04.CaseOneHS.LocalStructure.SourceAction.SolvableFour
public import CFSG.Quasithin.ChapterG.Section11.FourResidual

/-!
# The actual A₅ residual of the original four-dimensional HS action

The checked six-letter embedding omits A₆, and the original dotted group
is nonsolvable. Its solvable residual is therefore an actual A₅, acting
irreducibly on U/Z(U). The field-four module theorem supplies the two
possible actions with their literal equivariant coordinates.

NaturalResidual selects the natural action; NaturalOrder and FourCoordinates
extend its coordinates to the whole dotted group. The whole-component
branch remains open. The preceding centerlessness premise belongs to
qt-d-hs-local-structure.
Source: Aschbacher--Smith 14.3.23(2) and 14.3.32, pp.1000,1003--1004.
-/

public noncomputable section
open Subgroup Module Representation Theory.GroupTheory
open scoped IsMulCommutative MatrixGroups
local instance : Algebra (ZMod 2) (OrthogonalFourMinus.FiniteModel.Field 1) :=
  ZMod.algebra _ 2
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneHS
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter14.Section03.CaseOneSource
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
variable (d : Counterexample T L) (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U) (hZ : F.ZU ≠ F.Vi 1)
    (hI : Chapter12.Section08.centerIn (F.I₂ L) = ⊥)
include d earlier hq chosen structural alternatives hne hZ hI

/-- The exact solvable residual of the original dotted four-space is A₅. -/
theorem source_four_residual_alternatingFive (hc : Nat.card F.Uhat = 16) :
    Nonempty (solvableResidual F.TerminalHdot ≃* alternatingGroup (Fin 5)) := by
  obtain ⟨_,_,j,hj,_,ha⟩ := source_four_symplectic_embedding_of_centerless
    d earlier hq chosen structural alternatives F hne hZ hI hc
  exact Theory.SpecificGroups.SymmetricSix.residual_equiv_alternatingFive j hj
    (source_terminal_not_solvable_of_centerless d earlier hq chosen structural alternatives
      F hne hZ hI) ha

/-- The original four-space actor has order sixty or one hundred twenty. -/
theorem source_four_card_sixty_or_oneTwenty (hc : Nat.card F.Uhat = 16) :
    Nat.card F.TerminalHdot = 60 ∨ Nat.card F.TerminalHdot = 120 := by
  obtain ⟨_,_,j,hj,_,ha⟩ := source_four_symplectic_embedding_of_centerless
    d earlier hq chosen structural alternatives F hne hZ hI hc
  exact Theory.SpecificGroups.SymmetricSix.card_eq_sixty_or_oneTwenty j hj
    (source_terminal_not_solvable_of_centerless d earlier hq chosen structural alternatives
      F hne hZ hI) ha

/-- Literal natural/deleted coordinates on the original normal residual. -/
theorem source_four_residual_action_alternatives (hd : finrank (ZMod 2) (Additive F.Uhat) = 4) :
    (∃ e : solvableResidual F.TerminalHdot ≃* SL(2,OrthogonalFourMinus.FiniteModel.Field 1),
      Nonempty (Representation.Equiv (F.terminalRepresentation.comp (solvableResidual F.TerminalHdot).subtype)
        (SL2.BinarySmall.natural.comp e.toMonoidHom))) ∨
    (∃ e : solvableResidual F.TerminalHdot ≃* alternatingGroup (Fin 5),
      Nonempty (Representation.Equiv (F.terminalRepresentation.comp (solvableResidual F.TerminalHdot).subtype)
        (OrthogonalFourMinus.AlternatingFive.alternatingRepresentation.comp e.toMonoidHom))) := by
  have hc : Nat.card F.Uhat = 16 := by
    have hh := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive F.Uhat)
    change Nat.card F.Uhat = _ at hh
    simpa only [Nat.card_zmod,hd,show (2 : ℕ)^4=16 by decide] using hh
  obtain ⟨_,_,j,hj,_,ha⟩ := source_four_symplectic_embedding_of_centerless
    d earlier hq chosen structural alternatives F hne hZ hI hc
  exact ChapterG.Section11.FourResidual.action_alternatives F.terminalRepresentation
    F.terminalRepresentation_injective hd j hj
    (source_terminal_not_solvable_of_centerless d earlier hq chosen structural alternatives
      F hne hZ hI) ha

end CFSG.Quasithin.Chapter14.Section04.CaseOneHS
