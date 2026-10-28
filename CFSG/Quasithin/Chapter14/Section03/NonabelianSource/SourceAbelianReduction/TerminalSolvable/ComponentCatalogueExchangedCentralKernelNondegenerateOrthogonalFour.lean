module
public import Theory.LinearAlgebra.QuadraticForm.BinaryFourSolvable
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.ComponentCatalogueExchangedCentralKernelNondegenerate

/-!
# Excluding the plus-type orthogonal four-space

The actual H-image on the selected Irr+ constituent is nontrivial. In binary
dimension four, a totally singular plane identifies the full orthogonal group
with the solvable plus model, whose embedded solvable residual is trivial.
Its literal equality with the constituent image is therefore impossible.

No faithfulness, centerlessness or identification of the two-residual with
the solvable residual is assumed. The other orthogonal rows remain with
`qt-e-14315-exchanged-central-kernel`; final exchanged-image assembly remains
with `qt-e-14315-component-exchanged-images`.

Source: Aschbacher--Smith G.10.15, p.363, and G.12.1(2), p.370.
-/

public noncomputable section
open Subgroup Module Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section02 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open scoped IsMulCommutative
namespace ExchangedCentralSource
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {M Mc : Subgroup G}
  {F : InvariantFlag T (rankTwoSeed T M) 2}
  [IsElementaryAbelian 2 (rankTwoSeed T M)] [IsElementaryAbelian 2 F.Uhat]
  {g : G} [IsElementaryAbelian 2 (F.terminalDot (F.X g))]
  {B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)} {v : Additive F.Uhat}
  {L : Subgroup F.TerminalHdot} {I : Submodule (ZMod 2) (Additive F.Uhat)}
  (s : ExchangedCentralSource T M Mc F g B v L I)

include s

/-- Selection in Irr+ rules out a trivial literal constituent image. -/
theorem constituentImage_ne_bot : s.constituentLinearAction.range ≠ ⊥ := by
  intro he
  apply s.selected.isIrrPlus.not_le_fixedSpace F.terminalRepresentation
  intro w hw a
  have hact : s.constituentLinearAction a = 1 := by
    apply Subgroup.mem_bot.mp
    rw [← he]
    exact ⟨a,rfl⟩
  exact congrArg (fun f : I ≃ₗ[ZMod 2] I => (f ⟨w,hw⟩ : Additive F.Uhat)) hact

/-- The plus-four orthogonal residual cannot be the same selected action. -/
theorem false_of_orthogonal_four_plus
    (hnd : (B.restrict I).Nondegenerate)
    (q : QuadraticForm (ZMod 2) I) (hq : q.polarBilin = B.restrict I)
    (heq : s.constituentLinearAction.range =
      ChapterG.Section12.embeddedResidual q.isometrySubgroup)
    (hd : finrank (ZMod 2) I = 4)
    (U : Submodule (ZMod 2) I) (hU : finrank (ZMod 2) U = 2)
    (hs : ∀ u ∈ U, q u = 0) : False := by
  apply s.constituentImage_ne_bot
  rw [heq]
  exact QuadraticForm.BinaryFour.residual_eq_bot_of_singular_plane q
    (hq.symm ▸ hnd) hd U hU hs

end ExchangedCentralSource
end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
