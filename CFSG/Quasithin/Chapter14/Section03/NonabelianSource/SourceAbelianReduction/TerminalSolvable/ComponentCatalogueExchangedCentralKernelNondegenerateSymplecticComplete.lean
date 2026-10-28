module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.ComponentCatalogueExchangedCentralKernelNondegenerateSymplecticFourModel
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.ComponentCatalogueExchangedCentralKernelFullLinearComplete
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.ComponentCatalogueExchangedCentralKernelNondegenerateNatural

/-!
# Complete symplectic exclusion and the remaining central-kernel inputs

The degree-four residual is excluded by the actual order-eight actor and its
marked A6 module. Higher degrees are excluded by the source cubic-rank bound.
The full-linear exclusion supplies properness, so no local model or degree
callback remains in the symplectic branch. Together with the natural SL2(4)
exclusion this leaves precisely G.12 residual recognition and the orthogonal
row for the final central-kernel assembly.

This module does not prove those last two premises. Their construction and
final discharge remain with `qt-e-14315-exchanged-central-kernel`, whose
parent consumer is `qt-e-14315-component-exchanged-images`.

Source: Aschbacher--Smith G.10.15, printed p.363, in the original
14.3.12--15 source configuration, printed pp.993--994.
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

/-- The symplectic residual row is impossible under the original exchanged
central-kernel hypotheses, in every possible constituent dimension. -/
theorem false_of_symplectic
    (hnd : (B.restrict I).Nondegenerate)
    (heq : s.constituentLinearAction.range = ChapterG.Section12.embeddedResidual
      (ChapterG.Section12.formStabilizer (B.restrict I))) : False := by
  obtain ⟨n,hn⟩ := AlternatingForm.even_finrank (B.restrict I)
    (fun w => s.hypothesis.alternating w) hnd
  by_cases hd : finrank (ZMod 2) I = 4
  · exact s.false_of_symplectic_four s.not_fullLinear hnd heq hd
  · exact s.false_of_symplectic_higher hnd heq (by have := s.dimension_gt_two; omega)

/-- The literal faithful constituent consumer now retains only G.12 recognition
and the orthogonal source exclusion. Those premises are not discharged here. -/
theorem faithful_data_of_recognition_orthogonal
    (hrecognition : ∀ u i : I, ChapterG.Section12.ClassificationHypotheses
      s.constituentGeneratedImage (B.restrict I) u i →
      ChapterG.Section12.ResidualModel
        (ChapterG.Section12.embeddedResidual s.constituentGeneratedImage) (B.restrict I))
    (horthogonal : (B.restrict I).Nondegenerate →
      ∀ q : QuadraticForm (ZMod 2) I, q.polarBilin = B.restrict I →
        s.constituentLinearAction.range = ChapterG.Section12.embeddedResidual
          q.isometrySubgroup → False) :
    ExchangedFaithfulConstituentData F.terminalRepresentation B L
      (F.terminalDot (F.X g)) I s.selected :=
  s.faithful_data_of_not_nondegenerate
    (s.not_nondegenerate_of_classical_model_inputs s.not_fullLinear hrecognition
      s.false_of_symplectic horthogonal)

end ExchangedCentralSource
end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
