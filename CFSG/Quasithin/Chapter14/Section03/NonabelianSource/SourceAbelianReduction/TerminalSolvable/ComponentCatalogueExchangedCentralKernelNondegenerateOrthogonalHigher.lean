module
public import Theory.SpecificGroups.ClassicalOrthogonal.BinaryHigherResidual
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.ComponentCatalogueExchangedCentralKernelNondegenerateOrthogonalCenter

/-!
# Complete orthogonal exclusion for the exchanged central-kernel constituent

In dimension at least eight the actual orthogonal residual has cubic rank
at least three. Source irreducibility kills its center, so the literal
constituent map transports the original odd-rank bound and gives a contradiction.
Together with the checked degree-four and degree-six arguments this excludes
every orthogonal constituent, with no model or rank premise.

The faithful-constituent assembly now retains only transitive G.12 recognition
in degree at least six. That obligation remains with
`qt-e-14315-exchanged-central-kernel`; final exchanged-image assembly remains
with `qt-e-14315-component-exchanged-images`.
Source: Aschbacher--Smith G.10.15, printed p.363.
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

/-- The actual higher orthogonal residual contradicts the original cubic-rank bound. -/
theorem false_of_orthogonal_ge_eight
    (hnd : (B.restrict I).Nondegenerate) (hd : 8≤finrank (ZMod 2) I)
    (q : QuadraticForm (ZMod 2) I) (hq : q.polarBilin=B.restrict I)
    (heq : s.constituentLinearAction.range =
      ChapterG.Section12.embeddedResidual q.isometrySubgroup) : False :=
  s.false_of_orthogonal_rank_three hnd q hq heq
    (QuadraticForm.BinaryHigherCoordinates.residual_rank_ge_three q (hq.symm ▸ hnd) hd)

/-- All orthogonal source alternatives are excluded on the selected constituent. -/
theorem false_of_orthogonal
    (hnd : (B.restrict I).Nondegenerate)
    (q : QuadraticForm (ZMod 2) I) (hq : q.polarBilin=B.restrict I)
    (heq : s.constituentLinearAction.range =
      ChapterG.Section12.embeddedResidual q.isometrySubgroup) : False := by
  by_cases h4 : finrank (ZMod 2) I=4
  · exact s.not_nondegenerate_four h4 hnd
  by_cases h6 : finrank (ZMod 2) I=6
  · exact s.false_of_orthogonal_six hnd q hq heq h6
  obtain ⟨n,hn⟩ := AlternatingForm.even_finrank (B.restrict I)
    (fun w => s.hypothesis.alternating w) hnd
  have hd := s.dimension_gt_two
  exact s.false_of_orthogonal_ge_eight hnd (by omega) q hq heq

/-- The literal faithful constituent assembly, with the complete orthogonal
family discharged. The sole remaining premise is retained by this source owner. -/
theorem faithful_data_of_transitive_recognition
    (htransitive : 6 ≤ finrank (ZMod 2) I →
      ∀ u i : I, ChapterG.Section12.ClassificationHypotheses
        s.constituentGeneratedImage (B.restrict I) u i →
        (∀ x : I,x≠0 → ∃ a∈s.constituentGeneratedImage,a i=x) →
        ChapterG.Section12.ResidualModel
          (ChapterG.Section12.embeddedResidual s.constituentGeneratedImage) (B.restrict I)) :
    ExchangedFaithfulConstituentData F.terminalRepresentation B L
      (F.terminalDot (F.X g)) I s.selected := by
  apply s.faithful_data_of_higher_transitive_orthogonal htransitive
  intro hnd _ q hq heq
  exact s.false_of_orthogonal hnd q hq heq

end ExchangedCentralSource
end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
