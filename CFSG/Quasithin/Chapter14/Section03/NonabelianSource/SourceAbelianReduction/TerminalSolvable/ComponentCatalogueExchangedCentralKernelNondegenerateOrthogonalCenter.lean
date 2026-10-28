module
public import Theory.LinearAlgebra.BinaryReflectionCenter
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.ComponentCatalogueExchangedCentralKernelNondegenerateOrthogonalSix

/-!
# Centerlessness of the actual orthogonal constituent residual

The original constituent image is irreducible. A nonsingular reflection
normalizes the full orthogonal residual. Its rank-one action therefore kills
the residual center in dimension greater than two. The central constituent
kernel is then trivial, and the original terminal odd-rank bounds transport
to this exact orthogonal residual.

Thus the remaining higher-dimensional orthogonal exclusion needs only a
cubic-rank witness; centerlessness is discharged from the original source.
That witness and transitive G.12 recognition remain obligations of
qt-e-14315-exchanged-central-kernel. Final exchanged-image assembly remains
with qt-e-14315-component-exchanged-images.

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

/-- Source irreducibility and a full orthogonal reflection kill the center
of the literal constituent image, in every permitted dimension. -/
theorem constituentImage_centerless_of_orthogonal
    (hnd : (B.restrict I).Nondegenerate)
    (q : QuadraticForm (ZMod 2) I) (hq : q.polarBilin=B.restrict I)
    (heq : s.constituentLinearAction.range =
      ChapterG.Section12.embeddedResidual q.isometrySubgroup) :
    center s.constituentLinearAction.range=⊥ := by
  have hi : ChapterG.Section12.Irreducible
      (ChapterG.Section12.embeddedResidual q.isometrySubgroup) := by
    rw [← heq]
    exact s.constituentImage_irreducible
  rw [heq]
  exact BinaryReflectionCenter.center_orthogonal_residual_eq_bot q
    (hq.symm ▸ hnd) s.dimension_gt_two hi

/-- The source odd-rank bound holds for the exact recognized orthogonal
residual without an additional center or faithfulness hypothesis. -/
theorem orthogonal_residual_odd_primeRank_le_two
    (hnd : (B.restrict I).Nondegenerate)
    (q : QuadraticForm (ZMod 2) I) (hq : q.polarBilin=B.restrict I)
    (heq : s.constituentLinearAction.range =
      ChapterG.Section12.embeddedResidual q.isometrySubgroup)
    (p : ℕ) [Fact p.Prime] (hp : Odd p) :
    primeRank p (ChapterG.Section12.embeddedResidual q.isometrySubgroup) ≤ 2 := by
  rw [← heq]
  exact s.constituentImage_odd_primeRank_le_two
    (s.constituentImage_centerless_of_orthogonal hnd q hq heq) p hp

/-- A cubic-rank witness alone now excludes the orthogonal residual. -/
theorem false_of_orthogonal_rank_three
    (hnd : (B.restrict I).Nondegenerate)
    (q : QuadraticForm (ZMod 2) I) (hq : q.polarBilin=B.restrict I)
    (heq : s.constituentLinearAction.range =
      ChapterG.Section12.embeddedResidual q.isometrySubgroup)
    (hr : 3 ≤ primeRank 3 (ChapterG.Section12.embeddedResidual q.isometrySubgroup)) :
    False := by
  have hb := s.orthogonal_residual_odd_primeRank_le_two hnd q hq heq 3 (by decide)
  omega

/-- The remaining original source obligations are transitive recognition
and a cubic-rank witness in orthogonal degree at least eight. These local
premises remain with this theorem's source assembly owner. -/
theorem faithful_data_of_transitive_orthogonal_rank
    (htransitive : 6 ≤ finrank (ZMod 2) I →
      ∀ u i : I, ChapterG.Section12.ClassificationHypotheses
        s.constituentGeneratedImage (B.restrict I) u i →
        (∀ x : I,x≠0 → ∃ a∈s.constituentGeneratedImage,a i=x) →
        ChapterG.Section12.ResidualModel
          (ChapterG.Section12.embeddedResidual s.constituentGeneratedImage) (B.restrict I))
    (hrank : 8 ≤ finrank (ZMod 2) I →
      ∀ q : QuadraticForm (ZMod 2) I,q.polarBilin.Nondegenerate →
        3 ≤ primeRank 3 (ChapterG.Section12.embeddedResidual q.isometrySubgroup)) :
    ExchangedFaithfulConstituentData F.terminalRepresentation B L
      (F.terminalDot (F.X g)) I s.selected := by
  apply s.faithful_data_of_transitive_orthogonal_ge_eight htransitive
  intro hnd hd q hq he
  exact s.false_of_orthogonal_rank_three hnd q hq he (hrank hd q (hq.symm ▸ hnd))

end ExchangedCentralSource
end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
