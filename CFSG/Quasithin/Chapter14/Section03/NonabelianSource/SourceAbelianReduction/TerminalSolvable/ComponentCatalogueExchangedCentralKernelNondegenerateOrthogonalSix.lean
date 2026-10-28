module
public import Theory.SpecificGroups.ClassicalOrthogonal.BinarySixResidual
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.ComponentCatalogueExchangedCentralKernelNondegenerateFourComplete
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.ComponentCatalogueExchangedCentralKernelNondegenerateOrthogonalReduction

/-!
# Excluding both degree-six orthogonal constituents

The actual quadratic-space classification identifies the full isometry group
with the split S₈ action or the minus-six model. The split residual is centerless
and every automorphism preserves the natural module, contradicting the
exchanged-constituent obstruction. The minus residual is centerless with cubic
rank at least three, contradicting the original terminal odd-rank bound.

This discharges the complete degree-six orthogonal alternative on the literal
selected constituent. Together with the nontransitive recognition, it proves
that a nondegenerate degree-six constituent would have transitive generated
action. Transitive recognition and orthogonal degrees at least eight remain
with qt-e-14315-exchanged-central-kernel; final exchanged-image assembly remains
with qt-e-14315-component-exchanged-images.

Source: Aschbacher--Smith G.10.15, printed p.363, using G.12.10, printed p.373.
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

/-- Both degree-six orthogonal signs are impossible for the original action. -/
theorem false_of_orthogonal_six
    (hnd : (B.restrict I).Nondegenerate)
    (q : QuadraticForm (ZMod 2) I) (hq : q.polarBilin=B.restrict I)
    (heq : s.constituentLinearAction.range =
      ChapterG.Section12.embeddedResidual q.isometrySubgroup)
    (hd : finrank (ZMod 2) I=6) : False := by
  have h := QuadraticForm.BinarySixResidual.orthogonal_six q (hq.symm ▸ hnd) hd
  change center (ChapterG.Section12.embeddedResidual q.isometrySubgroup)=⊥ ∧
    (ImageAutomorphismsLinear (ChapterG.Section12.embeddedResidual q.isometrySubgroup) ∨
      3 ≤ primeRank 3 (ChapterG.Section12.embeddedResidual q.isometrySubgroup)) at h
  rw [← heq] at h
  rcases h.2 with hl|hr
  · exact s.not_imageAutomorphismsLinear_of_constituentImage_centerless s.not_fullLinear h.1 hl
  · have hb := s.constituentImage_odd_primeRank_le_two h.1 3 (by decide)
    omega

/-- The recognized nontransitive branch cannot occur in degree six. -/
theorem nondegenerate_transitive_of_dimension_six
    (hnd : (B.restrict I).Nondegenerate) {u i : I}
    (h : ChapterG.Section12.ClassificationHypotheses
      s.constituentGeneratedImage (B.restrict I) u i)
    (hd : finrank (ZMod 2) I=6) :
    ∀ x : I,x≠0 → ∃ a∈s.constituentGeneratedImage,a i=x := by
  by_contra ht
  obtain ⟨_,q,hq,he⟩ := s.nondegenerate_orthogonal_of_not_transitive hnd h ht
  exact s.false_of_orthogonal_six hnd q hq he hd

/-- The original source assembly now retains transitive recognition in degree
at least six and orthogonal exclusion only in degree at least eight.
These remaining local source obligations stay with this task's owner. -/
theorem faithful_data_of_transitive_orthogonal_ge_eight
    (htransitive : 6 ≤ finrank (ZMod 2) I →
      ∀ u i : I, ChapterG.Section12.ClassificationHypotheses
        s.constituentGeneratedImage (B.restrict I) u i →
        (∀ x : I,x≠0 → ∃ a∈s.constituentGeneratedImage,a i=x) →
        ChapterG.Section12.ResidualModel
          (ChapterG.Section12.embeddedResidual s.constituentGeneratedImage) (B.restrict I))
    (horthogonal : (B.restrict I).Nondegenerate →
      8 ≤ finrank (ZMod 2) I →
      ∀ q : QuadraticForm (ZMod 2) I,q.polarBilin=B.restrict I →
        s.constituentLinearAction.range=ChapterG.Section12.embeddedResidual
          q.isometrySubgroup → False) :
    ExchangedFaithfulConstituentData F.terminalRepresentation B L
      (F.terminalDot (F.X g)) I s.selected := by
  apply s.faithful_data_of_higher_transitive_orthogonal htransitive
  intro hnd hd q hq he
  by_cases hs : finrank (ZMod 2) I=6
  · exact s.false_of_orthogonal_six hnd q hq he hs
  obtain ⟨n,hn⟩ := AlternatingForm.even_finrank (B.restrict I)
    (fun w => s.hypothesis.alternating w) hnd
  exact horthogonal hnd (by omega) q hq he

end ExchangedCentralSource
end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
