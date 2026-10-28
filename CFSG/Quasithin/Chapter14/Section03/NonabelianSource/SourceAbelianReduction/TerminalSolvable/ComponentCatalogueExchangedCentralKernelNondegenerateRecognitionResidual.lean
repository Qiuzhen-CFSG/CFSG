module
public import CFSG.Quasithin.ChapterG.Section12.RecognitionQuadraticResidual
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.ComponentCatalogueExchangedCentralKernelNondegenerateRecognitionQuadratic

/-!
# Complete nontransitive recognition on the selected constituent

The original center orbit constructs its invariant quadratic form. The full
orthogonal residual is generated inside the original HY-image by its actual
point radicals; perfectness then identifies it with the original H-image.
Degree four is already excluded by containment in the orthogonal group, so
this branch has degree at least six.

The literal faithful-constituent consumer therefore requires recognition only
for transitive actions, together with the higher orthogonal exclusions.
Both remaining obligations stay with `qt-e-14315-exchanged-central-kernel`;
final exchanged-image assembly stays with `qt-e-14315-component-exchanged-images`.
This module proves the nontransitive branch, not that final assembly.

Source: Aschbacher--Smith G.12.10, printed p.373, used in G.10.15 on p.363.
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

/-- The nontransitive source case is the literal orthogonal residual,
with no recognition premise and with dimension four already excluded. -/
theorem nondegenerate_orthogonal_of_not_transitive
    (hnd : (B.restrict I).Nondegenerate) {u i : I}
    (h : ChapterG.Section12.ClassificationHypotheses
      s.constituentGeneratedImage (B.restrict I) u i)
    (hnt : ¬∀ x : I,x≠0 → ∃ a∈s.constituentGeneratedImage,a i=x) :
    6 ≤ finrank (ZMod 2) I ∧
    ∃ q : QuadraticForm (ZMod 2) I,q.polarBilin=B.restrict I ∧
      s.constituentLinearAction.range=ChapterG.Section12.embeddedResidual q.isometrySubgroup := by
  have hn4 : finrank (ZMod 2) I≠4 :=
    fun hd => hnt (s.nondegenerate_transitive_of_dimension_four hnd h hd)
  obtain ⟨n,hn⟩ := AlternatingForm.even_finrank (B.restrict I) h.alternating hnd
  have hd : 6≤finrank (ZMod 2) I := by have := h.dimension; omega
  obtain ⟨q,hq,_,he⟩ := ChapterG.Section12.GoodVector.residual_orthogonal_of_not_transitive
    (V := I) (D := s.constituentGeneratedImage) (B := B.restrict I) (v := i)
    h.good_v hnd h.preserves h.irreducible (by omega : 5 ≤ finrank (ZMod 2) I) hnt
  rw [s.constituentGeneratedImage_residual] at he
  exact ⟨hd,q,hq,he⟩

/-- The original nondegenerate constituent has either a transitive generated
action or the recognized higher-dimensional orthogonal residual. -/
theorem nondegenerate_transitive_or_orthogonal
    (hnd : (B.restrict I).Nondegenerate) {u i : I}
    (h : ChapterG.Section12.ClassificationHypotheses
      s.constituentGeneratedImage (B.restrict I) u i) :
    (∀ x : I,x≠0 → ∃ a∈s.constituentGeneratedImage,a i=x) ∨
    (6≤finrank (ZMod 2) I ∧
      ∃ q : QuadraticForm (ZMod 2) I,q.polarBilin=B.restrict I ∧
        s.constituentLinearAction.range=ChapterG.Section12.embeddedResidual q.isometrySubgroup) := by
  by_cases ht : ∀ x : I,x≠0 → ∃ a∈s.constituentGeneratedImage,a i=x
  · exact Or.inl ht
  · exact Or.inr (s.nondegenerate_orthogonal_of_not_transitive hnd h ht)

/-- Conditional final assembly now needs recognition only in the transitive
branch. The complete nontransitive recognition is discharged above. The two
remaining premises are retained by this same source owner. -/
theorem faithful_data_of_transitive_recognition_orthogonal
    (htransitive : ∀ u i : I, ChapterG.Section12.ClassificationHypotheses
      s.constituentGeneratedImage (B.restrict I) u i →
      (∀ x : I,x≠0 → ∃ a∈s.constituentGeneratedImage,a i=x) →
      ChapterG.Section12.ResidualModel
        (ChapterG.Section12.embeddedResidual s.constituentGeneratedImage) (B.restrict I))
    (horthogonal : (B.restrict I).Nondegenerate →
      6≤finrank (ZMod 2) I →
      ∀ q : QuadraticForm (ZMod 2) I,q.polarBilin=B.restrict I →
        s.constituentLinearAction.range=ChapterG.Section12.embeddedResidual
          q.isometrySubgroup → False) :
    ExchangedFaithfulConstituentData F.terminalRepresentation B L
      (F.terminalDot (F.X g)) I s.selected := by
  apply s.faithful_data_of_recognition_orthogonal_ge_six _ horthogonal
  intro u i h
  rcases s.nondegenerate_transitive_or_orthogonal h.nondegenerate h with ht|⟨_,q,hq,he⟩
  · exact htransitive u i h ht
  · right; left
    exact ⟨q,hq,s.constituentGeneratedImage_residual.trans he⟩

end ExchangedCentralSource
end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
