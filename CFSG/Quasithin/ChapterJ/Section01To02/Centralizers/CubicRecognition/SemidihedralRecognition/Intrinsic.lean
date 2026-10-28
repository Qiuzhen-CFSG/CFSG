module

public import CFSG.Quasithin.ChapterJ.Section01To02.Centralizers.CubicRecognition.SemidihedralRecognition.ResidualGeometry
public import CFSG.Quasithin.ChapterJ.Section01To02.Centralizers.CubicRecognition.SemidihedralRecognition.A6Identification
public import CFSG.Quasithin.ChapterJ.Section01To02.Centralizers.CubicRecognition.SemidihedralRecognition.PSL3Exclusion

/-!
# Intrinsic semidihedral involution-centralizer recognition

The actual two-residual has index two, one involution class and a D8
involution centralizer. Exactly the n=3 implication of I.4.1 identifies it
with PSL₃(2) or A₆. The former has no index-two extension with an SD16 Sylow.
For the latter, faithful conjugation and the marked Sylow geometry identify
the image with the specified M₁₀ subgroup of Aut(A₆), retaining the original
residual as the restricted inner subgroup.

Only I.4.1(2) remains parameterized. Its proof belongs to the earlier-source
owner; no extension recognition or residual conclusion is an extra premise.
Source: Aschbacher–Smith, J.2.7, printed p.435 (PDF p.446), and I.4.1(2),
printed p.415 (PDF p.426).
-/

public section
namespace CFSG.Quasithin.ChapterJ.SemidihedralRecognition
universe u

/-- Exactly the n=3 implication of source I.4.1, for arbitrary finite groups. -/
@[expose] def DihedralEightRecognition : Prop :=
  ∀ (X : Type u) [Group X] [Finite X], DihedralInvolutionCentralizerHypotheses X 3 →
    Nonempty (X ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2)) ∨
      Nonempty (X ≃* alternatingGroup (Fin 6))

namespace Hypotheses
variable {W : Type u} [Group W] [Finite W] (h : Hypotheses W)
include h

/-- I.4.1(2) identifies the actual residual with A₆; the PSL₃(2) branch is impossible. -/
theorem twoResidual_alternatingSix (hI : DihedralEightRecognition.{u}) :
    Nonempty (pResidual 2 W ≃* alternatingGroup (Fin 6)) := by
  rcases hI (pResidual 2 W) h.residualDihedralHypotheses with hp | ha
  · exact False.elim (h.no_psl3_index_two _ h.twoResidual_index hp.some)
  · exact ha

/-- Intrinsic recognition by the actual M₁₀, retaining the residual embedding. -/
theorem recognize_marked (hI : DihedralEightRecognition.{u}) :
    ∃ e : W ≃* AlternatingSix.M10.extension,
      (pResidual 2 W).map e.toMonoidHom =
        AlternatingSix.ShadowLocal.inner.subgroupOf AlternatingSix.M10.extension :=
  h.exists_marked_M10_equiv _ h.twoResidual_index (h.twoResidual_alternatingSix hI).some

/-- Intrinsic recognition by the specified subgroup of Aut(A₆). -/
theorem recognize (hI : DihedralEightRecognition.{u}) :
    Nonempty (W ≃* AlternatingSix.M10.extension) :=
  ⟨(h.recognize_marked hI).choose⟩

end Hypotheses
end CFSG.Quasithin.ChapterJ.SemidihedralRecognition
