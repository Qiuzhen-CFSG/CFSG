module

public import CFSG.Quasithin.Chapter13.Section08.SourceCompletion.LocalModels.Quotient
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Swapped.LinearThree.MarkedAutomizer.ModelDefs
public import Theory.Mathieu.M22.ChapterHLocalClassification.HexadAction.SymplecticComparison.PolarModel

/-!
# Compatible original point models

The prescribed natural A₆ coordinates on V are transported by the proved
six-letter-to-polar equivalence. The original component quotient has a
marked ordinary or cubic-cover identification over the same A₆ projection.
Consequently the literal L-action supplies precisely the simple/covered
point models used in the two-factor branch of 13.8.5, without an extra
module-marking hypothesis.

Source: Aschbacher–Smith, Notation 13.2.1 and 13.5.2(3), pp.877,915.
-/

public section

open Subgroup BinaryPermutation Theory.SpecificGroups.SymmetricSix
namespace CFSG.Quasithin.Chapter13.Section08.SourceCompletion
open TransvectionRecognition.Component.ModelExtension
open Components.Swapped.LinearThree.MarkedAutomizer
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ : Subgroup G}
  (d : LocalSetup T L V V₁ V₂ V₃ M G₁)

private noncomputable def local_polar_coordinate :
    V ≃* Multiplicative NaturalModule :=
  d.coordinate.trans
    HexadSymplecticComparison.PolarModel.deletedToPolar.toAddEquiv.toMultiplicative

private theorem local_polar_action (l : L) (v : V) :
    (local_polar_coordinate d (V.normalizerMonoidHom
      ⟨l.val, d.normalizes_V (mem_sup_left l.property)⟩ v)).toAdd =
      polarAction (d.local_quotient (QuotientGroup.mk' (centralCore L) l)).val
        (local_polar_coordinate d v).toAdd := by
  change HexadSymplecticComparison.PolarModel.deletedToPolar
    (d.coordinate (V.normalizerMonoidHom _ v)).toAdd = _
  rw [d.conjugation]
  exact (HexadSymplecticComparison.PolarModel.deletedToPolar_equivariant
    (d.local_quotient (QuotientGroup.mk' (centralCore L) l)).val
    (d.coordinate v).toAdd).trans (polarRepresentation_apply _ _)

/-- The actual simple or covered point marking, preserving the original
quotient map and conjugation on V. -/
theorem local_point_models :
    Nonempty (SimplePointModel L V (le_sup_left.trans d.normalizes_V)) ∨
      Nonempty (CoverPointModel L V (le_sup_left.trans d.normalizes_V)) := by
  rcases local_quotient_alternatives d with ⟨e, he⟩ | ⟨e, he⟩
  · refine Or.inl ⟨{ quotientEquiv := e, moduleEquiv := local_polar_coordinate d, equivariant := ?_ }⟩
    intro l v
    change (local_polar_coordinate d (V.normalizerMonoidHom
      ⟨l.val, d.normalizes_V (mem_sup_left l.property)⟩ v)).toAdd = _
    rw [he]
    exact local_polar_action d l v
  · refine Or.inr ⟨{ quotientEquiv := e, moduleEquiv := local_polar_coordinate d, equivariant := ?_ }⟩
    intro l v
    change (local_polar_coordinate d (V.normalizerMonoidHom
      ⟨l.val, d.normalizes_V (mem_sup_left l.property)⟩ v)).toAdd = _
    rw [he]
    exact local_polar_action d l v

end CFSG.Quasithin.Chapter13.Section08.SourceCompletion

end
