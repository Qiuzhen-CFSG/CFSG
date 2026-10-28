module
public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels.Source
public import CFSG.Quasithin.ChapterE.Section02.Structure.NumericalBounds.Paired.Attainment
import all CFSG.Quasithin.ChapterB.Section06To07.Structure

/-!
# Original paired generation witness for the source dispatcher

The actual nonnormal source C-component supplies some positive E-generation
parameter of H. No component model, equality across the maximal core, or
external attainment certificate is assumed. This is the exchanged-component
input for the final KnownSimple minimal-parabolic dispatcher.
Source: Aschbacher–Smith E.1.11 and E.2.2, printed pp.213–216.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels
universe u
variable {H : Type u} [Group H] [Finite H] {κ : GroupClass.{u}}

theorem paired_exists_isEGenerated
    (hA : ChapterA.Section02.TheoremA κ H) (hH : IsSQTK κ H)
    (T : Sylow 2 H) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (hs : ¬Group.IsSolvable H) (K : Subgroup H) (hK : K.IsCComponent)
    (hgen : K ⊔ (T : Subgroup H) = ⊤) (hn : ¬ K.Normal) :
    ∃ f : ℕ, 0 < f ∧ IsEGenerated f H :=
  Structure.NumericalBounds.paired_exists_isEGenerated hA hH T hP hs K hK hgen hn

end CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels
