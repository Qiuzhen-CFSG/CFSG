module
public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels.Source
public import CFSG.Quasithin.ChapterE.Section02.Structure.NumericalBounds.Paired.Original
import all CFSG.Quasithin.ChapterB.Section06To07.Structure

/-!
# Paired bounds on the marked original quotient

The field exponent belongs to the actual sourceImage of the original
C-component in H/core(M). The paired binary PSL₂ and Suzuki proofs give
IsEGenerated f H and n(H) ≤ f while retaining that literal map and Sylow.
This supplies the numerical side of the field-indexed exchanged Cartan row.
Source: Aschbacher–Smith E.2.2, printed pp.215–216.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels
universe u
variable {H : Type u} [Group H] [Finite H] {κ : GroupClass.{u}}

theorem paired_bender_isEGenerated
    (hA : ChapterA.Section02.TheoremA κ H) (hH : IsSQTK κ H)
    (T : Sylow 2 H) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (hs : ¬Group.IsSolvable H) (K : Subgroup H) (hK : K.IsCComponent)
    (hgen : K ⊔ (T : Subgroup H) = ⊤) (hn : ¬ K.Normal) {f : ℕ}
    (hm : (2 ≤ f ∧ ClassicalGroup.IsPSL
      (sourceImage (ChapterB.minimalParabolicMax T hP) K) 2 (2^f)) ∨
      ∃ m : ℕ, 0 < m ∧ f = 2*m+1 ∧ Nonempty
        ((sourceImage (ChapterB.minimalParabolicMax T hP) K) ≃*
          BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m)) : IsEGenerated f H :=
  Structure.NumericalBounds.paired_bender_isEGenerated hA hH T hP hs K hK hgen hn hm

theorem paired_bender_parameter_le
    (hA : ChapterA.Section02.TheoremA κ H) (hH : IsSQTK κ H)
    (T : Sylow 2 H) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (hs : ¬Group.IsSolvable H) (K : Subgroup H) (hK : K.IsCComponent)
    (hgen : K ⊔ (T : Subgroup H) = ⊤) (hn : ¬ K.Normal) {f : ℕ}
    (hm : (2 ≤ f ∧ ClassicalGroup.IsPSL
      (sourceImage (ChapterB.minimalParabolicMax T hP) K) 2 (2^f)) ∨
      ∃ m : ℕ, 0 < m ∧ f = 2*m+1 ∧ Nonempty
        ((sourceImage (ChapterB.minimalParabolicMax T hP) K) ≃*
          BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m)) : generationParameter H ≤ f :=
  Structure.NumericalBounds.paired_bender_upper hA hH T hP hs K hK hgen hn hm

end CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels
