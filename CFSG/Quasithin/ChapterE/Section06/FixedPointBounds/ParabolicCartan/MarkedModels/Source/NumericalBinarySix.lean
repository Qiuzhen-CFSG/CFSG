module
public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels.Source
public import CFSG.Quasithin.ChapterE.Section02.Structure.NumericalBounds.BinarySix
import all CFSG.Quasithin.ChapterB.Section06To07.Structure

/-!
# The binary derived symplectic bound on the literal source quotient

The actual sourceImage M K, with M the original unique maximal overgroup of
T, is marked by the commutator of PSp₄(2). Its genuine full-extension bound
lifts through core_H(M) and gives both attained E-generation at one and
n(H) ≤ 1. This removes the binary row from the Cartan consumer when n(H)>1.
The source model, original quotient map and prescribed Sylow are preserved.

Source: Aschbacher–Smith E.1.14 and E.2.2, printed pp.214–216.
-/

public section
open Subgroup
namespace CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels
universe u
variable {H : Type u} [Group H] [Finite H]

/-- The literal binary source row supplies original rank-one generation. -/
theorem normal_binary_six_isEGenerated
    (T : Sylow 2 H) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (hs : ¬Group.IsSolvable H) (K : Subgroup H) (hK : K.IsCComponent) [K.Normal]
    (hgen : K ⊔ (T : Subgroup H) = ⊤)
    (hm : Nonempty ((sourceImage (ChapterB.minimalParabolicMax T hP) K) ≃*
      commutator (ClassicalGroup.PSp 2 (ZMod 2)))) :
    IsEGenerated 1 H :=
  Structure.NumericalBounds.normal_binary_six_isEGenerated T hP hs K hK hgen hm

/-- The literal binary source row gives the original parameter bound. -/
theorem normal_binary_six_parameter_le
    (T : Sylow 2 H) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (hs : ¬Group.IsSolvable H) (K : Subgroup H) (hK : K.IsCComponent) [K.Normal]
    (hgen : K ⊔ (T : Subgroup H) = ⊤)
    (hm : Nonempty ((sourceImage (ChapterB.minimalParabolicMax T hP) K) ≃*
      commutator (ClassicalGroup.PSp 2 (ZMod 2)))) :
    generationParameter H ≤ 1 :=
  Structure.NumericalBounds.normal_binary_six_upper T hP hs K hK hgen hm

end CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels
