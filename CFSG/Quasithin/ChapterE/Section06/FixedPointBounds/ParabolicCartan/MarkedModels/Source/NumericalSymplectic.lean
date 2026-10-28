module
public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels.Source
public import CFSG.Quasithin.ChapterE.Section02.Structure.NumericalBounds.Symplectic.Nonbinary
import all CFSG.Quasithin.ChapterB.Section06To07.Structure

/-!
# The symplectic bound with the literal source quotient

Apply the full-extension generation theorem to the actual sourceImage M K,
where M is the original unique maximal subgroup above T. Its field exponent
bounds n(H) and supplies an attained E-generation witness in H. No diagram,
fixed-group or solvability calculation remains as a consumer premise.

Source: Aschbacher–Smith E.2.2, printed pp.215–216, and the field-indexed
Cartan argument used in E.6.27, printed p.257.
-/

public section
open Subgroup
namespace CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels
universe u
variable {H : Type u} [Group H] [Finite H] {κ : GroupClass.{u}}

/-- The literal nonbinary symplectic row gives actual original generation. -/
theorem normal_symplectic_isEGenerated
    (hA : ChapterA.Section02.TheoremA κ H) (hH : IsSQTK κ H)
    (T : Sylow 2 H) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (hs : ¬Group.IsSolvable H) (K : Subgroup H) (hK : K.IsCComponent) [K.Normal]
    (hgen : K ⊔ (T : Subgroup H) = ⊤) {f : ℕ} (hf : 1 < f)
    (hm : ClassicalGroup.IsPSp
      (sourceImage (ChapterB.minimalParabolicMax T hP) K) 2 (2^f)) :
    IsEGenerated f H :=
  Structure.NumericalBounds.normal_symplectic_isEGenerated hA hH T hP hs K hK hgen hf hm

/-- The literal marked row gives the upper bound consumed by Cartan. -/
theorem normal_symplectic_parameter_le
    (hA : ChapterA.Section02.TheoremA κ H) (hH : IsSQTK κ H)
    (T : Sylow 2 H) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (hs : ¬Group.IsSolvable H) (K : Subgroup H) (hK : K.IsCComponent) [K.Normal]
    (hgen : K ⊔ (T : Subgroup H) = ⊤) {f : ℕ} (hf : 1 < f)
    (hm : ClassicalGroup.IsPSp
      (sourceImage (ChapterB.minimalParabolicMax T hP) K) 2 (2^f)) :
    generationParameter H ≤ f :=
  Structure.NumericalBounds.normal_symplectic_upper hA hH T hP hs K hK hgen hf hm

end CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels
