module
public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels.Source.NumericalClassical
public import CFSG.Quasithin.ChapterE.Section02.Structure.NumericalBounds.Classical.Generation
import all CFSG.Quasithin.ChapterB.Section06To07.Structure

/-!
# E-generation with the literal marked classical source image

Retain the actual quotient by core_H(M) and expose generation at the model
exponent, in addition to the numerical upper bound. This is the generation
input required when a consumer has not assumed general attainment of n(H).
All original-kernel conditions are discharged by the lower source producer.

Source: Aschbacher–Smith E.1.10–14, E.2.2 and the E.6 Cartan application.
-/

public section
open Subgroup
namespace CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels
universe u
variable {H : Type u} [Group H] [Finite H] {κ : GroupClass.{u}}

/-- The original marked source model supplies actual E-generation at f. -/
theorem normal_classical_isEGenerated
    (hA : ChapterA.Section02.TheoremA κ H) (hH : IsSQTK κ H)
    (T : Sylow 2 H) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (hs : ¬Group.IsSolvable H) (K : Subgroup H) (hK : K.IsCComponent) [K.Normal]
    (hgen : K ⊔ (T : Subgroup H) = ⊤) {f : ℕ}
    (hm :
      (2 ≤ f ∧ ClassicalGroup.IsPSL (sourceImage (ChapterB.minimalParabolicMax T hP) K) 2 (2 ^ f)) ∨
      (2 ≤ f ∧ ClassicalGroup.IsPSU (sourceImage (ChapterB.minimalParabolicMax T hP) K) 3 (2 ^ f)) ∨
      (0 < f ∧ ClassicalGroup.IsPSL (sourceImage (ChapterB.minimalParabolicMax T hP) K) 3 (2 ^ f))) :
    IsEGenerated f H :=
  Structure.NumericalBounds.normal_classical_isEGenerated hA hH T hP hs K hK hgen hm

end CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels
