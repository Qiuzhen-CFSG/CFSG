module
public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels.Source
public import CFSG.Quasithin.ChapterE.Section02.Structure.NumericalBounds.Classical
import all CFSG.Quasithin.ChapterB.Section06To07.Structure

/-!
# The classical upper bound with the original marked source image

These consumers use precisely `sourceImage M K`, where M is the unique
maximal subgroup above the prescribed Sylow subgroup of the original H.
Thus the quotient kernel is core_H(M), with no silent replacement by O₂(H).
The normal PSL₂, PSU₃ and PSL₃ rows give n(H) ≤ f; a later faithful degree
bound f ≤ n′ can then be composed without an equality across the core.

Source: Aschbacher–Smith E.2.2, pp.215–216, and the model-indexed Cartan
argument used in E.6.27, p.257. The old `FullAlternatives` and `SourceE22`
interfaces are preserved. Model selection belongs to the structural source
assembly; every kernel and quotient-generation premise is discharged here.
-/

public section
open Subgroup
namespace CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels
universe u
variable {H : Type u} [Group H] [Finite H] {κ : GroupClass.{u}}

/-- All three normal classical rows, on the literal marked source image. -/
theorem normal_classical_parameter_le
    (hA : ChapterA.Section02.TheoremA κ H) (hH : IsSQTK κ H)
    (T : Sylow 2 H) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (hs : ¬Group.IsSolvable H) (K : Subgroup H) (hK : K.IsCComponent) [K.Normal]
    (hgen : K ⊔ (T : Subgroup H) = ⊤) {f : ℕ}
    (hm :
      (2 ≤ f ∧ ClassicalGroup.IsPSL (sourceImage (ChapterB.minimalParabolicMax T hP) K) 2 (2 ^ f)) ∨
      (2 ≤ f ∧ ClassicalGroup.IsPSU (sourceImage (ChapterB.minimalParabolicMax T hP) K) 3 (2 ^ f)) ∨
      (0 < f ∧ ClassicalGroup.IsPSL (sourceImage (ChapterB.minimalParabolicMax T hP) K) 3 (2 ^ f))) :
    generationParameter H ≤ f :=
  Structure.NumericalBounds.normal_classical_upper hA hH T hP hs K hK hgen hm

/-- The normal binary PSL₂ row, retaining the original core quotient. -/
theorem normal_linear_two_parameter_le
    (hA : ChapterA.Section02.TheoremA κ H) (hH : IsSQTK κ H)
    (T : Sylow 2 H) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (hs : ¬Group.IsSolvable H) (K : Subgroup H) (hK : K.IsCComponent) [K.Normal]
    (hgen : K ⊔ (T : Subgroup H) = ⊤) {f : ℕ} (hf : 2 ≤ f)
    (hm : ClassicalGroup.IsPSL (sourceImage (ChapterB.minimalParabolicMax T hP) K) 2 (2 ^ f)) :
    generationParameter H ≤ f :=
  normal_classical_parameter_le hA hH T hP hs K hK hgen (.inl ⟨hf,hm⟩)

/-- The normal binary PSU₃ row, with f the fixed-field exponent. -/
theorem normal_unitary_three_parameter_le
    (hA : ChapterA.Section02.TheoremA κ H) (hH : IsSQTK κ H)
    (T : Sylow 2 H) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (hs : ¬Group.IsSolvable H) (K : Subgroup H) (hK : K.IsCComponent) [K.Normal]
    (hgen : K ⊔ (T : Subgroup H) = ⊤) {f : ℕ} (hf : 2 ≤ f)
    (hm : ClassicalGroup.IsPSU (sourceImage (ChapterB.minimalParabolicMax T hP) K) 3 (2 ^ f)) :
    generationParameter H ≤ f :=
  normal_classical_parameter_le hA hH T hP hs K hK hgen (.inr (.inl ⟨hf,hm⟩))

/-- The normal binary PSL₃ row includes f = 1. -/
theorem normal_linear_three_parameter_le
    (hA : ChapterA.Section02.TheoremA κ H) (hH : IsSQTK κ H)
    (T : Sylow 2 H) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (hs : ¬Group.IsSolvable H) (K : Subgroup H) (hK : K.IsCComponent) [K.Normal]
    (hgen : K ⊔ (T : Subgroup H) = ⊤) {f : ℕ} (hf : 0 < f)
    (hm : ClassicalGroup.IsPSL (sourceImage (ChapterB.minimalParabolicMax T hP) K) 3 (2 ^ f)) :
    generationParameter H ≤ f :=
  normal_classical_parameter_le hA hH T hP hs K hK hgen (.inr (.inr ⟨hf,hm⟩))

end CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels
