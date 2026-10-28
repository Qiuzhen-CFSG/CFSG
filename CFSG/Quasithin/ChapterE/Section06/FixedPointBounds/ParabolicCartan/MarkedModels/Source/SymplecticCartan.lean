module
public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels.Source.NumericalSymplectic
public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels.Source.SymplecticFour
public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels.Source.NormalClauses
public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels.ParameterBound
/-!
# The original nonbinary symplectic Cartan construction

Combine the full diagram-extension generation theorem and solvable-core
lift with the actual original Borel and diagram marking. The covered
Borel supplies Hall control, so the field exponent gives a complete
Hall–Cartan witness, actual E-generation and an upper bound on n(H).
No equality across the original maximal core is asserted.

Source: Aschbacher–Smith E.2.2(2b) and E.6.27, pp.215–216,257.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels
universe u
variable {H:Type u} [Group H] [Finite H] {κ:GroupClass.{u}}
theorem normal_symplectic_intrinsic
    (hA:ChapterA.Section02.TheoremA κ H) (hH:IsSQTK κ H)
    (T:Sylow 2 H) (hP:ChapterB.IsMinimalParabolicOver T ⊤)
    (hs:¬Group.IsSolvable H) (K:Subgroup H) (hK:K.IsCComponent) [K.Normal]
    (hqs:IsQuasisimple (K⧸pCore 2 K)) (hgen:K⊔(T:Subgroup H)=⊤) {f:ℕ} (hf:1<f)
    (hm:ClassicalGroup.IsPSp (sourceImage (ChapterB.minimalParabolicMax T hP) K) 2 (2^f)) :
    IsEGenerated f H ∧ generationParameter H≤f ∧ Nonempty (IntrinsicHallCartanData T hP f) := by
  exact ⟨normal_symplectic_isEGenerated hA hH T hP hs K hK hgen hf hm,
    normal_symplectic_parameter_le hA hH T hP hs K hK hgen hf hm,
    diagram_intrinsic_at T hP hf hK (source_single_clauses T hP hs K hK hqs hgen)
      (source_binary_symplectic_model T hP hs K hK hgen hf hm)⟩
end CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels
