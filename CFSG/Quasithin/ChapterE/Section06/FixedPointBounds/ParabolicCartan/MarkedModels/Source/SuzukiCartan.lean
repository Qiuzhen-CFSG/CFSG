module
public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels.Source.ClassicalCartan
public import CFSG.Quasithin.ChapterE.Section01.ValuesEvenExceptional.Suzuki
import all CFSG.Quasithin.ChapterB.Section06To07.Structure
/-!
# Actual Suzuki generation and the original Cartan witness

The original star quotient has the selected simple component as its
full generalized Fitting subgroup. The genuine Suzuki generation theorem
and solvability of the full original maximal core give actual E-generation
on H and the upper bound by the odd field exponent. The original Borel
marking and single-component structural theorem supply the complete
Hall–Cartan witness at that same exponent.

Source: Aschbacher–Smith E.1.14, E.2.2 and E.6.27, pp.214–216,257.
-/

public section
open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
namespace CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels
variable {H:Type*} [Group H] [Finite H]
theorem normal_suzuki_generation
    (T:Sylow 2 H) (hP:ChapterB.IsMinimalParabolicOver T ⊤)
    (hs:¬Group.IsSolvable H) (K:Subgroup H) (hK:K.IsCComponent) [K.Normal]
    (hgen:K⊔(T:Subgroup H)=⊤) {m:ℕ} (hm:0<m)
    (he:Nonempty (sourceImage (ChapterB.minimalParabolicMax T hP) K≃*SuzukiMatrixGroup m)) :
    IsEGenerated (2*m+1) H ∧ generationParameter H≤2*m+1 := by
  let J:=ChapterB.minimalParabolicCore T hP
  let q:=QuotientGroup.mk' J
  let S:=T.mapSurjective (QuotientGroup.mk'_surjective J)
  let D:=K.map q
  obtain ⟨hDs,hDa,hDn,hDT⟩:=Structure.source_normal_simple_image T hP hs K hK hgen
  let : IsSimpleGroup D:=hDs
  let : D.Normal:=hDn
  have hstar:=Structure.source_star_minimal_core_free T hP
  have hF:generalizedFitting (H⧸J)=D :=
    (Structure.Sporadic.faithful_normal_structure S hstar.1 hstar.2 D hDa hDT).1
  let ef:generalizedFitting (H⧸J)≃*D:=MulEquiv.subgroupCongr hF
  let : IsSimpleGroup (generalizedFitting (H⧸J)):=ef.isSimpleGroup
  obtain ⟨e⟩:=he
  have hgenstar:generalizedFitting (H⧸J)⊔(S:Subgroup (H⧸J))=⊤:=by rw [hF];exact hDT
  have hvalue:=ExceptionalValues.Suzuki.generationParameter_eq S hgenstar hm (ef.trans e)
  have hg:=Structure.NumericalBounds.isEGenerated_of_star_parameter T hP (by omega) hvalue
  exact ⟨hg,generationParameter_le (by omega) hg⟩

theorem normal_suzuki_intrinsic
    (T:Sylow 2 H) (hP:ChapterB.IsMinimalParabolicOver T ⊤)
    (hs:¬Group.IsSolvable H) (K:Subgroup H) (hK:K.IsCComponent) [K.Normal]
    (hqs:IsQuasisimple (K⧸pCore 2 K)) (hgen:K⊔(T:Subgroup H)=⊤) {m:ℕ} (hm:0<m)
    (he:Nonempty (sourceImage (ChapterB.minimalParabolicMax T hP) K≃*SuzukiMatrixGroup m)) :
    IsEGenerated (2*m+1) H ∧ generationParameter H≤2*m+1 ∧
      Nonempty (IntrinsicHallCartanData T hP (2*m+1)) := by
  obtain ⟨hg,hb⟩:=normal_suzuki_generation T hP hs K hK hgen hm he
  exact ⟨hg,hb,bender_intrinsic_at T hP (by omega) hK
    (source_single_clauses T hP hs K hK hqs hgen)
    (Or.inl (source_suzuki_borel_model T hP hs K hK hgen hm he))⟩
end CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels
