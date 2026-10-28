module
public import CFSG.Quasithin.ChapterF.Section04.UnitaryFiveSource.Classes
public import CFSG.Quasithin.ChapterF.Section04.UnitaryFiveSource.LineCenter
public import Theory.GroupTheory.EmbeddedCenterMap

/-!
# The same long root in both U₅ endpoints

The plane parameter diag(1,0) is literally the line-radical scalar
parameter (0,1). Its matrix equality places this same projective element
in the center of the opposite residual. The source application can thus
transport the orthogonal three-space's compatible long-root generator
into the original long-root class using the full amalgam marking.

Source: Aschbacher–Smith F.4.42, printed pp.295–296 of refs/quasithin.pdf.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Matrix
namespace CFSG.Quasithin.ChapterF.GreenBook.UnitaryFive.Model
open Theory.SpecificGroups.UnitaryFive
variable (U : Model 4)

/-- The plane long mark is literally central in the opposite line residual. -/
theorem longInvolution_mem_leftLocalImage_center : U.longInvolution.val ∈
    (center U.leftLocalImage).map U.leftLocalImage.subtype := by
  let u : LineCore.Coord U.form := ⟨0,1,by simp [CharTwo.add_self_eq_zero]⟩
  have he : (LineCore.Parabolic.toParabolic U.form U.matrix u).val = U.longInvolution.val := by
    change project U.form (LineCore.Parabolic.toSU U.form U.matrix u) =
      project U.form (PlaneCore.Parameters.toSU U.matrix (PlaneCore.Parameters.diagonalParameter U.form 0 (map_zero _)))
    congr 1
    apply Subtype.ext
    apply Units.ext
    change (LineCore.Parabolic.ambientGL U.form u).val =
      (PlaneCore.Parameters.ambientGL (PlaneCore.Parameters.diagonalParameter U.form 0 (map_zero _))).val
    rw [LineCore.Parabolic.ambientGL_val,PlaneCore.Parameters.ambientGL_val]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [LineCore.Parabolic.ambientMatrix,PlaneCore.Parameters.ambientMatrix,
        PlaneCore.Parameters.diagonalParameter,u]
  rw [←he]
  apply (map_embeddedCenter U.leftLocal U.leftParabolic.subtype U.leftParabolic.subtype_injective).le
  refine ⟨LineCore.Parabolic.toParabolic U.form U.matrix u,?_,rfl⟩
  rw [U.leftLocal_eq_lineRadicalLeviSubgroup]
  obtain ⟨c,hc⟩ := U.exists_lineTraceOne
  rw [LineCore.Parabolic.center_image_eq U.form U.matrix U.conjugation U.local_field_card c hc]
  exact ⟨u,(LineCore.Coord.mem_center_iff_vector_eq_zero c hc u).mpr rfl,rfl⟩

end CFSG.Quasithin.ChapterF.GreenBook.UnitaryFive.Model
