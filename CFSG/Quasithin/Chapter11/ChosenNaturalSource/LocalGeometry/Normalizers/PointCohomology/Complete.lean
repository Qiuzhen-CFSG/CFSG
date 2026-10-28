module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.PointCohomology.Assembly
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.PointCohomology.PointGeometry.SL3Core
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.PointCohomology.PointGeometry.Sp4Core

/-!
# The corrected point-radical omega-center calculation

The original point residual has radical O₂(L₁)O₂(LT), even with the full outer
Sylow supplement. Its fixed space is the original V₁, retaining every lift
through the possible nonsplit symplectic central kernel. The actual Cartan
then supplies a coprime decomposition of the radical omega-center.

Split first at Q=VC_T(L). In the strict branch, displacement cocycles construct
the literal quotient embedding; natural H¹ excludes SL₃ and the block forces
Sp₄(4). The dual orthogonal five-space calculation supplies the required
point-fixed bound. Thus no point-core, fixed-space or quotient-embedding
premise remains in the center identity. The normalizer-source parent
qt-d-1222-natural-normalizer-source owns block recognition and the subsequent
preservation of the fixed center in the full 11.1.5 alternative.

Source: Aschbacher–Smith 11.1.5, printed pp.765–766, with the C.1.13
correction Q₁=VC_T(L), and the original flag of pp.760–761.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.ChapterB.QuasisimpleSource
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.PointCohomology
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)

/-- Both original point-core calculations, including the full outer Sylow supplement. -/
theorem point_core_calculations {c : Coordinates D S.field} (f : InvariantFlag c)
    (hb : ChapterC.IsSL3EvenBlock L S.field.degree ∨ ChapterC.IsSp4FourBlock L) :
    f.Ri 0 = (f.Li 0).pCoreIn 2 ⊔ (L ⊔ (T : Subgroup G)).pCoreIn 2 ∧
      V ⊓ centralizer ((f.Li 0).pCoreIn 2 : Set G) = f.Vi 0 := by
  cases c with
  | sl3 m => exact ⟨PointGeometry.SL3Core.core_product D S m f,
      PointGeometry.SL3Core.local_core_fixed D S m f⟩
  | sp4 m => exact ⟨PointGeometry.Sp4Core.core_product D S m f,
      PointGeometry.Sp4Core.local_core_fixed D S m f⟩
  | g2 m => exact (PointGeometry.no_g2_block_marking D S m hb).elim

/-- The literal point and Cartan geometry used in the center calculation. -/
theorem exists_point_geometry {c : Coordinates D S.field} (f : InvariantFlag c)
    (hb : ChapterC.IsSL3EvenBlock L S.field.degree ∨ ChapterC.IsSp4FourBlock L) :
    ∃ X : Subgroup G, IsCartan T L X ∧ X ≤ normalizer (f.Ri 0 : Set G) ∧
      (V ⊓ centralizer (X : Set G) ≤ centralizer (L : Set G)) ∧
      V ⊓ centralizer (f.Ri 0 : Set G) = f.Vi 0 := by
  obtain ⟨hp,hf⟩ := point_core_calculations D S f hb
  exact PointGeometry.exists_point_geometry_of_core_calculations D S f hb hp hf

/-- The corrected 11.1.5 omega-center identity on the original flag and radical. -/
theorem center_eq {c : Coordinates D S.field} (f : InvariantFlag c)
    (hb : ChapterC.IsSL3EvenBlock L S.field.degree ∨ ChapterC.IsSp4FourBlock L) :
    radicalOmegaCenter (f.Ri 0) = f.Vi 0 ⊔ radicalFixedCenter (f.Ri 0) L := by
  obtain ⟨hp,hf⟩ := point_core_calculations D S f hb
  exact center_eq_of_core_calculations D S f hb hp hf

/-- The actual RadicalAssembly application with the center premise discharged.
The normalizer-source parent retains only its block and fixed-center obligations. -/
theorem radicalAlternative {c : Coordinates D S.field} (f : InvariantFlag c)
    (hblocks : (¬ normalizer (f.Ri 0 : Set G) ≤ normalizer (L : Set G)) →
      V = Source.conjugateSpan (normalizer (L : Set G)) V ∧
        (ChapterC.IsSL3EvenBlock L S.field.degree ∨ ChapterC.IsSp4FourBlock L))
    (hfixed : (¬ normalizer (f.Ri 0 : Set G) ≤ normalizer (L : Set G)) →
      (ChapterC.IsSL3EvenBlock L S.field.degree ∨ ChapterC.IsSp4FourBlock L) →
      radicalOmegaCenter (f.Ri 0) = f.Vi 0 ⊔ radicalFixedCenter (f.Ri 0) L →
      normalizer (f.Ri 0 : Set G) ≤ normalizer (radicalFixedCenter (f.Ri 0) L : Set G)) :
    Source.RadicalNormalizerAlternative (T : Subgroup G) V (f.Vi 0) (f.Ri 0)
      (normalizer (L : Set G)) L S.field.degree := by
  apply chosen_radicalAlternative_of_source_steps D S f hblocks _ hfixed
  intro _ hb
  exact center_eq D S f hb

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.PointCohomology
