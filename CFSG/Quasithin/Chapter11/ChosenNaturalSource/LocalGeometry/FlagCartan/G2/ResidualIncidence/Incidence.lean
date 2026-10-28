module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.FlagCartan.G2.ResidualIncidence.Incidence.Model
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.FlagCartan.G2.ResidualIncidence.Incidence.Transport
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.FlagCartan.G2.ResidualIncidence.OrbitGeneration
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.FlagCartan.G2.ResidualIncidence.Incidence.PointImage
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.FlagCartan.G2.DisplacementNormalizer

/-!
# Incidence and displacement geometry of the original G₂ plane family

Two explicit model planes meet in the first flag space and span the third.
Their full preimages, transported through the common marking, give the same
identities in the original group, retaining the central kernel. The marked
point-residual Sylow image discharges the displacement-family premise.

The resulting normalizer-control theorem retains only the earlier unique
noncentral-component input. That input belongs to
`qt-d-1222-natural-relative-components`; the final source assembly remains
with `qt-d-1222-natural-local-geometry` and the normalizer source owner.

Source: Aschbacher--Smith, opening §11.1 and 11.1.4, pp.760--761,765.
-/

@[expose] public section


set_option backward.isDefEq.respectTransparency false
noncomputable section
open Subgroup Representation
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.ChapterB.QuasisimpleSource
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.G2.ResidualIncidence
open Atlas.G2 Atlas.G2.Natural Atlas.G2.Natural.OrthogonalCover
open Atlas.G2.Natural.OrthogonalCover.SylowFlag Atlas.G2.LieParabolicSetup
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : ChosenModule T L V} (S : D.NonbinaryNaturalInput)
    (m : ActionEquiv D.centralQuotientAction
      (restrictScalars (k := ZMod 2) (g2Natural S.field.Carrier)))

/-- The original plane conjugate uses the same alignment and residual projection. -/
theorem planeConjugate_eq (l : (flag S m).Li 0) :
    ((flag S m).Vi 1).map (MulAut.conj (l : G)).toMonoidHom =
      (coordinates S m).preimage
        (((naturalPlane S.field.Carrier).map
          (Natural.action S.field.Carrier (localProjection S m 0 l).val)).map
            (Natural.action S.field.Carrier (alignment S m).val)) := by
  change ((coordinates S m).preimage ((flag S m).space 1)).map
    (MulAut.conj (l : G)).toMonoidHom = _
  rw [(coordinates S m).preimage_conjugate
    ⟨l.val,(localResidual_le _ l.property).1⟩, flag_space_eq S m 1]
  change (coordinates S m).preimage
    (((naturalPlane S.field.Carrier).map (Natural.action S.field.Carrier (alignment S m).val)).map
      (Natural.action S.field.Carrier ((coordinates S m).quotientMap
        ⟨l.val,(localResidual_le _ l.property).1⟩))) = _
  congr 1
  rw [← Submodule.map_comp, ← Submodule.map_comp]
  congr 1
  apply LinearMap.ext
  intro x
  change Natural.action S.field.Carrier
    ((coordinates S m).quotientMap ⟨l.val,(localResidual_le _ l.property).1⟩)
      (Natural.action S.field.Carrier (alignment S m).val x) =
    Natural.action S.field.Carrier (alignment S m).val
      (Natural.action S.field.Carrier (localProjection S m 0 l).val x)
  have he : (show Model S.field.Carrier from
      (coordinates S m).quotientMap ⟨l.val,(localResidual_le _ l.property).1⟩) *
      (alignment S m).val = (alignment S m).val * (localProjection S m 0 l).val := by
    rw [localProjection_coe]
    group
  simpa only [map_mul,Module.End.mul_apply] using
    congrArg (fun g => Natural.action S.field.Carrier g x) he

/-- Every full ambient plane in the point-residual orbit lies between V1 and V3. -/
theorem planeOrbit_interval (U : Subgroup G) (hU : U ∈ planeOrbit S m) :
    (flag S m).Vi 0 ≤ U ∧ U ≤ (flag S m).Vi 2 := by
  obtain ⟨l,rfl⟩ := hU
  rw [planeConjugate_eq S m l]
  have hi := local₂_plane_interval S.field.Carrier (localProjection S m 0 l).val
    (localProjection S m 0 l).property
  constructor
  · apply ((coordinates S m).preimage_le_iff _ _).mpr
    rw [flag_space_eq S m 0]
    exact Submodule.map_mono hi.1
  · apply ((coordinates S m).preimage_le_iff _ _).mpr
    rw [flag_space_eq S m 2]
    exact Submodule.map_mono hi.2

/-- One actual element of L1 gives the two-plane meet and join witnesses. -/
theorem exists_planeConjugate_meet_join :
    ∃ l : (flag S m).Li 0,
      (flag S m).Vi 1 ⊓ ((flag S m).Vi 1).map (MulAut.conj (l : G)).toMonoidHom =
        (flag S m).Vi 0 ∧
      (flag S m).Vi 1 ⊔ ((flag S m).Vi 1).map (MulAut.conj (l : G)).toMonoidHom =
        (flag S m).Vi 2 := by
  have hw : (weylR : Model S.field.Carrier) ∈ standardLocal S.field.Carrier 0 :=
    (show Subgroup.closure {weylR} ≤ local₂ (F := S.field.Carrier) from le_sup_right)
      (subset_closure (by simp))
  obtain ⟨l,hl⟩ := localProjection_surjective S m 0 ⟨weylR,hw⟩
  refine ⟨l,?_,?_⟩
  · rw [planeConjugate_eq, hl]
    change (coordinates S m).preimage ((flag S m).space 1) ⊓ _ =
      (coordinates S m).preimage ((flag S m).space 0)
    rw [← (coordinates S m).preimage_inf, flag_space_eq S m 1, flag_space_eq S m 0]
    change (coordinates S m).preimage
      (((naturalPlane S.field.Carrier).map (Natural.action S.field.Carrier (alignment S m).val)) ⊓
        (((naturalPlane S.field.Carrier).map (Natural.action S.field.Carrier weylR)).map
          (Natural.action S.field.Carrier (alignment S m).val))) =
      (coordinates S m).preimage
        ((N1 S.field.Carrier).map (Natural.action S.field.Carrier (alignment S m).val))
    rw [← Submodule.map_inf _ ((Natural.action S.field.Carrier).apply_bijective _).injective,
      plane_inf_weylR]
  · rw [planeConjugate_eq, hl]
    change (coordinates S m).preimage ((flag S m).space 1) ⊔ _ =
      (coordinates S m).preimage ((flag S m).space 2)
    rw [← (coordinates S m).preimage_sup, flag_space_eq S m 1, flag_space_eq S m 2]
    change (coordinates S m).preimage
      (((naturalPlane S.field.Carrier).map (Natural.action S.field.Carrier (alignment S m).val)) ⊔
        (((naturalPlane S.field.Carrier).map (Natural.action S.field.Carrier weylR)).map
          (Natural.action S.field.Carrier (alignment S m).val))) =
      (coordinates S m).preimage
        ((naturalThreeSpace S.field.Carrier).map (Natural.action S.field.Carrier (alignment S m).val))
    rw [← Submodule.map_sup, plane_sup_weylR]

private theorem planeOrbit_base : (flag S m).Vi 1 ∈ planeOrbit S m := by
  refine ⟨1,?_⟩
  ext x
  simp

/-- The actual plane orbit has intersection V1, including the common central kernel. -/
theorem planeOrbit_meet : (⨅ U : planeOrbit S m, U.val) = (flag S m).Vi 0 := by
  obtain ⟨l,hm,-⟩ := exists_planeConjugate_meet_join S m
  apply le_antisymm
  · calc
      (⨅ U : planeOrbit S m, U.val) ≤ (flag S m).Vi 1 ⊓
          ((flag S m).Vi 1).map (MulAut.conj (l : G)).toMonoidHom :=
        le_inf (iInf_le (fun U : planeOrbit S m => U.val) ⟨_,planeOrbit_base S m⟩) (iInf_le (fun U : planeOrbit S m => U.val) ⟨_,⟨l,rfl⟩⟩)
      _ = (flag S m).Vi 0 := hm
  · exact le_iInf fun U => (planeOrbit_interval S m U.val U.property).1

/-- The actual plane orbit generates V3, as an ambient subgroup. -/
theorem planeOrbit_span : (⨆ U : planeOrbit S m, U.val) = (flag S m).Vi 2 := by
  obtain ⟨l,-,hj⟩ := exists_planeConjugate_meet_join S m
  apply le_antisymm
  · exact iSup_le fun U => (planeOrbit_interval S m U.val U.property).2
  · rw [← hj]
    exact sup_le (le_iSup (fun U : planeOrbit S m => U.val) ⟨_,planeOrbit_base S m⟩) (le_iSup (fun U : planeOrbit S m => U.val) ⟨_,⟨l,rfl⟩⟩)

/-- Application of the proved incidence to source 11.1.4. The unique component
input is produced by the independent relative-components source owner. -/
theorem normalizes_of_centralizes_third_section
    (hunique : Source.UniqueNoncentralComponent
      (normalizer ((flag S m).Vi 1 : Set G)) ((flag S m).Vi 1) ((flag S m).Li 1))
    {g : G} (hg : Source.CentralizesSection g ((flag S m).Vi 2) ((flag S m).Vi 0)) :
    g ∈ normalizer (L : Set G) := by
  apply normalizes_of_plane_permutation S m hunique
  intro U hU
  rwa [Normalizers.sectionCentralizer_fixes (planeOrbit_interval S m U hU).1
    (planeOrbit_interval S m U hU).2 hg]

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.G2.ResidualIncidence

set_option backward.isDefEq.respectTransparency false
noncomputable section
open Subgroup Representation
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.ChapterB.QuasisimpleSource
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.G2.ResidualIncidence
open Atlas.G2 Atlas.G2.Natural Atlas.G2.Natural.OrthogonalCover
open Atlas.G2.Natural.OrthogonalCover.SylowFlag Atlas.G2.LieParabolicSetup
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : ChosenModule T L V} (S : D.NonbinaryNaturalInput)
    (m : ActionEquiv D.centralQuotientAction
      (restrictScalars (k := ZMod 2) (g2Natural S.field.Carrier)))

/-- Corrected source 11.1.4, with only the independent component input retained. -/
theorem source_normalizerControl
    (hunique : Source.UniqueNoncentralComponent
      (normalizer ((flag S m).Vi 1 : Set G)) ((flag S m).Vi 1) ((flag S m).Li 1)) :
    Source.NormalizerControl ((flag S m).Vi 2) ((flag S m).Vi 0) ((flag S m).Li 0)
      (normalizer (L : Set G)) := by
  exact normalizerControl_of_point_image S m (pointMap_image_contains_sylow S m)
    hunique (planeOrbit_residuals_generate S m) (planeOrbit_interval S m)

/-- The original plane family has the repaired Sylow displacement description. -/
theorem planeOrbit_eq_sylow_displacement :
    Normalizers.planeOrbit ((flag S m).Vi 1) ((flag S m).Li 0) =
      Set.range (fun P : Sylow 2 ((flag S m).Li 0) =>
        Displacement.subgroup ((flag S m).Vi 2) ((flag S m).Vi 0)
          ((P : Subgroup ((flag S m).Li 0)).map ((flag S m).Li 0).subtype)) := by
  obtain ⟨P,hP⟩ := exists_pointSylow S m (pointMap_image_contains_sylow S m)
  exact planeOrbit_eq_displacement S m P hP (planeOrbit_interval S m)

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.G2.ResidualIncidence

