module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.G2.PlaneGeneration
public import Theory.AtlasPort.LinearGroups.G2.SylowParabolicInvariance.Normalizers

/-!
# Generation by the recognized full G₂ root planes

Conjugating the proved point-residual plane orbit by the inverse of its
original alignment puts every plane in the long-root family of the fixed
A-B plane. The point parabolic normalizes that root family. Its actual full
preimages therefore generate all of L by their relative solvable residuals,
including the original two-core kernel. No assertion that the covering
center vanishes is used.

Comparison applies this generating family to the paired reciprocal planes.
This avoids requiring equality of two larger plane families: the recognized
root planes already contain a generating residual orbit.
Source: Aschbacher--Smith 11.1.3--4 and 11.2.2(5), printed pp.765,768.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.G2.CommonPlanes
open Atlas.G2 Atlas.G2.Natural Atlas.G2.Natural.OrthogonalCover
open CFSG.Quasithin.ChapterB.QuasisimpleSource CFSG.Quasithin.Chapter12.Section02
open LocalGeometry.G2.ResidualIncidence
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    (m : ActionEquiv D.centralQuotientAction
      (restrictScalars (k:=ZMod 2) (g2Natural S.field.Carrier)))

private theorem embeddedResidual_map (e : G ≃* G) (H : Subgroup G) :
    ((solvableResidual H).map H.subtype).map e.toMonoidHom =
      (solvableResidual (H.map e.toMonoidHom)).map (H.map e.toMonoidHom).subtype := by
  have he := congrArg (map (H.map e.toMonoidHom).subtype)
    (map_solvableResidual_eq (e.subgroupMap H).toMonoidHom (e.subgroupMap H).surjective)
  rw [map_map] at he ⊢
  exact he

private theorem localResidual_map (e : G ≃* G) (L U : Subgroup G) :
    (localResidual L U).map e.toMonoidHom =
      localResidual (L.map e.toMonoidHom) (U.map e.toMonoidHom) := by
  unfold localResidual
  rw [embeddedResidual_map, map_inf _ _ _ e.injective, map_equiv_normalizer_eq]

private theorem local_root (u : Model S.field.Carrier) (hu : u ∈ LieParabolicSetup.local₂) :
    LieParabolicSetup.highestRoot.map (MulAut.conj u).toMonoidHom ≤ longRootLocal := by
  have hbase : LieParabolicSetup.highestRoot (F:=S.field.Carrier) ≤ longRootLocal := by
    rintro _ ⟨t,rfl⟩
    exact rootA_mem_longRootLocal t.toAdd
  have hn : u ∈ normalizer (longRootLocal (F:=S.field.Carrier) : Set _) := by
    rw [Atlas.G2.SylowParabolicInvariance.normalizer_longRootLocal]
    exact (show LieParabolicSetup.local₂ ≤ LieParabolicSetup.local₂ ⊔ borel from le_sup_left).trans_eq
      LieParabolicSetup.local₂_sup_borel hu
  exact (map_mono hbase).trans_eq (mem_normalizer_iff_map_conj_eq.mp hn)

/-- The full planes of the recognized long roots generate the original L
by their literal relative residuals, with the central preimages retained. -/
theorem root_plane_residuals_generate :
    (⨆ u : Model S.field.Carrier, ⨆ (_ : LieParabolicSetup.highestRoot.map
      (MulAut.conj u).toMonoidHom ≤ longRootLocal),
      localResidual L ((Coordinates.g2 m).preimage
        ((naturalPlane S.field.Carrier).map (Natural.action S.field.Carrier u)))) = L := by
  apply le_antisymm
  · exact iSup_le fun _ => iSup_le fun _ => (localResidual_le _).trans inf_le_left
  · obtain ⟨l,hl⟩ := (Coordinates.g2 m).quotientMap_surjective (alignment S m).val⁻¹
    have hL : L.map (MulAut.conj (l : G)).toMonoidHom = L :=
      mem_normalizer_iff_map_conj_eq.mp (L.le_normalizer l.property)
    have hgen := congrArg (map (MulAut.conj (l : G)).toMonoidHom)
      (planeOrbit_residuals_generate S m)
    rw [hL,Subgroup.map_iSup] at hgen
    conv_lhs => rw [hgen]
    apply iSup_le
    intro I
    obtain ⟨b,hb⟩ := I.property
    change (localResidual L I.val).map (MulAut.conj (l : G)).toMonoidHom ≤ _
    rw [localResidual_map,hL,hb,planeConjugate_eq S m b]
    rw [(Coordinates.g2 m).preimage_conjugate l,hl]
    have hp : (((naturalPlane S.field.Carrier).map
        (Natural.action S.field.Carrier (localProjection S m 0 b).val)).map
          (Natural.action S.field.Carrier (alignment S m).val)).map
          (Natural.action S.field.Carrier (alignment S m).val⁻¹) =
        (naturalPlane S.field.Carrier).map (Natural.action S.field.Carrier (localProjection S m 0 b).val) := by
      rw [←Submodule.map_comp]
      have hi : (Natural.action S.field.Carrier (alignment S m).val⁻¹).comp
          (Natural.action S.field.Carrier (alignment S m).val) = LinearMap.id := by
        apply LinearMap.ext
        intro x
        exact (Natural.action S.field.Carrier).inv_self_apply _ x
      rw [hi,Submodule.map_id]
    have hpm : (Coordinates.g2 m).modelAction (alignment S m).val⁻¹ =
        Natural.action S.field.Carrier (alignment S m).val⁻¹ := rfl
    rw [hpm,hp]
    exact le_iSup_of_le (localProjection S m 0 b).val
      (le_iSup_of_le (local_root D S _ (localProjection S m 0 b).property) le_rfl)
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.G2.CommonPlanes
