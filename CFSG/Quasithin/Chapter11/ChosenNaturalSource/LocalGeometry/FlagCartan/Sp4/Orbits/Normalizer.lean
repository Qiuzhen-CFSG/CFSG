module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.FlagCartan.Sp4.Orbits.Displacement
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.FlagCartan.Sp4.Orbits.Generation

/-!
# Corrected symplectic plane-family normalizer control

The ordinary fixed-space clause in the proof of source 11.1.4 cannot supply
its plane family: even the natural symplectic unipotent group fixes only
the point. The original full-cover Sylow calculation proves the corresponding
ambient obstruction. The plane is instead defined by displacement into V1.

The point residual fixes V1, and V1 is its intrinsic fixed subgroup in V3.
Common normalizers therefore preserve V1 and permute the displacement family.
Together with orbit-residual generation, this gives both normalizer
containments of 11.1.4. Only the genuine preceding unique noncentral-component
input remains; qt-d-1222-natural-relative-components produces it and the
source assembly owner discharges it.

Source: Aschbacher--Smith, 11.1.3--4, printed p.765, with the full-cover
fixed-space convention of I.2.3(1a), printed p.413.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Representation
open scoped IsMulCommutative
open Theory.SpecificGroups.SymplecticFour
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.ChapterB.QuasisimpleSource
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Sp4.Orbits

/-- The ordinary fixed-plane proposal already fails in the natural model. -/
theorem standardPlane_not_fixed_by_unipotent {F : Type*} [Field F] :
    ¬ ∀ x ∈ plane F, ∀ u ∈ unipotent (F := F), u • x = x := by
  intro h
  have hx := (fixedBy_unipotent_iff (e (F := F) 1)).mp (h _ (e_mem_plane 1))
  have hz := (mem_point_iff _).mp hx |>.1
  simp [Theory.SpecificGroups.SymplecticFour.e] at hz

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : ChosenModule T L V} (S : D.NonbinaryNaturalInput)
    (m : ActionEquiv D.centralQuotientAction
      (restrictScalars (k := ZMod 2) (symplecticNatural (k := S.field.Carrier) 2)))

private theorem pointMap_action (l : (flag m S).Li 0) (x : Vector S.field.Carrier) :
    pointMap S m l • ((alignment m) • x) =
      (alignment m) • ((PlaneAction.localProjection S m 0 l).val • x) := by
  rw [PlaneAction.localProjection_coe]
  simp only [mul_smul,smul_inv_smul]
  rfl

/-- The point residual fixes every original vector above the marked point. -/
theorem first_le_point_centralizer :
    (flag m S).Vi 0 ≤ centralizer ((flag m S).Li 0 : Set G) := by
  intro v hv r hr
  let w : V := ⟨v,D.centralQuotientPreimage_le _ hv⟩
  have hw : ((Coordinates.sp4 m).projection w).toAdd ∈
      (point S.field.Carrier).map (toLinear (alignment m)).toLinearMap :=
    ((Coordinates.sp4 m).mem_preimage _ w).mp hv
  obtain ⟨x,hx,he⟩ := hw
  have hf : (PlaneAction.localProjection S m 0 ⟨r,hr⟩).val • x = x := by
    obtain ⟨a,rfl⟩ := Submodule.mem_span_singleton.mp hx
    change toLinear (PlaneAction.localProjection S m 0 ⟨r,hr⟩).val (a • e (F := S.field.Carrier) 0) = a • e (F := S.field.Carrier) 0
    rw [map_smul]
    change a • ((PlaneAction.localProjection S m 0 ⟨r,hr⟩).val • e (F := S.field.Carrier) 0) = a • e (F := S.field.Carrier) 0
    rw [(mem_pointLocal_iff_fixed _).mp (PlaneAction.localProjection S m 0 ⟨r,hr⟩).property]
  have hmodel : (Coordinates.sp4 m).modelAction
      ((Coordinates.sp4 m).quotientMap ⟨r,(localResidual_le _ hr).1⟩)
        ((Coordinates.sp4 m).projection w).toAdd = ((Coordinates.sp4 m).projection w).toAdd := by
    change pointMap S m ⟨r,hr⟩ •
      (show Vector S.field.Carrier from ((Coordinates.sp4 m).projection w).toAdd) =
      (show Vector S.field.Carrier from ((Coordinates.sp4 m).projection w).toAdd)
    change (alignment m) • x =
      (show Vector S.field.Carrier from ((Coordinates.sp4 m).projection w).toAdd) at he
    rw [← he,pointMap_action,hf]
  have h := PlaneAction.component_fixed_of_projection_fixed S m
    ⟨r,(localResidual_le _ hr).1⟩ w hmodel
  exact mul_inv_eq_iff_eq_mul.mp (congrArg Subtype.val h)

/-- V1 is intrinsic to V3 and its point residual, including the central kernel. -/
theorem first_eq_third_inf_point_centralizer :
    (flag m S).Vi 0 = (flag m S).Vi 2 ⊓ centralizer ((flag m S).Li 0 : Set G) := by
  apply le_antisymm
  · exact le_inf ((flag m S).Vi_mono (by decide)) (first_le_point_centralizer S m)
  · calc
      _ ≤ (flag m S).Vi 2 ⊓ centralizer
          (((pointSylow S m : Subgroup ((flag m S).Li 0))).map ((flag m S).Li 0).subtype : Set G) :=
        inf_le_inf_left _ (centralizer_le (map_subtype_le _))
      _ = (flag m S).Vi 0 := (pointSylow_fixed_third S m).symm

theorem normalizer_preserves_first :
    normalizer ((flag m S).Vi 2 : Set G) ⊓ normalizer ((flag m S).Li 0 : Set G) ≤
      normalizer ((flag m S).Vi 0 : Set G) := by
  rw [first_eq_third_inf_point_centralizer S m]
  exact (inf_le_inf_left _ (normalizer_le_normalizer_centralizer _)).trans
    inf_normalizer_le_normalizer_inf

/-- The ordinary Sylow fixed family is not the source plane orbit. -/
theorem planeOrbit_ne_sylow_fixed :
    planeOrbit S m ≠ Set.range (fun P : Sylow 2 ((flag m S).Li 0) =>
      (flag m S).Vi 2 ⊓ centralizer
        ((P : Subgroup ((flag m S).Li 0)).map ((flag m S).Li 0).subtype : Set G)) := by
  intro h
  have hline : (flag m S).Vi 0 ∈ planeOrbit S m := by
    rw [h]
    exact ⟨pointSylow S m,(pointSylow_fixed_third S m).symm⟩
  obtain ⟨l,hl⟩ := hline
  have he := (Coordinates.sp4 m).preimage_injective (hl.trans (planeConjugate_eq S m l))
  have hd := congrArg (fun U : Submodule S.field.Carrier (Coordinates.sp4 m).Space =>
    Module.finrank S.field.Carrier U) he
  rw [(flag m S).dimension 0,LinearEquiv.finrank_map_eq,
    LinearEquiv.finrank_map_eq,finrank_plane] at hd
  contradiction

private theorem seed_normalizes_first : V ≤ normalizer ((flag m S).Vi 0 : Set G) := by
  let := D.elementary
  exact ((le_centralizer_iff_isMulCommutative.mpr inferInstance :
    V ≤ centralizer (V : Set G)).trans
      (centralizer_le (D.centralQuotientPreimage_le _))).trans (Subgroup.centralizer_le_normalizer _)

/-- The base plane is a displacement subgroup modulo the first full preimage. -/
theorem second_eq_displacement :
    (flag m S).Vi 1 = G2.Displacement.subgroup V ((flag m S).Vi 0)
      ((pointSylow S m : Subgroup ((flag m S).Li 0)).map ((flag m S).Li 0).subtype) := by
  ext v
  rw [G2.Displacement.mem_subgroup (seed_normalizes_first S m)]
  constructor
  · intro hv
    have hV := D.centralQuotientPreimage_le _ hv
    refine ⟨hV,?_⟩
    rintro p ⟨q,hq,rfl⟩
    exact (mem_second_iff_displacement S m ⟨v,hV⟩).mp hv ⟨q,hq⟩
  · rintro ⟨hV,hv⟩
    apply (mem_second_iff_displacement S m ⟨v,hV⟩).mpr
    intro p
    exact hv _ (mem_map_of_mem _ p.property)

/-- The corrected family uses displacement into V1, restricted to V3. -/
theorem planeOrbit_eq_sylow_displacement :
    planeOrbit S m = Set.range (fun P : Sylow 2 ((flag m S).Li 0) =>
      G2.Displacement.subgroup ((flag m S).Vi 2) ((flag m S).Vi 0)
        ((P : Subgroup ((flag m S).Li 0)).map ((flag m S).Li 0).subtype)) := by
  have he : planeOrbit S m = Set.range (fun P : Sylow 2 ((flag m S).Li 0) =>
      G2.Displacement.subgroup V ((flag m S).Vi 0)
        ((P : Subgroup ((flag m S).Li 0)).map ((flag m S).Li 0).subtype)) :=
    G2.Displacement.orbit_eq_range
      (((localResidual_le _).trans inf_le_left).trans D.normalizes)
      ((localResidual_le _).trans inf_le_right) (pointSylow S m) (second_eq_displacement S m)
  have hr (P : Sylow 2 ((flag m S).Li 0)) :
      G2.Displacement.subgroup ((flag m S).Vi 2) ((flag m S).Vi 0)
        ((P : Subgroup ((flag m S).Li 0)).map ((flag m S).Li 0).subtype) =
      G2.Displacement.subgroup V ((flag m S).Vi 0)
        ((P : Subgroup ((flag m S).Li 0)).map ((flag m S).Li 0).subtype) := by
    apply G2.Displacement.restrict_eq (D.centralQuotientPreimage_le _)
    apply (planeOrbit_interval S m _ _).2
    rw [he]
    exact ⟨P,rfl⟩
  simpa only [hr] using he

/-- Common normalizers permute the actual plane family through Sylow displacement. -/
theorem normalizer_permutes_planes {g : G}
    (hg : g ∈ normalizer ((flag m S).Vi 2 : Set G) ⊓ normalizer ((flag m S).Li 0 : Set G)) :
    ∀ U ∈ planeOrbit S m, U.map (MulAut.conj g).toMonoidHom ∈ planeOrbit S m := by
  intro U hU
  rw [planeOrbit_eq_sylow_displacement S m] at hU ⊢
  obtain ⟨P,rfl⟩ := hU
  obtain ⟨Q,hQ⟩ := G2.Displacement.normalizer_permutes hg.1
    (normalizer_preserves_first S m hg) hg.2 P
  exact ⟨Q,hQ.symm⟩

/-- Both source 11.1.4 containments, retaining only the earlier component input. -/
theorem source_normalizerControl
    (hunique : Source.UniqueNoncentralComponent
      (normalizer ((flag m S).Vi 1 : Set G)) ((flag m S).Vi 1) ((flag m S).Li 1)) :
    Source.NormalizerControl ((flag m S).Vi 2) ((flag m S).Vi 0) ((flag m S).Li 0)
      (normalizer (L : Set G)) := by
  constructor
  · intro g hg
    apply normalizes_of_plane_permutation S m hunique
    intro U hU
    rwa [Normalizers.sectionCentralizer_fixes (planeOrbit_interval S m U hU).1
      (planeOrbit_interval S m U hU).2 hg]
  · intro g hg
    exact normalizes_of_plane_permutation S m hunique (normalizer_permutes_planes S m hg)

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Sp4.Orbits
