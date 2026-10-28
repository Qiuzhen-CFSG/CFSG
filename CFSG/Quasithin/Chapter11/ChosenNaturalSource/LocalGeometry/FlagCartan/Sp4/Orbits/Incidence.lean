module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.FlagCartan.Sp4
public import Theory.SpecificGroups.SymplecticFour.LocalStructure.Point.Coordinates
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.FlagCartan.Sp4.PlaneAction.Natural
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.FlagCartan.G2.ResidualIncidence.Incidence.Transport
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.PlaneOrbit

/-!
# Incidence of the original symplectic plane orbit

The standard plane and its middle-coordinate Weyl conjugate meet in the
point and span its perpendicular three-space. Every point-residual translate
lies in this interval. The common flag alignment and original central
quotient transport both identities to the full ambient preimages, including
C_V(L). These are the incidence inputs to source 11.1.4.

Source: Aschbacher--Smith, opening §11.1 and 11.1.4, pp.760--761,765.
-/

@[expose] public noncomputable section
open Subgroup Matrix
open Theory.SpecificGroups.SymplecticFour
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Sp4.Orbits
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

/-- The point residual fixes the point and preserves its perpendicular hyperplane. -/
theorem pointLocal_plane_interval (g : pointLocal (F := F)) :
    point F ≤ (plane F).map (toLinear g.val).toLinearMap ∧
      (plane F).map (toLinear g.val).toLinearMap ≤ ModelFlag.hyperplane := by
  constructor
  · apply Submodule.span_le.mpr
    intro x hx
    rcases Set.mem_singleton_iff.mp hx with rfl
    refine ⟨e 0,e_mem_plane 0,?_⟩
    exact (mem_pointLocal_iff_fixed g.val).mp g.property
  · rintro x ⟨y,hy,rfl⟩
    rw [ModelFlag.mem_hyperplane]
    change (g.val.val *ᵥ y) (.inr 0) = 0
    simp [Matrix.mulVec, dotProduct, pointLocal_row, hy 0]

/-- The Weyl element exchanging the two middle coordinates, inside the point residual. -/
def middleSwap : pointLocal (F := F) :=
  pointLevi ⟨!![0,1;1,0], by simp [Matrix.det_fin_two, CharTwo.neg_eq]⟩

omit [Finite F] in
private theorem middleSwap_action (x : Vector F) :
    (middleSwap (F := F)).val • x =
      Sum.elim ![x (.inl 0),x (.inr 1)] ![x (.inr 0),x (.inl 1)] := by
  funext i
  cases i with
  | inl i => fin_cases i <;>
      simp [middleSwap,pointLevi,pointLeviMatrix,Matrix.mulVec,dotProduct,
        Fintype.sum_sum_type,Fin.sum_univ_two]
  | inr i => fin_cases i <;>
      simp [middleSwap,pointLevi,pointLeviMatrix,Matrix.mulVec,dotProduct,
        Fintype.sum_sum_type,Fin.sum_univ_two]

/-- Two explicit point-residual planes meet in the standard point. -/
theorem plane_inf_middleSwap :
    plane F ⊓ (plane F).map (toLinear (middleSwap (F := F)).val).toLinearMap = point F := by
  apply le_antisymm
  · rintro x ⟨hx,hy⟩
    rw [mem_point_iff]
    refine ⟨?_,hx⟩
    obtain ⟨y,hy,rfl⟩ := hy
    change ((middleSwap (F := F)).val • y) (.inl 1) = 0
    rw [middleSwap_action]
    exact hy 1
  · exact le_inf point_le_plane (pointLocal_plane_interval middleSwap).1

/-- The same two planes span the perpendicular three-space. -/
theorem plane_sup_middleSwap :
    plane F ⊔ (plane F).map (toLinear (middleSwap (F := F)).val).toLinearMap =
      ModelFlag.hyperplane := by
  have hle : plane F ⊔ (plane F).map (toLinear (middleSwap (F := F)).val).toLinearMap ≤
      ModelFlag.hyperplane := sup_le ModelFlag.plane_le_hyperplane
        (pointLocal_plane_interval middleSwap).2
  apply Submodule.eq_of_le_of_finrank_eq hle
  have hdim := Submodule.finrank_sup_add_finrank_inf_eq (plane F)
    ((plane F).map (toLinear (middleSwap (F := F)).val).toLinearMap)
  rw [plane_inf_middleSwap,finrank_point,finrank_plane,
    LinearEquiv.finrank_map_eq,finrank_plane] at hdim
  rw [ModelFlag.hyperplane_finrank]
  omega

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Sp4.Orbits

set_option backward.isDefEq.respectTransparency false
open Representation
open scoped MatrixGroups
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.ChapterB.QuasisimpleSource
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Sp4.Orbits
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : ChosenModule T L V} (S : D.NonbinaryNaturalInput)
    (m : ActionEquiv D.centralQuotientAction
      (restrictScalars (k := ZMod 2) (symplecticNatural (k := S.field.Carrier) 2)))

abbrev planeOrbit := Normalizers.planeOrbit ((flag m S).Vi 1) ((flag m S).Li 0)

theorem flag_space_eq (i : Fin 3) : (flag m S).space i =
    (ModelFlag.stage i.succ).map (toLinear (alignment m)).toLinearMap := rfl

theorem planeConjugate_eq (l : (flag m S).Li 0) :
    ((flag m S).Vi 1).map (MulAut.conj (l : G)).toMonoidHom =
      (Coordinates.sp4 m).preimage
        (((plane S.field.Carrier).map
          (toLinear (PlaneAction.localProjection S m 0 l).val).toLinearMap).map
            (toLinear (alignment m)).toLinearMap) := by
  change ((Coordinates.sp4 m).preimage ((flag m S).space 1)).map
    (MulAut.conj (l : G)).toMonoidHom = _
  rw [(Coordinates.sp4 m).preimage_conjugate
    ⟨l.val,(localResidual_le _ l.property).1⟩,flag_space_eq S m 1]
  change (Coordinates.sp4 m).preimage
    (((plane S.field.Carrier).map (toLinear (alignment m)).toLinearMap).map
      ((Coordinates.sp4 m).modelAction ((Coordinates.sp4 m).quotientMap
        ⟨l.val,(localResidual_le _ l.property).1⟩))) = _
  congr 1
  rw [← Submodule.map_comp,← Submodule.map_comp]
  congr 1
  apply LinearMap.ext
  intro x
  change (show Sp S.field.Carrier from
    (Coordinates.sp4 m).quotientMap ⟨l.val,(localResidual_le _ l.property).1⟩) •
    ((alignment m) • x) = (alignment m) • ((PlaneAction.localProjection S m 0 l).val • x)
  rw [PlaneAction.localProjection_coe]
  simp only [mul_smul,smul_inv_smul]

theorem planeOrbit_interval (U : Subgroup G) (hU : U ∈ planeOrbit S m) :
    (flag m S).Vi 0 ≤ U ∧ U ≤ (flag m S).Vi 2 := by
  obtain ⟨l,rfl⟩ := hU
  rw [planeConjugate_eq S m l]
  have hi := pointLocal_plane_interval (PlaneAction.localProjection S m 0 l)
  constructor
  · change (Coordinates.sp4 m).preimage ((flag m S).space 0) ≤ _
    apply ((Coordinates.sp4 m).preimage_le_iff _ _).mpr
    rw [flag_space_eq S m 0]
    exact Submodule.map_mono hi.1
  · change _ ≤ (Coordinates.sp4 m).preimage ((flag m S).space 2)
    apply ((Coordinates.sp4 m).preimage_le_iff _ _).mpr
    rw [flag_space_eq S m 2]
    exact Submodule.map_mono hi.2

theorem exists_planeConjugate_meet_join :
    ∃ l : (flag m S).Li 0,
      (flag m S).Vi 1 ⊓ ((flag m S).Vi 1).map (MulAut.conj (l : G)).toMonoidHom =
        (flag m S).Vi 0 ∧
      (flag m S).Vi 1 ⊔ ((flag m S).Vi 1).map (MulAut.conj (l : G)).toMonoidHom =
        (flag m S).Vi 2 := by
  obtain ⟨l,hl⟩ := PlaneAction.localProjection_surjective S m 0 middleSwap
  refine ⟨l,?_,?_⟩
  · rw [planeConjugate_eq,hl]
    change (Coordinates.sp4 m).preimage ((flag m S).space 1) ⊓ _ =
      (Coordinates.sp4 m).preimage ((flag m S).space 0)
    rw [← (Coordinates.sp4 m).preimage_inf,flag_space_eq S m 1,flag_space_eq S m 0]
    change (Coordinates.sp4 m).preimage
      (((plane S.field.Carrier).map (toLinear (alignment m)).toLinearMap) ⊓
        (((plane S.field.Carrier).map (toLinear (middleSwap (F := S.field.Carrier)).val).toLinearMap).map
          (toLinear (alignment m)).toLinearMap)) = _
    rw [← Submodule.map_inf _ (toLinear (alignment m)).injective,plane_inf_middleSwap]
    rfl
  · rw [planeConjugate_eq,hl]
    change (Coordinates.sp4 m).preimage ((flag m S).space 1) ⊔ _ =
      (Coordinates.sp4 m).preimage ((flag m S).space 2)
    rw [← (Coordinates.sp4 m).preimage_sup,flag_space_eq S m 1,flag_space_eq S m 2]
    change (Coordinates.sp4 m).preimage
      (((plane S.field.Carrier).map (toLinear (alignment m)).toLinearMap) ⊔
        (((plane S.field.Carrier).map (toLinear (middleSwap (F := S.field.Carrier)).val).toLinearMap).map
          (toLinear (alignment m)).toLinearMap)) = _
    rw [← Submodule.map_sup,plane_sup_middleSwap]
    rfl

private theorem planeOrbit_base : (flag m S).Vi 1 ∈ planeOrbit S m := by
  refine ⟨1,?_⟩
  ext x
  simp

theorem planeOrbit_meet : (⨅ U : planeOrbit S m,U.val) = (flag m S).Vi 0 := by
  obtain ⟨l,hm,-⟩ := exists_planeConjugate_meet_join S m
  apply le_antisymm
  · calc
      (⨅ U : planeOrbit S m,U.val) ≤ (flag m S).Vi 1 ⊓
          ((flag m S).Vi 1).map (MulAut.conj (l : G)).toMonoidHom :=
        le_inf (iInf_le (fun U : planeOrbit S m => U.val) ⟨_,planeOrbit_base S m⟩)
          (iInf_le (fun U : planeOrbit S m => U.val) ⟨_,⟨l,rfl⟩⟩)
      _ = (flag m S).Vi 0 := hm
  · exact le_iInf fun U => (planeOrbit_interval S m U.val U.property).1

theorem planeOrbit_span : (⨆ U : planeOrbit S m,U.val) = (flag m S).Vi 2 := by
  obtain ⟨l,-,hj⟩ := exists_planeConjugate_meet_join S m
  apply le_antisymm
  · exact iSup_le fun U => (planeOrbit_interval S m U.val U.property).2
  · rw [← hj]
    exact sup_le (le_iSup (fun U : planeOrbit S m => U.val) ⟨_,planeOrbit_base S m⟩)
      (le_iSup (fun U : planeOrbit S m => U.val) ⟨_,⟨l,rfl⟩⟩)

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Sp4.Orbits
