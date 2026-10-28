module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.FlagCartan.Sp4.PlaneAction
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Nonnormalization.Reductions
public import Theory.SpecificGroups.SL2.UpperUnipotent
public import Theory.SpecificGroups.SymplecticFour.LocalStructure.TwoLocalCover.Geometry

/-!
# The original symplectic point orbit

Lift the upper-unipotent Sylow through the actual plane projection. The aligned
plane coordinates identify its fixed line, and fixed lifting through the chosen
central cover identifies its full preimage with the original point. Sylow
conjugacy gives the complete fixed-subgroup family and the source orbit
reduction. Natural-vector transitivity also gives transitivity on all original
field-line preimages and on the lines in the marked plane.

Source: Aschbacher--Smith, 11.2.4, printed pp.769--770. The relative-normality
premise in the final normalizer application belongs to
qt-d-1222-natural-relative-components and is discharged by the local-geometry
assembly owner. All vector preimages retain the literal C_V(L).
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Representation Matrix Matrix.SpecialLinearGroup
open scoped MatrixGroups IsMulCommutative
open Theory.SpecificGroups.SymplecticFour
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.ChapterB.QuasisimpleSource
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Sp4.Orbits
open PlaneAction

private theorem upper_fixed {F : Type*} [Field F] (v : Fin 2 → F) : v 1 = 0 ↔
    ∀ g ∈ upperUnipotent F, specialLinearNatural 2 g v = v := by
  constructor
  · intro hv g hg
    obtain ⟨t,rfl⟩ := (mem_upperUnipotent F g).mp hg
    ext i
    fin_cases i <;> simp [specialLinearNatural_apply,transvection_coe,mulVec,dotProduct,
      Fin.sum_univ_two,hv]
  · intro h
    have he := congrFun (h (transvection zero_ne_one (1:F))
      ((mem_upperUnipotent F _).mpr ⟨1,rfl⟩)) 0
    simpa [specialLinearNatural_apply,transvection_coe,mulVec,dotProduct,Fin.sum_univ_two] using he

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : ChosenModule T L V} (S : D.NonbinaryNaturalInput)
    (m : ActionEquiv D.centralQuotientAction
      (restrictScalars (k := ZMod 2) (symplecticNatural (k := S.field.Carrier) 2)))

/-- A Sylow of the actual plane residual, with upper-unipotent natural image. -/
def planeSylow : Sylow 2 ((flag m S).Li 1) :=
  (Sylow.mapSurjective_surjective (planeProjection_surjective S m) 2
    (upperUnipotentSylow S.field.Carrier 2)).choose

theorem planeSylow_image :
    (planeSylow S m : Subgroup ((flag m S).Li 1)).map (planeProjection S m) =
      upperUnipotent S.field.Carrier :=
  congrArg (fun P : Sylow 2 SL(2,S.field.Carrier) => (P : Subgroup SL(2,S.field.Carrier)))
    (Sylow.mapSurjective_surjective (planeProjection_surjective S m) 2
      (upperUnipotentSylow S.field.Carrier 2)).choose_spec

private theorem point_mem_iff (v : (flag m S).Vi 1) :
    (v : G) ∈ (flag m S).Vi 0 ↔ planeMap S m (Additive.ofMul v) 1 = 0 := by
  let v' : V := ⟨v,D.centralQuotientPreimage_le _ v.property⟩
  have hv := ((Coordinates.sp4 m).mem_preimage ((flag m S).space 1) v').mp v.property
  change ((Coordinates.sp4 m).projection v').toAdd ∈ ModelFlag.movedStage (alignment m) 2 at hv
  rw [ModelFlag.mem_movedStage] at hv
  change (v' : G) ∈ (Coordinates.sp4 m).preimage ((flag m S).space 0) ↔
    alignedPlaneCoordinates S m (planeVectorProjection S m v).toAdd 1 = 0
  rw [(Coordinates.sp4 m).mem_preimage,alignedPlaneCoordinates_apply]
  change ((Coordinates.sp4 m).projection v').toAdd ∈ ModelFlag.movedStage (alignment m) 1 ↔ _
  rw [ModelFlag.mem_movedStage]
  change (alignment m)⁻¹ • (show Vector S.field.Carrier from
    ((Coordinates.sp4 m).projection v').toAdd) ∈ point S.field.Carrier ↔ _
  rw [mem_point_iff]
  exact ⟨And.left, fun h => ⟨h,hv⟩⟩

/-- The original point, including its central kernel, is a Sylow fixed subgroup. -/
theorem planeSylow_fixed :
    (flag m S).Vi 0 = (flag m S).Vi 1 ⊓
      centralizer (((planeSylow S m : Subgroup ((flag m S).Li 1))).map
        ((flag m S).Li 1).subtype : Set G) := by
  let f := flag m S
  ext v
  constructor
  · intro hv
    have hv2 : v ∈ f.Vi 1 := f.Vi_mono (by decide : (0:Fin 3) ≤ 1) hv
    refine ⟨hv2,?_⟩
    rintro x ⟨l,hl,rfl⟩
    have hz := (point_mem_iff S m ⟨v,hv2⟩).mp hv
    have hq : planeProjection S m l ∈ upperUnipotent S.field.Carrier :=
      planeSylow_image S m ▸ mem_map_of_mem _ hl
    let w := (planeVectorProjection S m ⟨v,hv2⟩).toAdd
    have hf : planeAction S m l w = w := by
      apply (alignedPlaneCoordinates S m).injective
      rw [alignedPlaneCoordinates_intertwines]
      exact (upper_fixed _).mp hz _ hq
    have he := component_fixed_of_projection_fixed S m
      ⟨l.val,(localResidual_le _ l.property).1⟩
      ⟨v,D.centralQuotientPreimage_le _ hv2⟩ (congrArg Subtype.val hf)
    exact mul_inv_eq_iff_eq_mul.mp (congrArg Subtype.val he)
  · rintro ⟨hv,hc⟩
    apply (point_mem_iff S m ⟨v,hv⟩).mpr
    apply (upper_fixed _).mpr
    intro g hg
    rw [← planeSylow_image S m] at hg
    obtain ⟨l,hl,rfl⟩ := hg
    rw [← planeMap_intertwines]
    congr 1
    apply Additive.toMul.injective
    apply Subtype.ext
    change (l : G) * v * (l : G)⁻¹ = v
    exact mul_inv_eq_iff_eq_mul.mpr (hc l (mem_map_of_mem _ hl))

private theorem fixed_conjugate (P : Sylow 2 ((flag m S).Li 1))
    (l : (flag m S).Li 1) :
    (((flag m S).Vi 1 ⊓ centralizer
      ((P : Subgroup ((flag m S).Li 1)).map ((flag m S).Li 1).subtype : Set G))).map
        (MulAut.conj (l : G)).toMonoidHom =
      (flag m S).Vi 1 ⊓ centralizer
        (((l • P : Sylow 2 ((flag m S).Li 1)) : Subgroup ((flag m S).Li 1)).map
          ((flag m S).Li 1).subtype : Set G) := by
  let f := flag m S
  have hV : (f.Vi 1).map (MulAut.conj (l : G)).toMonoidHom = f.Vi 1 :=
    mem_normalizer_iff_map_conj_eq.mp (localResidual_le _ l.property).2
  rw [map_inf _ _ _ (MulAut.conj (l : G)).injective,hV,
    Theory.GroupTheory.map_centralizer_equiv]
  have he : ((P : Subgroup (f.Li 1)).map (f.Li 1).subtype).map
      (MulAut.conj (l : G)).toMonoidHom =
      ((l • P : Sylow 2 (f.Li 1)) : Subgroup (f.Li 1)).map (f.Li 1).subtype := by
    rw [Sylow.coe_subgroup_smul]
    change _ = ((P : Subgroup (f.Li 1)).map (MulAut.conj l).toMonoidHom).map _
    rw [Subgroup.map_map,Subgroup.map_map]
    congr 1
  exact congrArg (fun X : Subgroup G => f.Vi 1 ⊓ centralizer (X : Set G)) he

/-- The L₂-orbit of V₁ is the complete Sylow fixed-subgroup family in V₂. -/
theorem point_orbit_eq_sylow_fixed :
    {U : Subgroup G | ∃ l ∈ (flag m S).Li 1,
      ((flag m S).Vi 0).map (MulAut.conj l).toMonoidHom = U} =
    {U : Subgroup G | ∃ P : Sylow 2 ((flag m S).Li 1),
      U = (flag m S).Vi 1 ⊓ centralizer
        ((P : Subgroup ((flag m S).Li 1)).map ((flag m S).Li 1).subtype : Set G)} := by
  let P := planeSylow S m
  ext U
  constructor
  · rintro ⟨l,hl,rfl⟩
    refine ⟨(⟨l,hl⟩ : (flag m S).Li 1) • P,?_⟩
    rw [planeSylow_fixed]
    exact fixed_conjugate S m P ⟨l,hl⟩
  · rintro ⟨Q,rfl⟩
    obtain ⟨l,hl⟩ := MulAction.exists_smul_eq ((flag m S).Li 1) P Q
    refine ⟨l,l.property,?_⟩
    rw [planeSylow_fixed]
    rw [fixed_conjugate,hl]

/-- The actual fixed family supplies the normalizer-orbit step of 11.2.4. -/
theorem point_orbit
    (hN : normalizer ((flag m S).Vi 1 : Set G) ≤
      normalizer ((flag m S).Li 1 : Set G)) :
    ∀ y ∈ normalizer ((flag m S).Vi 1 : Set G),
      ∃ l ∈ (flag m S).Li 1,
        ((flag m S).Vi 0).map (MulAut.conj y).toMonoidHom =
          ((flag m S).Vi 0).map (MulAut.conj l).toMonoidHom :=
  WeakClosure.Nonnormalization.point_orbit_of_sylow_fixed D S
    (flag m S) hN (planeSylow S m) (planeSylow_fixed S m)

/-- L is transitive on the original preimages of all field lines. -/
theorem field_lines_transitive
    (U W : Submodule S.field.Carrier (Vector S.field.Carrier))
    (hU : Module.finrank S.field.Carrier U = 1)
    (hW : Module.finrank S.field.Carrier W = 1) :
    ∃ l : L, ((Coordinates.sp4 m).preimage U).map (MulAut.conj (l : G)).toMonoidHom =
      (Coordinates.sp4 m).preimage W := by
  obtain ⟨v,hv,hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (show U ≠ ⊥ from by
    intro h; rw [h,finrank_bot] at hU; omega)
  obtain ⟨w,hw,hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (show W ≠ ⊥ from by
    intro h; rw [h,finrank_bot] at hW; omega)
  obtain ⟨a,ha⟩ := TwoLocalCover.nonzero_vector_transitive hv0 hw0
  obtain ⟨l,hl⟩ := (Coordinates.sp4 m).quotientMap_surjective a
  refine ⟨l,?_⟩
  rw [← (Coordinates.sp4 m).preimage_map_action l U]
  congr 1
  rw [eq_span_singleton_of_mem_of_finrank_eq_one hU hv hv0,
    eq_span_singleton_of_mem_of_finrank_eq_one hW hw hw0]
  rw [Submodule.map_span,Set.image_singleton]
  rw [hl]
  exact congrArg (fun v => Submodule.span S.field.Carrier {v}) ha

/-- L₂ is transitive on the original preimages of field lines in its plane. -/
theorem plane_field_lines_transitive
    (U W : Submodule S.field.Carrier (Vector S.field.Carrier))
    (hU : Module.finrank S.field.Carrier U = 1)
    (hW : Module.finrank S.field.Carrier W = 1)
    (hUP : U ≤ (flag m S).space 1) (hWP : W ≤ (flag m S).space 1) :
    ∃ l : (flag m S).Li 1,
      ((Coordinates.sp4 m).preimage U).map (MulAut.conj (l : G)).toMonoidHom =
        (Coordinates.sp4 m).preimage W := by
  obtain ⟨v,hv,hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (show U ≠ ⊥ from by
    intro h; rw [h,finrank_bot] at hU; omega)
  obtain ⟨w,hw,hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (show W ≠ ⊥ from by
    intro h; rw [h,finrank_bot] at hW; omega)
  let e := alignedPlaneCoordinates S m
  let v' : (flag m S).space 1 := ⟨v,hUP hv⟩
  let w' : (flag m S).space 1 := ⟨w,hWP hw⟩
  obtain ⟨a,ha⟩ := Matrix.SL2.exists_mulVec_eq S.field.Carrier (e v') (e w')
    (fun h => hv0 (congrArg Subtype.val (e.injective (h.trans e.map_zero.symm))))
    (fun h => hw0 (congrArg Subtype.val (e.injective (h.trans e.map_zero.symm))))
  obtain ⟨l,hl⟩ := planeProjection_surjective S m a
  have he := alignedPlaneCoordinates_intertwines S m l v'
  rw [hl] at he
  have hact : planeAction S m l v' = w' := e.injective (he.trans ha)
  let l' : L := ⟨l,(localResidual_le _ l.property).1⟩
  have hvec : (Coordinates.sp4 m).modelAction ((Coordinates.sp4 m).quotientMap l') v = w :=
    congrArg Subtype.val hact
  refine ⟨l,?_⟩
  rw [← (Coordinates.sp4 m).preimage_map_action l']
  congr 1
  rw [eq_span_singleton_of_mem_of_finrank_eq_one hU hv hv0,
    eq_span_singleton_of_mem_of_finrank_eq_one hW hw hw0,
    Submodule.map_span,Set.image_singleton,hvec]

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Sp4.Orbits
