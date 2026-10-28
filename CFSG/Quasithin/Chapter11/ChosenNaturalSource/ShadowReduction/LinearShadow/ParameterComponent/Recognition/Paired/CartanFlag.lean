module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.ParameterComponent.Recognition.Paired.CartanAlignment
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.ParameterComponent.Recognition.Paired.OriginalAction
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.FlagCartan.SL3.Model
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.FlagCartan.Sp4.ModelFlag

/-!
# The intrinsic flags in the simultaneous Cartan coordinates

The original Sylow element conjugates the actual inner Sylow to itself.
The aligned operator therefore permutes its natural actions. Intrinsic
fixed spaces, and fixed spaces modulo earlier stages, show that this
operator preserves the standard SL3 point/plane and all three Sp4 flag
stages. This uses the same inner coordinate change as CartanAlignment,
with the literal original quotient action from OriginalAction.

These source applications remove the flag-preservation premise from the
Cartan power-action argument. The matrix calculation and outside-component
recognition stay with this parameter-component owner; final assembly stays
with qt-d-1222-shadow-linear-geometry.
Source: Aschbacher--Smith, 11.3.5(2), printed pp.771--772.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open Subgroup Representation
open CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ParameterComponent.Paired
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : Chapter12.Section02.ChosenModule T L V} {S : D.NonbinaryNaturalInput}

/-- The aligned operator permutes the actual inner-Sylow actions. Its
inverse conjugation is still performed by the original Sylow element. -/
theorem alignedSylowOperator_moves_inner (c : Coordinates D S.field)
    (b : c.ModelGroup) (t : T) (p : c.ModelGroup)
    (hp : p ∈ ((T : Subgroup G).subgroupOf L).map
      ((MulAut.conj b).toMonoidHom.comp c.quotientMap)) :
    ∃ q ∈ ((T : Subgroup G).subgroupOf L).map
      ((MulAut.conj b).toMonoidHom.comp c.quotientMap), ∀ v,
      c.modelAction p (alignedSylowOperator c b t v) =
        alignedSylowOperator c b t (c.modelAction q v) := by
  obtain ⟨l,hl,rfl⟩ := hp
  let l' := L.normalizerMonoidHom (inclusion D.sylow_normalizes_component t⁻¹) l
  have hl' : l' ∈ (T : Subgroup G).subgroupOf L := by
    change (t : G)⁻¹ * (l : G) * ((t : G)⁻¹)⁻¹ ∈ (T : Subgroup G)
    exact T.mul_mem (T.mul_mem (T.inv_mem t.property) hl)
      (T.inv_mem (T.inv_mem t.property))
  refine ⟨b*c.quotientMap l'*b⁻¹,mem_map_of_mem _ hl',fun v => ?_⟩
  have he : L.normalizerMonoidHom (inclusion D.sylow_normalizes_component t) l' = l := by
    change L.normalizerMonoidHom (inclusion D.sylow_normalizes_component t)
      (L.normalizerMonoidHom (inclusion D.sylow_normalizes_component t⁻¹) l) = l
    rw [map_inv,map_inv]
    exact MulEquiv.apply_symm_apply _ l
  have hh := (alignedSylowOperator_intertwines c b t l' v).symm
  rw [he] at hh
  exact hh

/-- The source Sylow operator preserves both standard SL3 flag spaces
in any of the simultaneous Sylow/Cartan-torsion alignments. -/
theorem source_aligned_flag_sl3
    (m : ActionEquiv D.centralQuotientAction (linearNatural S.field 3))
    (b : SL(3,S.field.Carrier))
    (hb : ((T : Subgroup G).subgroupOf L).map
      ((MulAut.conj b).toMonoidHom.comp (Coordinates.sl3 m).quotientMap) =
        Matrix.PSL3.LinearThree.unipotentSL S.field.Carrier) (t : T) :
    (∀ v ∈ LocalGeometry.SL3.Model.point,
      alignedSylowOperator (Coordinates.sl3 m) b t v ∈ LocalGeometry.SL3.Model.point) ∧
    (∀ v ∈ LocalGeometry.SL3.Model.plane,
      alignedSylowOperator (Coordinates.sl3 m) b t v ∈ LocalGeometry.SL3.Model.plane) := by
  let c : Coordinates D S.field := .sl3 m
  have hmove (p : SL(3,S.field.Carrier))
      (hp : p ∈ Matrix.PSL3.LinearThree.unipotentSL S.field.Carrier) :
      ∃ q ∈ Matrix.PSL3.LinearThree.unipotentSL S.field.Carrier, ∀ v,
        specialLinearNatural 3 p (alignedSylowOperator c b t v) =
          alignedSylowOperator c b t (specialLinearNatural 3 q v) := by
    rw [←hb] at hp ⊢
    exact alignedSylowOperator_moves_inner c b t p hp
  have hpoint : ∀ v ∈ LocalGeometry.SL3.Model.point,
      alignedSylowOperator c b t v ∈ LocalGeometry.SL3.Model.point := by
    intro v hv
    rw [LocalGeometry.SL3.Model.point_fixed] at hv ⊢
    intro p hp
    obtain ⟨q,hq,hqv⟩ := hmove p hp
    rw [hqv,hv q hq]
  refine ⟨hpoint,fun v hv => ?_⟩
  rw [LocalGeometry.SL3.Model.plane_second_fixed] at hv ⊢
  intro p hp
  obtain ⟨q,hq,hqv⟩ := hmove p hp
  rw [hqv]
  exact (map_sub (alignedSylowOperator c b t) _ _ ▸ hpoint _ (hv q hq))

/-- The original symplectic Sylow operator preserves the entire intrinsic
fixed-space filtration in the same simultaneous Cartan coordinates. -/
theorem source_aligned_flag_sp4
    (m : ActionEquiv D.centralQuotientAction
      (restrictScalars (k := ZMod 2) (symplecticNatural (k := S.field.Carrier) 2)))
    (b : Theory.SpecificGroups.SymplecticFour.Sp S.field.Carrier)
    (hb : ((T : Subgroup G).subgroupOf L).map
      ((MulAut.conj b).toMonoidHom.comp (Coordinates.sp4 m).quotientMap) =
        Theory.SpecificGroups.SymplecticFour.unipotent) (t : T) :
    ∀ i : Fin 4, ∀ v ∈ LocalGeometry.Sp4.ModelFlag.stage i,
      alignedSylowOperator (Coordinates.sp4 m) b t v ∈ LocalGeometry.Sp4.ModelFlag.stage i := by
  let c : Coordinates D S.field := .sp4 m
  let e : (Theory.SpecificGroups.SymplecticFour.Vector S.field.Carrier) ≃ₗ[ZMod 2]
      (Theory.SpecificGroups.SymplecticFour.Vector S.field.Carrier) := alignedSylowOperator c b t
  have hmove (p : Theory.SpecificGroups.SymplecticFour.Sp S.field.Carrier)
      (hp : p ∈ Theory.SpecificGroups.SymplecticFour.unipotent) :
      ∃ q ∈ Theory.SpecificGroups.SymplecticFour.unipotent (F := S.field.Carrier), ∀ v,
        p • (e v) = e (q • v) := by
    rw [←hb] at hp ⊢
    exact alignedSylowOperator_moves_inner c b t p hp
  change ∀ i : Fin 4, ∀ v ∈ LocalGeometry.Sp4.ModelFlag.stage i,
    e v ∈ LocalGeometry.Sp4.ModelFlag.stage i
  intro i
  induction i using Fin.induction with
  | zero =>
    intro v hv
    change v ∈ (⊥ : Submodule S.field.Carrier
      (Theory.SpecificGroups.SymplecticFour.Vector S.field.Carrier)) at hv
    rw [Submodule.mem_bot] at hv
    simp only [hv,map_zero]
    exact Submodule.zero_mem _
  | succ i ih =>
    intro v hv
    rw [LocalGeometry.Sp4.ModelFlag.mem_stage_succ_iff] at hv ⊢
    intro p hp
    obtain ⟨q,hq,hqv⟩ := hmove p hp
    rw [hqv,←map_sub]
    exact ih _ (hv q hq)

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ParameterComponent.Paired
