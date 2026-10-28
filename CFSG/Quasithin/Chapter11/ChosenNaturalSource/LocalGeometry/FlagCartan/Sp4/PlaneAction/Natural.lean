module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.FlagCartan.Sp4
public import Theory.Representation.GeneralLinearNatural
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Uniqueness

/-!
# The original marked symplectic plane action

Undo the common Sylow alignment on the actual field plane and project its
residual onto SL₂. The original binary vector projection intertwines this
natural action. Its kernel remains the literal relative centralizer C_V(L);
no splitting of the chosen central cover is assumed.

Source: Aschbacher--Smith, Chapter 11, 11.1.3 and 11.2.4, printed pp.764--765
and 769--770. Fixed-vector lifting and the full-plane core calculation are
separate from this quotient-plane identification.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Representation
open scoped MatrixGroups IsMulCommutative
open Matrix
open Theory.SpecificGroups.SymplecticFour
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.ChapterB.QuasisimpleSource
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Sp4.PlaneAction
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : ChosenModule T L V} (S : D.NonbinaryNaturalInput)
    (m : ActionEquiv D.centralQuotientAction
      (restrictScalars (k := ZMod 2) (symplecticNatural (k := S.field.Carrier) 2)))

/-- The same aligned residual projection used in the source quotient. -/
def localProjection (i : Fin 2) : (flag m S).Li i →* standardLocal (F := S.field) i :=
  (modelResidualEquiv m S.nonbinary i).toMonoidHom.comp
    ((Coordinates.sp4 m).residualProjection ((flag m S).space i.castSucc))

theorem localProjection_surjective (i : Fin 2) : Function.Surjective (localProjection S m i) :=
  (modelResidualEquiv m S.nonbinary i).surjective.comp
    ((Coordinates.sp4 m).residualProjection_surjective _)

theorem localProjection_coe (i : Fin 2) (l : (flag m S).Li i) :
    (localProjection S m i l).val = (alignment m)⁻¹ *
      (show Sp S.field.Carrier from (Coordinates.sp4 m).quotientMap
        ⟨l.val,(localResidual_le _ l.property).1⟩) * alignment m := by
  fin_cases i <;>
    change (MulAut.conj (alignment m)).symm
      (((Coordinates.sp4 m).residualProjection _ l).val.val) = _
  all_goals
    rw [(Coordinates.sp4 m).residualProjection_coe]
    rfl

theorem localProjection_ker_isTwoGroup (i : Fin 2) :
    IsPGroup 2 (localProjection S m i).ker := by
  have he : (localProjection S m i).ker =
      ((Coordinates.sp4 m).residualProjection ((flag m S).space i.castSucc)).ker := by
    ext l
    change modelResidualEquiv m S.nonbinary i
      (((Coordinates.sp4 m).residualProjection ((flag m S).space i.castSucc)) l) = 1 ↔ _
    rw [map_eq_one_iff _ (modelResidualEquiv m S.nonbinary i).injective]
    rfl
  rw [he]
  exact (Coordinates.sp4 m).residualProjection_ker_isTwoGroup _

/-- The literal upper-left action on the plane after undoing the alignment. -/
def planeProjection : (flag m S).Li 1 →* SL(2,S.field.Carrier) :=
  (Plane.quotientMap (F := S.field.Carrier)).comp (localProjection S m 1)

theorem planeProjection_surjective : Function.Surjective (planeProjection S m) :=
  Plane.quotientMap_surjective.comp (localProjection_surjective S m 1)

theorem planeProjection_ker : (planeProjection S m).ker = pCore 2 ((flag m S).Li 1) := by
  change ((Plane.quotientMap (F := S.field.Carrier)).comp (localProjection S m 1)).ker = _
  rw [← MonoidHom.comap_ker, Plane.quotientMap_ker,
    ← planeLocal_core_eq S.field.card_eq S.nonbinary]
  exact (localProjection S m 1).comap_pCore_of_ker_isPGroup
    (localProjection_surjective S m 1) (localProjection_ker_isTwoGroup S m 1)

/-- Undo the published common Sylow alignment on the actual field plane. -/
def alignedPlaneCoordinates : (flag m S).space 1 ≃ₗ[S.field.Carrier] (Fin 2 → S.field.Carrier) :=
  (((toLinear (alignment m)).ofSubmodules (plane S.field.Carrier) ((flag m S).space 1)
    (by rfl)).symm).trans planeEquiv

/-- First two coordinates in the inverse of the original alignment. -/
theorem alignedPlaneCoordinates_apply (v : (flag m S).space 1) (i : Fin 2) :
    alignedPlaneCoordinates S m v i = ((alignment m)⁻¹ • (show Vector S.field.Carrier from v.val)) (.inl i) := by
  change ((toLinear (alignment m)).symm (show Vector S.field.Carrier from v.val)) (.inl i) = _
  have ha : (toLinear (alignment m)).symm = toLinear (alignment m)⁻¹ :=
    (map_inv toLinear (alignment m)).symm
  rw [ha]
  rfl

/-- The quotient-plane action uses the original component quotient. -/
def planeAction : Representation S.field.Carrier ((flag m S).Li 1) ((flag m S).space 1) :=
  Subrepresentation.toRepresentation (ρ := (Coordinates.sp4 m).modelAction.comp
    ((Coordinates.sp4 m).quotientMap.comp (inclusion ((localResidual_le _).trans inf_le_left))))
      { toSubmodule := (flag m S).space 1
        apply_mem_toSubmodule := by
          intro l x hx
          exact (((Coordinates.sp4 m).mem_normalizer_preimage_iff ((flag m S).space 1)
            ⟨l.val,(localResidual_le _ l.property).1⟩).mp
              (localResidual_le _ l.property).2 x).mpr hx }

/-- The actual residual acts naturally in the aligned two coordinates. -/
theorem alignedPlaneCoordinates_intertwines (l : (flag m S).Li 1)
    (v : (flag m S).space 1) :
    alignedPlaneCoordinates S m (planeAction S m l v) =
      specialLinearNatural 2 (planeProjection S m l) (alignedPlaneCoordinates S m v) := by
  let w : Vector S.field.Carrier := (alignment m)⁻¹ • (show Vector S.field.Carrier from v.val)
  have hw : w ∈ plane S.field.Carrier := by
    have h := ((toLinear (alignment m)).ofSubmodules (plane S.field.Carrier)
      ((flag m S).space 1) (by rfl)).symm v |>.property
    have ha : (toLinear (alignment m)).symm = toLinear (alignment m)⁻¹ :=
      (map_inv toLinear (alignment m)).symm
    change (toLinear (alignment m)).symm (show Vector S.field.Carrier from v.val) ∈ _ at h
    simpa only [ha, toLinear_apply] using h
  let q : Sp S.field.Carrier := (Coordinates.sp4 m).quotientMap
    ⟨l.val,(localResidual_le _ l.property).1⟩
  have hc : (localProjection S m 1 l).val = (alignment m)⁻¹ * q * alignment m :=
    localProjection_coe S m 1 l
  have he : (alignment m)⁻¹ • (show Vector S.field.Carrier from (planeAction S m l v).val) =
      (localProjection S m 1 l).val • w := by
    change (alignment m)⁻¹ • (q • (show Vector S.field.Carrier from v.val)) = _
    rw [hc]
    simp only [mul_smul, w, smul_inv_smul]
  have hvw : alignedPlaneCoordinates S m v = fun j => w (.inl j) :=
    funext fun j => alignedPlaneCoordinates_apply S m v j
  ext i
  rw [alignedPlaneCoordinates_apply, he, hvw]
  change ((localProjection S m 1 l).val.val *ᵥ w) (.inl i) =
    ((Plane.quotientMap (localProjection S m 1 l)).val *ᵥ
      (fun j => w (.inl j))) i
  have hw0 (j : Fin 2) : w (.inr j) = 0 := hw j
  simp [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, hw0, Plane.quotientMap, Matrix.toBlocks₁₁]


/-- Restrict the original vector quotient without losing its central kernel. -/
def planeVectorProjection : (flag m S).Vi 1 →* Multiplicative ((flag m S).space 1) where
  toFun v := Multiplicative.ofAdd ⟨((Coordinates.sp4 m).projection
    ⟨v.val,D.centralQuotientPreimage_le _ v.property⟩).toAdd,
      ((Coordinates.sp4 m).mem_preimage _ _).mp v.property⟩
  map_one' := by
    apply congrArg Multiplicative.ofAdd
    apply Subtype.ext
    exact congrArg Multiplicative.toAdd ((Coordinates.sp4 m).projection.map_one)
  map_mul' v w := by
    apply congrArg Multiplicative.ofAdd
    apply Subtype.ext
    exact congrArg Multiplicative.toAdd ((Coordinates.sp4 m).projection.map_mul
      ⟨v.val,D.centralQuotientPreimage_le _ v.property⟩
      ⟨w.val,D.centralQuotientPreimage_le _ w.property⟩)

theorem planeVectorProjection_surjective : Function.Surjective (planeVectorProjection S m) := by
  intro x
  obtain ⟨v,hv⟩ := (Coordinates.sp4 m).projection_surjective (Multiplicative.ofAdd x.toAdd.val)
  have hvp : v.val ∈ (flag m S).Vi 1 :=
    ((Coordinates.sp4 m).mem_preimage _ _).mpr (by
      change ((Coordinates.sp4 m).projection v).toAdd ∈ (flag m S).space 1
      rw [hv]
      exact x.toAdd.property)
  refine ⟨⟨v.val,hvp⟩, ?_⟩
  apply congrArg Multiplicative.ofAdd
  apply Subtype.ext
  exact congrArg Multiplicative.toAdd hv

/-- The kernel is the literal relative C_V(L), not an assumed trivial subgroup. -/
theorem planeVectorProjection_ker : (planeVectorProjection S m).ker =
    (centralizer (L : Set G)).subgroupOf ((flag m S).Vi 1) := by
  ext v
  change planeVectorProjection S m v = 1 ↔ v.val ∈ centralizer (L : Set G)
  rw [← (Coordinates.sp4 m).projection_eq_one_iff
    ⟨v.val,D.centralQuotientPreimage_le _ v.property⟩]
  change Multiplicative.ofAdd _ = Multiplicative.ofAdd _ ↔ _ = _
  constructor
  · intro h
    exact congrArg (fun z => Multiplicative.ofAdd z.toAdd.val) h
  · intro h
    apply congrArg Multiplicative.ofAdd
    apply Subtype.ext
    exact congrArg Multiplicative.toAdd h

/-- The original vector quotient in natural two-space coordinates. -/
def naturalPlaneVectorProjection : (flag m S).Vi 1 →* Multiplicative (Fin 2 → S.field.Carrier) :=
  (alignedPlaneCoordinates S m).toAddEquiv.toMultiplicative.toMonoidHom.comp
    (planeVectorProjection S m)

theorem naturalPlaneVectorProjection_surjective :
    Function.Surjective (naturalPlaneVectorProjection S m) :=
  (alignedPlaneCoordinates S m).toAddEquiv.toMultiplicative.surjective.comp
    (planeVectorProjection_surjective S m)

theorem naturalPlaneVectorProjection_ker : (naturalPlaneVectorProjection S m).ker =
    (centralizer (L : Set G)).subgroupOf ((flag m S).Vi 1) := by
  rw [← planeVectorProjection_ker]
  ext v
  change (alignedPlaneCoordinates S m).toAddEquiv.toMultiplicative
    (planeVectorProjection S m v) = 1 ↔ _
  rw [map_eq_one_iff _ (alignedPlaneCoordinates S m).toAddEquiv.toMultiplicative.injective]
  rfl

/-- The requested surjective binary linear natural-plane map on the full preimage. -/
def planeMap : Additive ((flag m S).Vi 1) →ₗ[ZMod 2] (Fin 2 → S.field.Carrier) :=
  let h := (naturalPlaneVectorProjection S m).toAdditiveLeft
  { h with map_smul' := ZMod.map_smul h }

theorem planeMap_surjective : Function.Surjective (planeMap S m) :=
  naturalPlaneVectorProjection_surjective S m

/-- The actual ambient action, retaining the same relative normalizer embedding. -/
theorem planeMap_intertwines (l : (flag m S).Li 1) (v : Additive ((flag m S).Vi 1)) :
    planeMap S m (Components.flagAction (flag m S) 1
      ⟨l,(localResidual_le _ l.property).2⟩ v) =
      specialLinearNatural 2 (planeProjection S m l) (planeMap S m v) := by
  change alignedPlaneCoordinates S m ((planeVectorProjection S m _).toAdd) = _
  have he : (planeVectorProjection S m
      (((flag m S).Vi 1).normalizerMonoidHom
        ⟨l,(localResidual_le _ l.property).2⟩ v.toMul)).toAdd =
      planeAction S m l (planeVectorProjection S m v.toMul).toAdd := by
    apply Subtype.ext
    exact (Coordinates.sp4 m).projection_component_conjugation
      ⟨l.val,(localResidual_le _ l.property).1⟩
      ⟨v.toMul.val,D.centralQuotientPreimage_le _ v.toMul.property⟩
  exact (congrArg (alignedPlaneCoordinates S m) he).trans
    (alignedPlaneCoordinates_intertwines S m l _)

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Sp4.PlaneAction
