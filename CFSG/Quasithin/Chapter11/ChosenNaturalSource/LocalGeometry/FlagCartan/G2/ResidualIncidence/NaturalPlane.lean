module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.FlagCartan.G2.ResidualIncidence.PlaneProjection
public import Theory.Representation.GeneralLinearNatural

/-!
# Natural coordinates on the original G₂ quotient plane

Undoing the common Sylow alignment carries the marked plane to the standard
plane in the six-dimensional octonion quotient. Its first two coordinates
identify the action with the natural SL₂ action, using the literal short-local
projection. Composing with the original vector projection gives a surjective
natural two-space quotient of the entire ambient plane preimage. Both the
actor two-core and the possible central vector kernel are retained exactly.

Source: Aschbacher--Smith 11.0.2 and opening §11.1, printed pp.759--761.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open Subgroup Representation
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open scoped MatrixGroups

namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.G2.ResidualIncidence
open Atlas.G2 Atlas.G2.Natural Atlas.G2.Natural.OrthogonalCover
open Atlas.G2.Natural.OrthogonalCover.SylowFlag
open Atlas.G2.LieParabolicSetup

section Model
variable (F : Type*) [Field F] [CharP F 2]

/-- Read the two coordinates surviving on the standard quotient plane. -/
def planeRead : Natural.Space F →ₗ[F] (Fin 2 → F) where
  toFun x i := Restricted.NaturalCoordinates.coordinates F x (i.castLE (by decide : 2 ≤ 6))
  map_add' x y := by ext i; simp
  map_smul' a x := by ext i; simp

/-- On an octonion representative these are literally its first two coordinates. -/
theorem planeRead_mk (x : TraceZero F) :
    planeRead F (mk F x) = ![x.val 0,x.val 1] := by
  ext i
  fin_cases i <;> simp [planeRead, Restricted.NaturalCoordinates.projection]

/-- The standard plane lift is a right inverse to coordinate reading. -/
theorem planeRead_lift (v : Fin 2 → F) :
    planeRead F (mk F (planeLift F v)) = v := by
  rw [planeRead_mk]
  ext i
  fin_cases i <;> rfl

/-- The standard octonion plane is the field two-space. -/
def standardPlaneCoordinates : naturalPlane F ≃ₗ[F] (Fin 2 → F) :=
  { (planeRead F).domRestrict (naturalPlane F) with
    invFun v := ⟨mk F (planeLift F v), ⟨_,⟨v,rfl⟩,rfl⟩⟩
    left_inv := by
      rintro ⟨_,_,⟨v,rfl⟩,rfl⟩
      apply Subtype.ext
      change mk F (planeLift F (planeRead F (mk F (planeLift F v)))) = _
      rw [planeRead_lift]
    right_inv := planeRead_lift F }

/-- The short-local SL₂ map is the actual action on these two coordinates. -/
theorem planeRead_intertwines (g : local₁ (F := F)) (v : Natural.Space F)
    (hv : v ∈ naturalPlane F) :
    planeRead F (Natural.action F g.val v) =
      specialLinearNatural 2 (shortSLHom g) (planeRead F v) := by
  obtain ⟨_,⟨w,rfl⟩,rfl⟩ := hv
  rw [planeRead_lift, Natural.action_mk]
  have hw : (planeLift F w).val =
      w 0 • Atlas.SplitOctonion.basisVector 0 + w 1 • Atlas.SplitOctonion.basisVector 1 := by
    ext i
    fin_cases i <;> simp [planeLift, Atlas.SplitOctonion.basisVector]
  rw [planeRead_mk]
  ext i
  fin_cases i <;>
    simp [traceZeroAction_val, hw, map_add, map_smul, specialLinearNatural_apply,
      Matrix.mulVec, dotProduct, Fin.sum_univ_two, shortSLHom, shortRepresentation, mul_comm]

end Model

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : ChosenModule T L V} (S : D.NonbinaryNaturalInput)
    (m : ActionEquiv D.centralQuotientAction
      (restrictScalars (k := ZMod 2) (g2Natural S.field.Carrier)))

/-- Natural field coordinates after undoing the original marked alignment. -/
def planeCoordinates : (flag S m).space 1 ≃ₗ[S.field.Carrier] (Fin 2 → S.field.Carrier) :=
  (((Transport.linear (Natural.action S.field.Carrier) (alignment S m).val).ofSubmodules
      (naturalPlane S.field.Carrier) ((flag S m).space 1) (by
        rw [flag_space_eq S m 1]
        rfl)).symm).trans (standardPlaneCoordinates S.field.Carrier)

/-- The chosen coordinates use the inverse of the same alignment as the flag. -/
theorem planeCoordinates_apply (v : (flag S m).space 1) :
    planeCoordinates S m v = planeRead S.field.Carrier
      (Natural.action S.field.Carrier (alignment S m).val⁻¹ v.val) := rfl

/-- The literal original plane residual acts through its natural SL₂ projection. -/
theorem planeCoordinates_intertwines (l : (flag S m).Li 1) (v : (flag S m).space 1) :
    planeCoordinates S m (planeAction S m l v) =
      specialLinearNatural 2 (planeProjection S m l) (planeCoordinates S m v) := by
  have hv : Natural.action S.field.Carrier (alignment S m).val⁻¹ v.val ∈
      naturalPlane S.field.Carrier :=
    ((Transport.linear (Natural.action S.field.Carrier) (alignment S m).val).ofSubmodules
      (naturalPlane S.field.Carrier) ((flag S m).space 1) (by
        rw [flag_space_eq S m 1]
        rfl)).symm v |>.property
  rw [planeCoordinates_apply, planeCoordinates_apply]
  change planeRead S.field.Carrier
    (Natural.action S.field.Carrier (alignment S m).val⁻¹
      (Natural.action S.field.Carrier ((coordinates S m).quotientMap
        ⟨l.val,(localResidual_le _ l.property).1⟩) v.val)) = _
  rw [← Module.End.mul_apply, ← map_mul]
  have he : (alignment S m).val⁻¹ * (show Model S.field.Carrier from (coordinates S m).quotientMap
      ⟨l.val,(localResidual_le _ l.property).1⟩) =
      (localProjection S m 1 l).val * (alignment S m).val⁻¹ := by
    rw [localProjection_coe]
    simp only [mul_assoc, mul_inv_cancel, mul_one]
  rw [he, map_mul, Module.End.mul_apply]
  exact planeRead_intertwines S.field.Carrier (localProjection S m 1 l) _ hv

/-- The kernel of the quotient-plane action is exactly the original two-core. -/
theorem planeAction_fixes_iff (l : (flag S m).Li 1) :
    (∀ v, planeAction S m l v = v) ↔ l ∈ pCore 2 ((flag S m).Li 1) := by
  rw [← planeProjection_ker]
  change (∀ v, planeAction S m l v = v) ↔ planeProjection S m l = 1
  constructor
  · intro h
    apply specialLinearNatural_injective 2
    apply LinearMap.ext
    intro w
    obtain ⟨v,rfl⟩ := (planeCoordinates S m).surjective w
    rw [← planeCoordinates_intertwines, h]
    simp
  · intro h v
    apply (planeCoordinates S m).injective
    rw [planeCoordinates_intertwines, h]
    simp

/-- The original ambient plane maps onto the natural field two-space. -/
def naturalPlaneVectorProjection : (flag S m).Vi 1 →*
    Multiplicative (Fin 2 → S.field.Carrier) :=
  ((planeCoordinates S m).toAddEquiv.toMultiplicative.toMonoidHom).comp
    (planeVectorProjection S m)

/-- All natural vectors are images of original ambient plane elements. -/
theorem naturalPlaneVectorProjection_surjective :
    Function.Surjective (naturalPlaneVectorProjection S m) :=
  (planeCoordinates S m).toAddEquiv.toMultiplicative.surjective.comp
    (planeVectorProjection_surjective S m)

/-- The original central vector kernel is preserved by the new coordinates. -/
theorem naturalPlaneVectorProjection_ker : (naturalPlaneVectorProjection S m).ker =
    (centralizer (L : Set G)).subgroupOf ((flag S m).Vi 1) := by
  rw [← planeVectorProjection_ker]
  ext v
  change (planeCoordinates S m).toAddEquiv.toMultiplicative (planeVectorProjection S m v) = 1 ↔ _
  exact map_eq_one_iff _ (planeCoordinates S m).toAddEquiv.toMultiplicative.injective

/-- In the ambient group the vector kernel is exactly V intersect C_G(L). -/
theorem naturalPlaneVectorProjection_ker_map :
    (naturalPlaneVectorProjection S m).ker.map ((flag S m).Vi 1).subtype =
      V ⊓ centralizer (L : Set G) := by
  rw [naturalPlaneVectorProjection_ker]
  ext x
  constructor
  · rintro ⟨v, hv, rfl⟩
    exact ⟨D.centralQuotientPreimage_le _ v.property, hv⟩
  · intro hx
    exact ⟨⟨x, (flag S m).centralizer_le_Vi 1 hx⟩, hx.2, rfl⟩

/-- Ambient conjugation intertwines the natural vector and actor projections. -/
theorem naturalPlaneVectorProjection_intertwines (l : (flag S m).Li 1)
    (v : (flag S m).Vi 1) :
    naturalPlaneVectorProjection S m (planeConjugation S m l v) =
      Multiplicative.ofAdd (specialLinearNatural 2 (planeProjection S m l)
        (naturalPlaneVectorProjection S m v).toAdd) := by
  change Multiplicative.ofAdd (planeCoordinates S m
    (planeVectorProjection S m (planeConjugation S m l v)).toAdd) = _
  rw [planeVectorProjection_intertwines]
  exact congrArg Multiplicative.ofAdd (planeCoordinates_intertwines S m l _)

/-- The actual central quotient of the ambient plane is the natural two-space. -/
def naturalPlaneCentralQuotientEquiv :
    (((flag S m).Vi 1) ⧸ (planeVectorProjection S m).ker) ≃*
      Multiplicative (Fin 2 → S.field.Carrier) :=
  (planeCentralQuotientEquiv S m).trans (planeCoordinates S m).toAddEquiv.toMultiplicative

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.G2.ResidualIncidence
