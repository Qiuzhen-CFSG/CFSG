module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Symplectic.RadicalAction.PointModel
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.FlagCartan.Transport

/-!
# Identifying the literal point-normalizer residual

The original projection onto the marked field module identifies N_L(V₁)
with the preimage of the point stabilizer. Its solvable residual therefore
maps onto the solvable residual of that stabilizer. A genuine symplectic
point conjugacy and the nonbinary parabolic calculation identify this image
with the conjugate point local, discharging the local-image premise of the
native radical calculation. No equality O₂(L)=V is used.
Source: Aschbacher--Smith, the opening of §11.1 and assertion (!) in 11.5.7,
printed pp.760--761 and 782.
-/

set_option backward.isDefEq.respectTransparency false
public noncomputable section
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Symplectic.PointModel
open Subgroup Theory.SpecificGroups.SymplecticFour LocalGeometry
open CFSG.Quasithin.Chapter12.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : ChosenModule T L V} {E : Geometry D} (m : MarkedFlag E)

private theorem residual_image (W : Submodule E.input.field.Carrier
    (Vector E.input.field.Carrier)) :
    image m (localResidual L ((Coordinates.sp4 m.action).preimage W)) =
      residualIn ((Coordinates.sp4 m.action).modelStabilizer W) := by
  let c := Coordinates.sp4 m.action
  ext x
  constructor
  · rintro ⟨l,hl,rfl⟩
    let y : localResidual L (c.preimage W) := ⟨l,hl⟩
    refine ⟨(c.residualProjection W y).val,(c.residualProjection W y).property,?_⟩
    exact c.residualProjection_coe W y
  · rintro ⟨x,hx,rfl⟩
    obtain ⟨y,hy⟩ := (c.residualProjection_surjective W) ⟨x,hx⟩
    refine ⟨⟨y,(localResidual_le _ y.property).1⟩,y.property,?_⟩
    exact (c.residualProjection_coe W y).symm.trans (congrArg (fun z => z.val.val) hy)

private theorem modelStabilizer_eq (W : Submodule E.input.field.Carrier
    (Vector E.input.field.Carrier)) :
    (Coordinates.sp4 m.action).modelStabilizer W = stabilizer W := by
  change Representation.BinaryOffender.subspaceStabilizer
    (Representation.restrictScalars (k := ZMod 2)
      (Representation.symplecticNatural (k := E.input.field.Carrier) 2))
    (W.restrictScalars (ZMod 2)) = stabilizer W
  ext a
  change (∀ x, a • x ∈ W ↔ x ∈ W) ↔ a ∈ stabilizer W
  constructor
  · intro h
    exact (mem_stabilizer_iff W a).mpr (fun x hx => (h x).mpr hx)
  · intro h x
    constructor
    · intro hx
      simpa only [inv_smul_smul] using
        (mem_stabilizer_iff W a⁻¹).mp ((stabilizer W).inv_mem h) (a • x) hx
    · exact (mem_stabilizer_iff W a).mp h x

private theorem stabilizer_conjugate (W : Submodule E.input.field.Carrier
    (Vector E.input.field.Carrier)) (g : Sp E.input.field.Carrier) :
    stabilizer (W.map (toLinear g).toLinearMap) =
      (stabilizer W).map (MulAut.conj g).toMonoidHom := by
  apply le_antisymm
  · intro a ha
    refine ⟨g⁻¹ * a * g,?_,by simp [MulAut.conj_apply,mul_assoc]⟩
    apply (mem_stabilizer_iff _ _).mpr
    intro v hv
    have h := (mem_stabilizer_iff _ _).mp ha (g • v) ⟨v,hv,rfl⟩
    obtain ⟨w,hw,he⟩ := h
    have he' : g⁻¹ • (a • (g • v)) = w := by
      rw [← show g • w = a • (g • v) from he, inv_smul_smul]
    rw [mul_smul, mul_smul, he']
    exact hw
  · rintro _ ⟨a,ha,rfl⟩
    apply (mem_stabilizer_iff _ _).mpr
    rintro _ ⟨v,hv,rfl⟩
    refine ⟨a • v,(mem_stabilizer_iff _ _).mp ha v hv,?_⟩
    change g • (a • v) = (g * a * g⁻¹) • (g • v)
    simp only [mul_smul,inv_smul_smul]

/-- The literal normalizer residual becomes the conjugate point local under
any genuine symplectic point coordinate. Its two-core has not been identified
with V, and no radical-action conclusion is assumed. -/
theorem local_identification (g : Sp E.input.field.Carrier)
    (hpoint : m.flag.space 0 = (point E.input.field.Carrier).map (toLinear g).toLinearMap) :
    image m E.L₁ = pointLocal.map (MulAut.conj g).toMonoidHom := by
  have hpre : E.V₁ = (Coordinates.sp4 m.action).preimage
      ((point E.input.field.Carrier).map (toLinear g).toLinearMap) := by
    rw [m.point_preimage]
    change (Coordinates.sp4 m.action).preimage (m.flag.space 0) = _
    rw [hpoint]
  change image m (localResidual L E.V₁) = _
  rw [hpre, residual_image, modelStabilizer_eq, stabilizer_conjugate]
  change residualIn ((stabilizer (point E.input.field.Carrier)).map
    (MulAut.conj g).toMonoidHom) = pointLocal.map (MulAut.conj g).toMonoidHom
  calc
    _ = (residualIn (pointParabolic (F := E.input.field.Carrier))).map
        (MulAut.conj g).toMonoidHom :=
      (residualIn_map (pointParabolic (F := E.input.field.Carrier)) (MulAut.conj g)).symm
    _ = _ := congrArg (Subgroup.map (MulAut.conj g).toMonoidHom)
      (pointParabolic_solvableResidual_eq E.input.field.card_eq E.input.nonbinary)

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Symplectic.PointModel
