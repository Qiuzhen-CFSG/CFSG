module

public import Theory.Representation.MathieuCodeRestriction.CocodeLocal.Octad.Dynamics.Transvections
public import Theory.Representation.MathieuCodeRestriction.CodeLocal
public import Theory.SpecificGroups.BinaryLinear.OuterCyclic.Model
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card

/-!
# The natural binary four-space of a native octad stabilizer

For every native Witt octad O, the intrinsic two-core of its stabilizer is
identified with the additive binary four-space. The coordinates come from
the cocode transvection axis, whose action already intertwines actual M24
conjugation. The self-centralizing core gives the exact kernel of this
linear action. Its image has order 20160 and hence is all of GL4(2).

The binary matrix comparison identifies this linear group with the genuine
central quotient PSL4(2), with its usual matrix action. Thus the quotient
identification and the module coordinates are compatible, and not merely
independent group-order identifications. The construction works at every
octad; native conjugation also transports the ambient cores explicitly.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, H.14.1(4),
printed pp.396–397, citing Aschbacher (1994), 19.8. The transvection-axis
construction is in `MathieuCodeRestriction.CocodeLocal.Octad.Dynamics`.
-/

public section

open Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry
open MathieuCode MathieuCode.CocodeOctad MathieuCode.CocodeOctad.Dynamics
open scoped MatrixGroups Pointwise
namespace Sporadic.Mathieu.M24ChapterHStabilizers.OctadAction
noncomputable section

/-- The natural binary four-dimensional vector space. -/
abbrev Space := Fin 4 → ZMod 2

/-- The setwise stabilizer in the native M24 carrier. -/
abbrev Stabilizer (O : Octad) := octadStabilizer O

/-- The intrinsic two-core, with normality relative to the octad stabilizer. -/
abbrev Core (O : Octad) := pCore 2 (Stabilizer O)

/-- The intrinsic core placed in the native ambient group. -/
abbrev AmbientCore (O : Octad) := (Core O).map (Stabilizer O).subtype

/-- The actual quotient by the intrinsic two-core. -/
abbrev Quotient (O : Octad) := Stabilizer O ⧸ Core O

private def axisMap (O : Octad) : Axis O →ₗ[ZMod 2] Space :=
  (LinearMap.snd (ZMod 2) (ZMod 2) Space).comp
    ((model O).quotientCoordinates.toLinearMap.comp (Axis O).subtype)

private theorem axisMap_bijective (O : Octad) : Function.Bijective (axisMap O) := by
  have hzero (x : Axis O) : ((model O).quotientCoordinates x.val).1 = 0 := by
    obtain ⟨v, hv, hx⟩ := x.property
    rw [← hx, CoordinateModel.quotientCoordinates_mk, (model O).parity]
    exact hv
  constructor
  · intro x y h
    apply Subtype.ext
    apply (model O).quotientCoordinates.injective
    exact Prod.ext ((hzero x).trans (hzero y).symm) h
  · intro v
    obtain ⟨n, hn⟩ := SmallKernelFixed.decode_bijective.2 v
    refine ⟨(model O).axisDirection ((model O).actor n), ?_⟩
    change ((model O).quotientCoordinates
      ((model O).axisDirection ((model O).actor n)).val).2 = v
    rw [CoordinateModel.axisDirection_coordinates, Equiv.symm_apply_apply, hn]

/-- Moment coordinates identify the cocode transvection axis with the binary four-space. -/
def axisCoordinates (O : Octad) : Axis O ≃ₗ[ZMod 2] Space :=
  LinearEquiv.ofBijective (axisMap O) (axisMap_bijective O)

/-- The actual pointwise kernel is the additive group of the transvection axis. -/
def pointwiseCoordinates (O : Octad) :
    octadPointwiseKernel O ≃* Multiplicative Space :=
  (octadTransvectionEquiv O).trans (axisCoordinates O).toAddEquiv.toMultiplicative

/-- The intrinsic core and the ambient pointwise kernel have the same elements. -/
def corePointwiseEquiv (O : Octad) : Core O ≃* octadPointwiseKernel O :=
  ((Core O).equivMapOfInjective (Stabilizer O).subtype (Stabilizer O).subtype_injective).trans
    (MulEquiv.subgroupCongr (octad_core_map_eq_pointwise O))

theorem corePointwiseEquiv_coe (O : Octad) (a : Core O) :
    (corePointwiseEquiv O a).val = a.val.val := by rfl

/-- Binary coordinates for the intrinsic two-core. -/
def coreCoordinates (O : Octad) : Core O ≃* Multiplicative Space :=
  (corePointwiseEquiv O).trans (pointwiseCoordinates O)

/-- Binary coordinates for the core mapped into the native M24 carrier. -/
def ambientCoordinates (O : Octad) : AmbientCore O ≃* Multiplicative Space :=
  (MulEquiv.subgroupCongr (octad_core_map_eq_pointwise O)).trans (pointwiseCoordinates O)

/-- The actual induced cocode-axis action in moment coordinates. -/
def coordinateRepresentation (O : Octad) : Representation (ZMod 2) (Stabilizer O) Space :=
  (axisCoordinates O).conjRingEquiv.toMonoidHom.comp (axisRepresentation O)

/-- Conjugation on the intrinsic core, expressed as binary linear automorphisms. -/
def linearAction (O : Octad) : Stabilizer O →* (Space ≃ₗ[ZMod 2] Space) :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) Space).toMonoidHom.comp
    (coordinateRepresentation O).asGroupHom

theorem linearAction_axisCoordinates (O : Octad) (g : Stabilizer O) (x : Axis O) :
    linearAction O g (axisCoordinates O x) =
      axisCoordinates O (axisRepresentation O g x) := by
  change axisCoordinates O (axisRepresentation O g
    ((axisCoordinates O).symm (axisCoordinates O x))) = _
  rw [LinearEquiv.symm_apply_apply]

theorem pointwiseCoordinates_conjugation (O : Octad) (g : Stabilizer O)
    (a : octadPointwiseKernel O) :
    (pointwiseCoordinates O (kernelConjugate O g a)).toAdd =
      linearAction O g (pointwiseCoordinates O a).toAdd := by
  change axisCoordinates O (octadTransvectionEquiv O (kernelConjugate O g a)).toAdd =
    linearAction O g (axisCoordinates O (octadTransvectionEquiv O a).toAdd)
  rw [octadTransvectionEquiv_equivariant, linearAction_axisCoordinates]

/-- The action kernel is exactly the intrinsic core, by its self-centralizing property. -/
theorem linearAction_ker (O : Octad) : (linearAction O).ker = Core O := by
  apply le_antisymm
  · intro g hg
    apply LinearFourCore.octad_core_selfCentralizing O
    intro k hk
    let a := corePointwiseEquiv O ⟨k, hk⟩
    have he : kernelConjugate O g a = a := by
      apply (pointwiseCoordinates O).injective
      apply Multiplicative.toAdd.injective
      rw [pointwiseCoordinates_conjugation, MonoidHom.mem_ker.mp hg]
      rfl
    have hc : g.val * k.val * g.val⁻¹ = k.val := congrArg Subtype.val he
    apply Subtype.ext
    exact ((mul_inv_eq_iff_eq_mul).mp hc).symm
  · intro g hg
    apply MonoidHom.mem_ker.mpr
    apply LinearEquiv.ext
    intro v
    obtain ⟨x, rfl⟩ := (axisCoordinates O).surjective v
    rw [linearAction_axisCoordinates]
    change axisCoordinates O _ = axisCoordinates O x
    congr 1
    apply Subtype.ext
    exact kernel_fixes_axis O (corePointwiseEquiv O ⟨g, hg⟩) x

theorem core_card (O : Octad) : Nat.card (Core O) = 16 := by
  rw [Core, core_eq_coordinateKernel, card_coordinateKernel]

theorem linearAction_range_card (O : Octad) : Nat.card (linearAction O).range = 20160 := by
  have h := Subgroup.card_mul_index (linearAction O).ker
  rw [Subgroup.index_ker, linearAction_ker, core_card, octadStabilizer_card] at h
  omega

private instance : Finite (Space ≃ₗ[ZMod 2] Space) :=
  Finite.of_injective (fun g : Space ≃ₗ[ZMod 2] Space => (g : Space → Space))
    DFunLike.coe_injective

theorem linearGroup_card : Nat.card (Space ≃ₗ[ZMod 2] Space) = 20160 := by
  calc
    _ = Nat.card (Matrix.GeneralLinearGroup (Fin 4) (ZMod 2)) :=
      (Nat.card_congr (BinaryLinear.OuterCyclic.matrixEquivLinear 4).toEquiv).symm
    _ = ∏ i : Fin 4, (Fintype.card (ZMod 2) ^ 4 - Fintype.card (ZMod 2) ^ i.val) :=
      Matrix.card_GL_field (𝔽 := ZMod 2) 4
    _ = 20160 := by decide

/-- Every binary linear automorphism is induced by native stabilizer conjugation. -/
theorem linearAction_surjective (O : Octad) : Function.Surjective (linearAction O) := by
  apply MonoidHom.range_eq_top.mp
  apply Subgroup.eq_top_of_card_eq
  rw [linearAction_range_card, linearGroup_card]

/-- The faithful quotient action is the full general linear group. -/
def quotientLinearEquiv (O : Octad) : Quotient O ≃* (Space ≃ₗ[ZMod 2] Space) :=
  (QuotientGroup.quotientMulEquivOfEq (linearAction_ker O).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective (linearAction O) (linearAction_surjective O))

theorem quotientLinearEquiv_mk (O : Octad) (g : Stabilizer O) :
    quotientLinearEquiv O (QuotientGroup.mk g) = linearAction O g := by rfl

/-- The actual quotient by the intrinsic core is the matrix group PSL4(2). -/
def quotientEquiv (O : Octad) : Quotient O ≃* PSL(4, ZMod 2) :=
  (quotientLinearEquiv O).trans (BinaryLinear.OuterCyclic.projectiveEquivLinear (by decide)).symm

/-- The usual matrix action of PSL4(2), whose binary scalar center is trivial. -/
def naturalAction : PSL(4, ZMod 2) →* (Space ≃ₗ[ZMod 2] Space) :=
  (BinaryLinear.OuterCyclic.projectiveEquivLinear (by decide : 0 < 4)).toMonoidHom

/-- A special-linear matrix coset acts by its ordinary matrix-vector product. -/
theorem naturalAction_mk (x : SL(4, ZMod 2)) (v : Space) :
    naturalAction (QuotientGroup.mk x) v =
      (x : Matrix (Fin 4) (Fin 4) (ZMod 2)).mulVec v := by
  exact congrArg (fun f : BinaryLinear.OuterCyclic.LinearGroup 4 => f v)
    (BinaryLinear.OuterCyclic.projectiveEquivLinear_mk (by decide : 0 < 4) x)

theorem naturalAction_quotientEquiv (O : Octad) (g : Stabilizer O) :
    naturalAction (quotientEquiv O (QuotientGroup.mk g)) = linearAction O g := by
  exact (BinaryLinear.OuterCyclic.projectiveEquivLinear (by decide : 0 < 4)).apply_symm_apply _

/-- The ambient kernel is the natural module for the actual quotient identification. -/
theorem ambientCoordinates_conjugation (O : Octad) (g : Stabilizer O)
    (v : Space) :
    g.val * ((ambientCoordinates O).symm (Multiplicative.ofAdd v)).val * g.val⁻¹ =
      ((ambientCoordinates O).symm (Multiplicative.ofAdd
        (naturalAction (quotientEquiv O (QuotientGroup.mk g)) v))).val := by
  rw [naturalAction_quotientEquiv]
  let a := (pointwiseCoordinates O).symm (Multiplicative.ofAdd v)
  have h : (pointwiseCoordinates O (kernelConjugate O g a)).toAdd = linearAction O g v := by
    rw [pointwiseCoordinates_conjugation]
    change linearAction O g ((pointwiseCoordinates O) ((pointwiseCoordinates O).symm
      (Multiplicative.ofAdd v))).toAdd = _
    rw [MulEquiv.apply_symm_apply]
    rfl
  have he : kernelConjugate O g a =
      (pointwiseCoordinates O).symm (Multiplicative.ofAdd (linearAction O g v)) := by
    apply (pointwiseCoordinates O).injective
    rw [MulEquiv.apply_symm_apply]
    exact Multiplicative.toAdd.injective h
  exact congrArg Subtype.val he

/-- Conjugation inside the intrinsic two-core of the octad stabilizer. -/
def coreConjugate (O : Octad) (g : Stabilizer O) (a : Core O) : Core O :=
  ⟨g * a.val * g⁻¹, (inferInstance : (Core O).Normal).conj_mem a.val a.property g⟩

theorem coreConjugate_coe (O : Octad) (g : Stabilizer O) (a : Core O) :
    (coreConjugate O g a).val = g * a.val * g⁻¹ := by rfl

/-- The intrinsic kernel is the natural module for the same quotient identification. -/
theorem coreCoordinates_conjugation (O : Octad) (g : Stabilizer O) (a : Core O) :
    (coreCoordinates O (coreConjugate O g a)).toAdd =
      naturalAction (quotientEquiv O (QuotientGroup.mk g)) (coreCoordinates O a).toAdd := by
  rw [naturalAction_quotientEquiv]
  exact pointwiseCoordinates_conjugation O g (corePointwiseEquiv O a)

theorem ambientCore_elementary (O : Octad) : IsElementaryAbelian 2 (AmbientCore O) := by
  let := (LinearFourCore.octad_core_structure O).2
  exact IsElementaryAbelian.map (p := 2) (A := Core O) (Stabilizer O).subtype

theorem ambientCore_card (O : Octad) : Nat.card (AmbientCore O) = 16 := by
  rw [AmbientCore, Subgroup.card_map_of_injective (Stabilizer O).subtype_injective, core_card]

/-- Native geometric conjugation transports the mapped intrinsic two-cores. -/
def ambientTransport (O P : Octad) (g : M24) (hg : g • O.val = P.val) :
    AmbientCore O ≃* AmbientCore P :=
  (MulEquiv.subgroupCongr (octad_core_map_eq_pointwise O)).trans
    ((kernelTransport O P g hg).trans
      (MulEquiv.subgroupCongr (octad_core_map_eq_pointwise P).symm))

/-- Transport is the actual M24 conjugation on elements. -/
theorem ambientTransport_apply (O P : Octad) (g : M24) (hg : g • O.val = P.val)
    (a : AmbientCore O) : (ambientTransport O P g hg a).val = g * a.val * g⁻¹ := by rfl

end
end Sporadic.Mathieu.M24ChapterHStabilizers.OctadAction
