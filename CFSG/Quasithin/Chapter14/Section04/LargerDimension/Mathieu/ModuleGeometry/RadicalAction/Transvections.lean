module

public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Mathieu.ModuleGeometry.RadicalAction.Operators
public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Mathieu.ModuleGeometry.RadicalAction.FieldFrame
public import Mathlib.LinearAlgebra.Transvection.Basic

/-!
# A native radical transvection and its moved F₄-point

The explicit binary matrix acts on the literal six-space as
`u ↦ u + u₁ e₀` in the checked F₄-frame. It is therefore a genuine
F₄-transvection, and its moved space contains the whole marked F₄-point.
Its cyclic subgroup acts by transvections with this center.

The only placement input puts this concrete matrix in the intersection
of the actual point two-core and the genuine triple-cover component.
Parabolic membership, the action formula, the transvection assertion and
both ambient and restricted moved-point inclusions are proved here.

Source: Aschbacher–Smith 14.4.12, final paragraph, printed p.1012.
-/

@[expose] public section

open Matrix Representation.SL2FourNatural
open Sporadic.Mathieu M22TripleCover M22TripleCover.Unitary
open M22TripleCover.Uniqueness.PointRestriction (fieldModule fieldTower)
open Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreLinearModel
open Representation.BinaryOffender
open scoped Matrix
namespace CFSG.Quasithin.Chapter14.Section04.LargerDimension.Mathieu.ModuleGeometry.Native.RadicalAction

noncomputable section
local instance transvectionFieldModule : Module F BinarySpace :=
  fieldModule binaryRepresentation binaryRepresentation_faithful
local instance transvectionFieldTower : IsScalarTower (ZMod 2) F BinarySpace :=
  fieldTower binaryRepresentation binaryRepresentation_faithful

theorem transvection_field_action (h : nativeTransvectionUnit ∈ actionGroup) (u : Fin 3 → F) :
    parabolicRepresentation (parabolicTransvection h) (fieldFrame u) =
      fieldFrame (u + u 1 • Pi.single 0 1) := by
  rw [← frameEquiv_fieldSplit, transvection_action, modelAction_frameEquiv]
  have he : ∀ u : Fin 3 → F, transvectionMatrix *ᵥ fieldSplit u =
      fieldSplit (u + u 1 • Pi.single 0 1) := by decide +kernel
  rw [he, frameEquiv_fieldSplit]

def centerFunctional : Module.Dual F parabolicFieldSpace :=
  (LinearMap.proj 1).comp fieldFrame.symm.toLinearMap

def fieldTransvection : parabolicFieldSpace ≃ₗ[F] parabolicFieldSpace :=
  LinearEquiv.transvection (f := centerFunctional) (v := fieldFrame (Pi.single 0 1))
    (by simp [centerFunctional])

theorem fieldTransvection_is_transvection :
    fieldTransvection ∈ LinearEquiv.transvections F parabolicFieldSpace :=
  LinearEquiv.mem_transvections _

theorem fieldTransvection_is_native (h : nativeTransvectionUnit ∈ actionGroup)
    (v : parabolicFieldSpace) :
    (fieldTransvection v : BinarySpace) = representation (nativeTransvection h) v := by
  obtain ⟨u, rfl⟩ := fieldFrame.surjective v
  have he := congrArg (fun w : parabolicSpace => (w : BinarySpace))
    (transvection_field_action h u)
  calc
    _ = (fieldFrame (u + u 1 • Pi.single 0 1) : BinarySpace) := by
      apply congrArg Subtype.val
      change fieldFrame u + centerFunctional (fieldFrame u) • fieldFrame (Pi.single 0 1) = _
      simp [centerFunctional]
    _ = _ := he.symm

theorem nativeTransvection_formula (h : nativeTransvectionUnit ∈ actionGroup)
    (v : parabolicFieldSpace) :
    representation (nativeTransvection h) v =
      (v : BinarySpace) + centerFunctional v • markedVector := by
  have he := (fieldTransvection_is_native h v).symm
  change representation (nativeTransvection h) v =
    (v : BinarySpace) + centerFunctional v • (fieldFrame (Pi.single 0 1) : BinarySpace) at he
  rwa [fieldFrame_first] at he

def transvectionSubgroup (h : nativeTransvectionUnit ∈ actionGroup) : Subgroup Group :=
  Subgroup.zpowers (nativeTransvection h)

theorem transvectionSubgroup_le_intersection (h : nativeTransvectionUnit ∈ actionGroup)
    (hp : nativeTransvection h ∈ pointRadical ⊓ componentInclusion.range) :
    transvectionSubgroup h ≤ (pointRadical ⊓ componentInclusion.range) ⊓ parabolic := by
  apply Subgroup.zpowers_le.mpr
  exact ⟨hp, nativeTransvection_mem_parabolic h⟩

theorem transvectionSubgroup_elements (h : nativeTransvectionUnit ∈ actionGroup)
    {g : Group} (hg : g ∈ transvectionSubgroup h) :
    g = 1 ∨ g = nativeTransvection h := by
  have hs : nativeTransvection h ^ 2 = 1 := by
    apply Subtype.ext
    apply Units.ext
    change nativeTransvectionMatrix ^ 2 = 1
    rw [pow_two, nativeTransvection_square]
  have hf : IsOfFinOrder (nativeTransvection h) :=
    isOfFinOrder_iff_pow_eq_one.mpr ⟨2, by decide, hs⟩
  obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp (hf.mem_zpowers_iff_mem_range_orderOf.mp hg)
  have hn' := Finset.mem_range.mp hn
  have ho := orderOf_le_of_pow_eq_one (by decide : 0 < 2) hs
  have hn : n = 0 ∨ n = 1 := by omega
  rcases hn with rfl | rfl <;> simp

/-- Every element of the actual cyclic subgroup induces an F₄-transvection
    with center in the marked F₄-point; the identity corresponds to the zero form. -/
theorem transvectionSubgroup_action (h : nativeTransvectionUnit ∈ actionGroup)
    (g : Group) (hg : g ∈ transvectionSubgroup h) :
    ∃ f : Module.Dual F parabolicFieldSpace,
      f ⟨markedVector, markedVector_mem_parabolic⟩ = 0 ∧
      ∀ v : parabolicFieldSpace,
        representation g v = (v : BinarySpace) + f v • markedVector := by
  rcases transvectionSubgroup_elements h hg with rfl | rfl
  · exact ⟨0, rfl, by intro v; simp⟩
  · refine ⟨centerFunctional, ?_, nativeTransvection_formula h⟩
    have he : (⟨markedVector, markedVector_mem_parabolic⟩ : parabolicFieldSpace) =
        fieldFrame (Pi.single 0 1) := Subtype.ext fieldFrame_first.symm
    rw [he]
    simp [centerFunctional]

theorem markedPoint_le_transvection_moved (h : nativeTransvectionUnit ∈ actionGroup) :
    binaryPoint markedVector ≤
      subspaceCommutator representation parabolicSpace (transvectionSubgroup h) := by
  intro w hw
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hw
  let v : parabolicFieldSpace := fieldFrame (Pi.single 1 a)
  have hf : centerFunctional v = a := by simp [v, centerFunctional]
  have he : representation (nativeTransvection h) v - (v : BinarySpace) =
      a • markedVector := by
    rw [nativeTransvection_formula, hf, add_sub_cancel_left]
  rw [← he]
  exact Submodule.subset_span ⟨nativeTransvection h, Subgroup.mem_zpowers _, v, v.property, rfl⟩

/-- The placement input mentions only two concrete matrix memberships. The
    transvection and moved-point assertions are proved above from the native action. -/
theorem exists_radical_transvection_subgroup
    (hp : nativeTransvectionUnit ∈
      (pointRadical ⊓ componentInclusion.range).map actionGroup.subtype) :
    ∃ T : Subgroup Group,
      T ≤ (pointRadical ⊓ componentInclusion.range) ⊓ parabolic ∧
      (∀ g ∈ T, ∃ f : Module.Dual F parabolicFieldSpace,
        f ⟨markedVector, markedVector_mem_parabolic⟩ = 0 ∧
        ∀ v : parabolicFieldSpace,
          representation g v = (v : BinarySpace) + f v • markedVector) ∧
      binaryPoint markedVector ≤ subspaceCommutator representation parabolicSpace T := by
  obtain ⟨g, hg, he⟩ := hp
  have hG : nativeTransvectionUnit ∈ actionGroup := he ▸ g.property
  have hg' : nativeTransvection hG = g := Subtype.ext he.symm
  have hmem : nativeTransvection hG ∈ pointRadical ⊓ componentInclusion.range := by rwa [hg']
  exact ⟨transvectionSubgroup hG, transvectionSubgroup_le_intersection hG hmem,
    transvectionSubgroup_action hG, markedPoint_le_transvection_moved hG⟩


/-- The first moved-point inclusion on the literal restricted quotient. -/
theorem markedPoint_le_radical_component_moved
    (hp : nativeTransvectionUnit ∈
      (pointRadical ⊓ componentInclusion.range).map actionGroup.subtype) :
    (binaryPoint markedVector).comap parabolicSpace.subtype ≤
      subspaceCommutator parabolicRepresentation ⊤
        ((pointRadical ⊓ componentInclusion.range).subgroupOf parabolic) := by
  obtain ⟨g, hg, he⟩ := hp
  have hG : nativeTransvectionUnit ∈ actionGroup := he ▸ g.property
  have hg' : nativeTransvection hG = g := Subtype.ext he.symm
  have hmem : nativeTransvection hG ∈ pointRadical ⊓ componentInclusion.range := by rwa [hg']
  intro w hw
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hw
  let v : parabolicFieldSpace := fieldFrame (Pi.single 1 a)
  have hf : centerFunctional v = a := by simp [v, centerFunctional]
  let v₀ : parabolicSpace := ⟨v, v.property⟩
  have hd : parabolicRepresentation (parabolicTransvection hG) v₀ - v₀ = w := by
    apply Subtype.ext
    change representation (nativeTransvection hG) v - (v : BinarySpace) = (w : BinarySpace)
    rw [nativeTransvection_formula, hf, add_sub_cancel_left]
    exact ha
  rw [← hd]
  exact Submodule.subset_span ⟨parabolicTransvection hG, hmem, v₀, Submodule.mem_top, rfl⟩

end
end CFSG.Quasithin.Chapter14.Section04.LargerDimension.Mathieu.ModuleGeometry.Native.RadicalAction
