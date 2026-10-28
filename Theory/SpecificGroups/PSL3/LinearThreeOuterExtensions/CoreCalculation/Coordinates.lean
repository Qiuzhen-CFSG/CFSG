module

public import Theory.SpecificGroups.PSL3.LinearThreeOuterExtensions.Locals
public import Theory.SpecificGroups.PSL3.LinearThreeLocalCoordinates

/-!
# Literal block maps and coefficient transport for the PSL₃ locals

The maps here compose the original SL₃-to-PSL₃ projection with the proved
local two-core quotient. Their matrix entries are the lower-right block for
the point local and the upper-left block for the line local. Entrywise field
transport preserves both locals and intertwines these very block maps with
the coefficient action on SL₂. No automorphism decomposition is chosen.

Source: Aschbacher–Smith, F.1.12, printed p.264 (PDF p.275).
-/

@[expose] public section
open Matrix
open scoped MatrixGroups
open Matrix.PSL3.OuterSolvable Matrix.PSL3.ExtensionBorel
open Theory.GroupTheory.AutomorphismExtensionBorel
namespace Matrix.PSL3.LinearThree.OuterExtensions.CoreCalculation
variable (F : Type*) [Field F] [Finite F] [CharP F 2]
def localSL (point : Bool) : Subgroup SL(3,F) :=
  if point then pointLocalSL F else lineLocalSL F
noncomputable def localProjectEquiv (point : Bool) : localSL F point ≃* localFactor F point := by
  cases point
  · exact lineLocalProjectEquiv F
  · exact pointLocalProjectEquiv F
omit [Finite F] [CharP F 2] in
@[simp] theorem localProjectEquiv_val (point : Bool) (x : localSL F point) :
    (localProjectEquiv F point x).val = projection F x.val := by
  cases point <;> rfl
noncomputable def block (point : Bool) : localFactor F point →* SL(2,F) :=
  (localFactorQuotientEquiv F point).toMonoidHom.comp (QuotientGroup.mk' _)
noncomputable def slBlock (point : Bool) : localSL F point →* SL(2,F) :=
  (block F point).comp (localProjectEquiv F point).toMonoidHom
@[simp] theorem slBlock_point_val (x : localSL F true) :
    (slBlock F true x).val =
      !![x.val.val 1 1, x.val.val 1 2; x.val.val 2 1, x.val.val 2 2] :=
  pointLocalCoreQuotientEquiv_project_val F x
@[simp] theorem slBlock_line_val (x : localSL F false) :
    (slBlock F false x).val =
      !![x.val.val 0 0, x.val.val 0 1; x.val.val 1 0, x.val.val 1 1] :=
  lineLocalCoreQuotientEquiv_project_val F x

omit [Finite F] [CharP F 2] in
theorem field_mem_localSL (point : Bool) (σ : F ≃+* F) (x : localSL F point) :
    SpecialLinearGroup.map σ.toRingHom x.val ∈ localSL F point := by
  cases point
  · have hx := (mem_lineLocalSL_iff F x.val).mp x.property
    apply (mem_lineLocalSL_iff F _).mpr
    change σ (x.val.val 2 0) = 0 ∧ σ (x.val.val 2 1) = 0 ∧ σ (x.val.val 2 2) = 1
    simp only [hx.1, hx.2.1, hx.2.2, map_zero, map_one, and_self]
  · have hx := (mem_pointLocalSL_iff F x.val).mp x.property
    apply (mem_pointLocalSL_iff F _).mpr
    change σ (x.val.val 0 0) = 1 ∧ σ (x.val.val 1 0) = 0 ∧ σ (x.val.val 2 0) = 0
    simp only [hx.1, hx.2.1, hx.2.2, map_zero, map_one, and_self]

def slField (point : Bool) (σ : F ≃+* F) : localSL F point →* localSL F point :=
  ((SpecialLinearGroup.map σ.toRingHom).comp (localSL F point).subtype).codRestrict _
    (field_mem_localSL F point σ)

theorem slBlock_field (point : Bool) (σ : F ≃+* F) (x : localSL F point) :
    slBlock F point (slField F point σ x) =
      Atlas.RankOneFieldAutomorphisms.slFieldAction σ (slBlock F point x) := by
  apply Subtype.ext
  cases point
  · rw [slBlock_line_val]
    change _ = ((slBlock F false x).val.map σ)
    rw [slBlock_line_val]
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  · rw [slBlock_point_val]
    change _ = ((slBlock F true x).val.map σ)
    rw [slBlock_point_val]
    ext i j
    fin_cases i <;> fin_cases j <;> rfl

omit [Finite F] [CharP F 2] in
theorem field_mem_localFactor (point : Bool) (σ : F ≃+* F) (x : localFactor F point) :
    fieldAction F σ x.val ∈ localFactor F point := by
  obtain ⟨y, rfl⟩ := (localProjectEquiv F point).surjective x
  rw [localProjectEquiv_val]
  rw [show fieldAction F σ (projection F y.val) =
    projection F (SpecialLinearGroup.map σ.toRingHom y.val) from fieldAction_mk F σ y.val]
  have h := (localProjectEquiv F point
    ⟨SpecialLinearGroup.map σ.toRingHom y.val, field_mem_localSL F point σ y⟩).property
  rwa [localProjectEquiv_val] at h

omit [Finite F] [CharP F 2] in
theorem field_preserves (point : Bool) (σ : F ≃+* F) :
    (localFactor F point).map (fieldAction F σ).toMonoidHom = localFactor F point := by
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact field_mem_localFactor F point σ ⟨x,hx⟩
  · intro x hx
    refine ⟨fieldAction F σ⁻¹ x, field_mem_localFactor F point σ⁻¹ ⟨x,hx⟩, ?_⟩
    change (fieldAction F σ * fieldAction F σ⁻¹) x = x
    rw [← map_mul, mul_inv_cancel, map_one]
    rfl

noncomputable def localField (point : Bool) (σ : F ≃+* F) :
    localFactor F point →* localFactor F point :=
  ((fieldAction F σ).toMonoidHom.comp (localFactor F point).subtype).codRestrict _
    (field_mem_localFactor F point σ)

theorem block_field (point : Bool) (σ : F ≃+* F) (x : localFactor F point) :
    block F point (localField F point σ x) =
      Atlas.RankOneFieldAutomorphisms.slFieldAction σ (block F point x) := by
  obtain ⟨y, rfl⟩ := (localProjectEquiv F point).surjective x
  have h : localField F point σ (localProjectEquiv F point y) =
      localProjectEquiv F point (slField F point σ y) := by
    apply Subtype.ext
    change fieldAction F σ (localProjectEquiv F point y).val = _
    rw [localProjectEquiv_val, localProjectEquiv_val]
    exact fieldAction_mk F σ y.val
  rw [h]
  exact slBlock_field F point σ y
end Matrix.PSL3.LinearThree.OuterExtensions.CoreCalculation
