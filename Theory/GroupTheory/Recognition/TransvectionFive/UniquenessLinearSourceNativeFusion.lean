module
public import Theory.GroupTheory.Recognition.TransvectionFive.UniquenessLinearSourceMarkedAlignment
import all Theory.GroupTheory.Recognition.TransvectionFive.UniquenessLinearSourcePlaneCoordinates
import all Theory.GroupTheory.Recognition.TransvectionFive.UniquenessLinearSourcePlaneCensus
import all Theory.GroupTheory.Recognition.TransvectionFive.UniquenessMathieu.SourceNormalizer.Intersections.Model

/-!
# The native marking and its actual rectangle fusion

The identity marking of the full transvection centralizer in SL₅(2) has
exactly the two 21-element fusion sets. The first rectangle is parametrized
by six bits. Its rank-one elements reduce under the existing elementary
shears to four roots, each explicitly conjugate to the marked transvection.
Conversely the conjugate-root entry formula forces every two-by-two minor
to vanish. The involutory graph automorphism transports the count to the
second rectangle.

Applying marked alignment now gives compatible maps from the original
source normalizers to the literal native normalizers, including both
intersection restrictions and the row-side edge fixer. This is the model
input to Aschbacher, *Sporadic Groups* (1994), 41.4--41.5, p.222.
The setwise-edge compatibility and ambient source generation are separate
obligations; no recognition conclusion is assumed here.
-/

public noncomputable section
open Subgroup BinaryLinear.TransvectionFiveLocal
namespace Theory.GroupTheory.TransvectionFive.UniquenessLinear
open PlaneTensor PlaneCensus

/-- The identity marking of the actual full matrix centralizer. -/
def nativeMarking : MarkedCentralizer transvection where
  equiv := MulEquiv.refl _
  on_point := rfl

/-- The native marking pulls each centralizer subgroup back to itself. -/
theorem nativeMarking_pullback (A : Subgroup SL) (hA : A ≤ centralizer) :
    nativeMarking.pullback A = A := by
  ext a
  constructor
  · intro ha
    exact (nativeMarking.mem_pullback_iff A ⟨a, nativeMarking.pullback_le A ha⟩).mp ha
  · intro ha
    exact (nativeMarking.mem_pullback_iff A ⟨a, hA ha⟩).mpr ha

private theorem native_element_matrix (x : Code) :
    (element nativeMarking x).val =
      1 + Matrix.single 0 2 (decode x 0 0) + Matrix.single 0 3 (decode x 0 1) +
      Matrix.single 0 4 (decode x 0 2) + Matrix.single 1 2 (decode x 1 0) +
      Matrix.single 1 3 (decode x 1 1) + Matrix.single 1 4 (decode x 1 2) := by
  have h := element_model nativeMarking x
  change element nativeMarking x = modelElement (decode x) at h
  rw [h, modelElement_matrix]

private def swap01 : SL :=
  Matrix.SpecialLinearGroup.transvection (by decide : (0 : Fin 5) ≠ 1) 1 *
  Matrix.SpecialLinearGroup.transvection (by decide : (1 : Fin 5) ≠ 0) 1 *
  Matrix.SpecialLinearGroup.transvection (by decide : (0 : Fin 5) ≠ 1) 1
private def swap24 : SL :=
  Matrix.SpecialLinearGroup.transvection (by decide : (2 : Fin 5) ≠ 4) 1 *
  Matrix.SpecialLinearGroup.transvection (by decide : (4 : Fin 5) ≠ 2) 1 *
  Matrix.SpecialLinearGroup.transvection (by decide : (2 : Fin 5) ≠ 4) 1

private theorem native_pure_representative (x : Code) (hx : PlaneCensus.pure x = true) :
    IsConj transvection (element nativeMarking (representative (label x))) := by
  have h : representative (label x) = 1 ∨ representative (label x) = 4 ∨
      representative (label x) = 8 ∨ representative (label x) = 32 :=
    (by decide : ∀ a : Code, PlaneCensus.pure a = true →
      representative (label a) = 1 ∨ representative (label a) = 4 ∨
      representative (label a) = 8 ∨ representative (label a) = 32) x hx
  rcases h with h | h | h | h <;> rw [h]
  · apply isConj_iff.mpr
    refine ⟨swap24, ?_⟩
    apply Subtype.ext
    rw [native_element_matrix]
    simp only [swap24, mul_inv_rev, Matrix.SpecialLinearGroup.transvection_inv,
      show (-1 : ZMod 2) = 1 from rfl, Matrix.SpecialLinearGroup.coe_mul]
    decide
  · rw [element_point]
  · apply isConj_iff.mpr
    refine ⟨swap01 * swap24, ?_⟩
    apply Subtype.ext
    rw [native_element_matrix]
    simp only [swap01, swap24, mul_inv_rev, Matrix.SpecialLinearGroup.transvection_inv,
      show (-1 : ZMod 2) = 1 from rfl, Matrix.SpecialLinearGroup.coe_mul]
    decide
  · apply isConj_iff.mpr
    refine ⟨swap01, ?_⟩
    apply Subtype.ext
    rw [native_element_matrix]
    simp only [swap01, mul_inv_rev, Matrix.SpecialLinearGroup.transvection_inv,
      show (-1 : ZMod 2) = 1 from rfl, Matrix.SpecialLinearGroup.coe_mul]
    decide

private theorem native_pure_conjugate (x : Code) (hx : PlaneCensus.pure x = true) :
    IsConj transvection (element nativeMarking x) := by
  have hf (w : List (Fin 5)) (a : Code) : IsConj (element nativeMarking a)
      (element nativeMarking (w.foldl (fun b k => PlaneCensus.shear k b) a)) := by
    induction w generalizing a with
    | nil => exact IsConj.refl _
    | cons k w ih =>
      obtain ⟨g, _, hg⟩ := exists_shear_conjugator nativeMarking k a
      exact (isConj_iff.mpr ⟨g, hg⟩).trans (ih _)
  have h := hf (path x) x
  rw [normal_form] at h
  exact (native_pure_representative x hx).trans h.symm

private theorem native_conjugate_pure (x : Code)
    (hx : IsConj transvection (element nativeMarking x)) : PlaneCensus.pure x = true := by
  obtain ⟨g, hg⟩ := isConj_iff.mp hx
  have he (i : Fin 2) (j : Fin 3) :
      decode x i j = g.val ⟨i.val, by omega⟩ 0 * (g⁻¹).val 4 ⟨j.val + 2, by omega⟩ := by
    have hh := UniquenessMathieu.SourceNormalizer.conjugate_root_entry g
      (show (0 : Fin 5) < 4 by decide) ⟨i.val, by omega⟩ ⟨j.val + 2, by omega⟩
    change (g * transvection * g⁻¹).val _ _ = _ at hh
    rw [hg, native_element_matrix] at hh
    fin_cases i <;> fin_cases j <;> simpa [Matrix.single, Matrix.one_apply] using hh
  have hm (j k : Fin 3) : decode x 0 j * decode x 1 k = decode x 0 k * decode x 1 j := by
    rw [he, he, he, he]
    ring
  have hn : x ≠ 0 := by
    intro hz
    rw [hz, element_zero, isConj_one_left] at hx
    have ho := transvection_orderOf
    simp [hx] at ho
  exact (by decide : ∀ a : Code, a ≠ 0 →
    (∀ j k : Fin 3, decode a 0 j * decode a 1 k = decode a 0 k * decode a 1 j) →
    PlaneCensus.pure a = true) x hn hm


/-- Actual matrix conjugacy in the first rectangle is exactly rank one. -/
theorem native_fusion_iff_pure (x : Code) :
    IsConj transvection (element nativeMarking x) ↔ PlaneCensus.pure x = true :=
  ⟨native_conjugate_pure x, native_pure_conjugate x⟩

private theorem native_plane_image :
    element nativeMarking '' {x : Code | PlaneCensus.pure x = true} =
      nativeMarking.fusion nativeMarking.plane := by
  ext a
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨element_mem nativeMarking x, (native_fusion_iff_pure x).mpr hx⟩
  · rintro ⟨ha, hc⟩
    obtain ⟨x, hx⟩ := (sourceEquiv nativeMarking).surjective ⟨a, ha⟩
    have he : element nativeMarking x = a := congrArg Subtype.val hx
    exact ⟨x, (native_fusion_iff_pure x).mp (he.symm ▸ hc), he⟩

/-- There are exactly 21 transvections in the literal first rectangle. -/
theorem native_plane_fusion_card :
    (nativeMarking.fusion nativeMarking.plane).ncard = 21 := by
  rw [← native_plane_image, Set.ncard_image_of_injective _ (element_injective nativeMarking)]
  have he : {x : Code | PlaneCensus.pure x = true} =
      (Finset.univ.filter (fun x : Code => PlaneCensus.pure x = true) : Set Code) := by
    ext x
    simp
  rw [he, Set.ncard_coe_finset]
  decide

private theorem native_dual_fusion :
    modelDual '' (nativeMarking.fusion nativeMarking.threeSpace) =
      nativeMarking.fusion nativeMarking.plane := by
  have hp := nativeMarking_pullback Model.plane Model.plane_le_centralizer
  have ht := nativeMarking_pullback Model.threeSpace Model.threeSpace_le_centralizer
  ext a
  constructor
  · rintro ⟨b, ⟨hb, hc⟩, rfl⟩
    refine ⟨?_, ?_⟩
    · change modelDual b ∈ nativeMarking.pullback Model.plane
      rw [hp, modelDual_plane_iff]
      exact ht ▸ hb
    · simpa only [MulEquiv.coe_toMonoidHom, modelDual_point] using modelDual.toMonoidHom.map_isConj hc
  · rintro ⟨ha, hc⟩
    refine ⟨modelDual a, ⟨?_, ?_⟩, modelDual_square a⟩
    · change modelDual a ∈ nativeMarking.pullback Model.threeSpace
      rw [ht, modelDual_threeSpace_iff]
      exact hp ▸ ha
    · simpa only [MulEquiv.coe_toMonoidHom, modelDual_point] using modelDual.toMonoidHom.map_isConj hc

/-- The actual native matrix marking has the source 21/21 fusion pattern. -/
theorem nativeMarking_linearFusion : nativeMarking.LinearFusion := by
  refine ⟨native_plane_fusion_card, ?_⟩
  have h := congrArg Set.ncard native_dual_fusion
  rw [Set.ncard_image_of_injective _ modelDual.injective, native_plane_fusion_card] at h
  exact h

/-- Apply the marked alignment to the literal SL₅(2) carrier. -/
theorem exists_compatible_native_maps {G : Type*} [Group G] [Finite G] {z : G}
    (F : MarkedCentralizer z) (hlinear : F.LinearFusion) :
    ∃ (r : rowNormalizer F ≃* rowNormalizer nativeMarking)
      (t : sourceThreeSpaceNormalizer F ≃* sourceThreeSpaceNormalizer nativeMarking),
      (((sourcePlaneNormalizer F).subgroupOf (rowNormalizer F)).map r.toMonoidHom =
        (sourcePlaneNormalizer nativeMarking).subgroupOf (rowNormalizer nativeMarking)) ∧
      (((sourceThreeSpaceNormalizer F).subgroupOf (rowNormalizer F)).map r.toMonoidHom =
        (sourceThreeSpaceNormalizer nativeMarking).subgroupOf (rowNormalizer nativeMarking)) ∧
      (((SourceGeometry.edgeGroup F hlinear).subgroupOf (rowNormalizer F)).map r.toMonoidHom =
        (SourceGeometry.edgeGroup nativeMarking nativeMarking_linearFusion).subgroupOf
          (rowNormalizer nativeMarking)) ∧
      (((rowNormalizer F).subgroupOf (sourceThreeSpaceNormalizer F)).map t.toMonoidHom =
        (rowNormalizer nativeMarking).subgroupOf (sourceThreeSpaceNormalizer nativeMarking)) ∧
      ∀ (g : G) (hgR : g ∈ rowNormalizer F) (hgS : g ∈ sourceThreeSpaceNormalizer F),
        (r ⟨g, hgR⟩ : SL) = (t ⟨g, hgS⟩ : SL) :=
  exists_compatible_local_maps F nativeMarking hlinear nativeMarking_linearFusion

end Theory.GroupTheory.TransvectionFive.UniquenessLinear
