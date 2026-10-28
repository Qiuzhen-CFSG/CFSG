module

public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Mathieu.ModuleGeometry.RadicalAction.Operators

/-!
# The second Mathieu actor moves the marked line to order four

The full proposed six-space image preserves a binary plane. Two powers of
its cubic rotation move the marked vector to generators of that plane.
Thus the line commutator is exactly a two-dimensional binary space, of
order four. The shear is retained throughout the invariance calculation.

The final theorem applies to the literal restricted native action, under
its precise image-position input. Source: Aschbacher–Smith 14.4.12, p.1012.
-/

@[expose] public section

open Matrix Representation.SL2FourNatural
open Sporadic.Mathieu M22TripleCover M22TripleCover.Unitary
open Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreLinearModel
open Representation.BinaryOffender
open scoped Matrix
namespace CFSG.Quasithin.Chapter14.Section04.LargerDimension.Mathieu.ModuleGeometry.Native.RadicalAction

noncomputable def matrixRepresentation : Representation (ZMod 2) MatSixˣ Six :=
  Matrix.toLinAlgEquiv'.toMonoidHom.comp (Units.coeHom MatSix)

def planeMatrix : Matrix (Fin 6) (Fin 2) (ZMod 2) := binaryRows ![1,2,0,0,0,0]
def plane : Submodule (ZMod 2) Six := planeMatrix.mulVecLin.range

def modelMarkedLine : Submodule (ZMod 2) Six := Submodule.span (ZMod 2) {Pi.single 0 1}

theorem planeMatrix_injective : Function.Injective planeMatrix.mulVecLin := by
  intro u v h
  funext i
  fin_cases i
  · simpa [planeMatrix, binaryRows, mulVec, dotProduct, Fin.sum_univ_two, Nat.testBit] using congrFun h 0
  · simpa [planeMatrix, binaryRows, mulVec, dotProduct, Fin.sum_univ_two, Nat.testBit] using congrFun h 1

theorem plane_finrank : Module.finrank (ZMod 2) plane = 2 := by
  rw [plane, LinearMap.finrank_range_of_inj planeMatrix_injective]
  simp

theorem modelMarkedLine_le_plane : modelMarkedLine ≤ plane := by
  apply Submodule.span_le.mpr
  intro u hu
  rw [Set.mem_singleton_iff.mp hu]
  exact ⟨![1,0], by decide +kernel⟩

private theorem stabilizes_range {n : ℕ} (g : MatSixˣ)
    (E : Matrix (Fin 6) (Fin n) (ZMod 2))
    (A B : Matrix (Fin n) (Fin n) (ZMod 2))
    (hg : (g : MatSix) * E = E * A) (hi : (g⁻¹ : MatSixˣ).val * E = E * B) :
    g ∈ subspaceStabilizer matrixRepresentation E.mulVecLin.range := by
  have hf (g : MatSixˣ) (M : Matrix (Fin n) (Fin n) (ZMod 2))
      (h : g.val * E = E * M) : ∀ v ∈ E.mulVecLin.range,
        matrixRepresentation g v ∈ E.mulVecLin.range := by
    rintro v ⟨u, rfl⟩
    refine ⟨M *ᵥ u, ?_⟩
    change E *ᵥ (M *ᵥ u) = g.val *ᵥ (E *ᵥ u)
    simp only [mulVec_mulVec, h]
  intro v
  refine ⟨fun hv => ?_, hf g A hg v⟩
  have hh := hf g⁻¹ B hi _ hv
  simpa only [← Module.End.mul_apply, ← map_mul, inv_mul_cancel,
    map_one, Module.End.one_apply] using hh

theorem second_stabilizes_plane :
    secondMatrixGroup ≤ subspaceStabilizer matrixRepresentation plane := by
  apply (Subgroup.closure_le _).mpr
  intro g hg
  rcases Set.mem_insert_iff.mp hg with rfl | hg
  · exact stabilizes_range rotation planeMatrix !![0,1; 1,1] !![1,1; 1,0]
      (by decide +kernel) (by decide +kernel)
  · rw [Set.mem_singleton_iff.mp hg]
    exact stabilizes_range shear planeMatrix 1 1 (by decide +kernel) (by decide +kernel)

theorem model_second_commutator :
    subspaceCommutator matrixRepresentation modelMarkedLine secondMatrixGroup = plane := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro v ⟨g, hg, w, hw, rfl⟩
    exact plane.sub_mem ((second_stabilizes_plane hg w).2 (modelMarkedLine_le_plane hw))
      (modelMarkedLine_le_plane hw)
  · let M := subspaceCommutator matrixRepresentation modelMarkedLine secondMatrixGroup
    have hr : rotation ∈ secondMatrixGroup := Subgroup.subset_closure (Or.inl rfl)
    have h₁ : matrixRepresentation rotation (Pi.single 0 1) - Pi.single 0 1 ∈ M :=
      Submodule.subset_span ⟨rotation, hr, _, Submodule.mem_span_singleton_self _, rfl⟩
    have h₂ : matrixRepresentation (rotation ^ 2) (Pi.single 0 1) - Pi.single 0 1 ∈ M :=
      Submodule.subset_span ⟨rotation ^ 2, secondMatrixGroup.pow_mem hr 2, _,
        Submodule.mem_span_singleton_self _, rfl⟩
    have he₂ : matrixRepresentation (rotation ^ 2) (Pi.single 0 1) - Pi.single 0 1 =
        Pi.single 1 1 := by decide +kernel
    have he₁ : (matrixRepresentation rotation (Pi.single 0 1) - Pi.single 0 1) +
        Pi.single 1 1 = Pi.single 0 1 := by decide +kernel
    rw [he₂] at h₂
    have h₀ : Pi.single 0 1 ∈ M := he₁ ▸ M.add_mem h₁ h₂
    rintro v ⟨u, rfl⟩
    have he : planeMatrix *ᵥ u = u 0 • Pi.single 0 1 + u 1 • Pi.single 1 1 := by
      funext i
      fin_cases i <;> simp [planeMatrix, binaryRows, mulVec, dotProduct, Fin.sum_univ_two, Nat.testBit]
    rw [mulVecLin_apply, he]
    exact M.add_mem (M.smul_mem _ h₀) (M.smul_mem _ h₂)

noncomputable section

def movedPlane : Submodule (ZMod 2) parabolicSpace := plane.map frameEquiv.toLinearMap

theorem movedPlane_card : Nat.card movedPlane = 4 := by
  change Nat.card (plane.map frameEquiv.toLinearMap) = 4
  rw [Nat.card_congr (Submodule.equivMapOfInjective frameEquiv.toLinearMap
    frameEquiv.injective plane).toEquiv.symm]
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2), plane_finrank]
  norm_num

theorem markedLine_eq_map : markedLine = modelMarkedLine.map frameEquiv.toLinearMap := by
  rw [modelMarkedLine, Submodule.map_span, Set.image_singleton]
  change markedLine = Submodule.span (ZMod 2) {frameEquiv (Pi.single 0 1)}
  rw [frameEquiv_marked]
  rfl

theorem second_commutator_eq_movedPlane (A : Subgroup parabolic)
    (hA : A.map parabolicRepresentation.asGroupHom = secondImage) :
    subspaceCommutator parabolicRepresentation markedLine A = movedPlane := by
  change _ = plane.map frameEquiv.toLinearMap
  rw [← model_second_commutator]
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro v ⟨a, ha, w, hw, rfl⟩
    have him : parabolicRepresentation.asGroupHom a ∈ secondImage := by
      rw [← hA]
      exact ⟨a, ha, rfl⟩
    obtain ⟨g, hg, hga⟩ := him
    have he : parabolicRepresentation a = modelAction g.val :=
      (congrArg (fun t : (Module.End (ZMod 2) parabolicSpace)ˣ => t.val) hga).symm
    rw [markedLine_eq_map] at hw
    obtain ⟨u, hu, rfl⟩ := hw
    refine ⟨matrixRepresentation g u - u,
      Submodule.subset_span ⟨g, hg, u, hu, rfl⟩, ?_⟩
    change frameEquiv (matrixRepresentation g u - u) =
      parabolicRepresentation a (frameEquiv u) - frameEquiv u
    rw [he, modelAction_frameEquiv, map_sub]
    rfl
  · apply Submodule.map_le_iff_le_comap.mpr
    apply Submodule.span_le.mpr
    rintro v ⟨g, hg, u, hu, rfl⟩
    have him : modelUnits g ∈ A.map parabolicRepresentation.asGroupHom := by
      rw [hA]
      exact ⟨g, hg, rfl⟩
    obtain ⟨a, ha, hag⟩ := him
    have he : parabolicRepresentation a = modelAction g.val :=
      congrArg (fun t : (Module.End (ZMod 2) parabolicSpace)ˣ => t.val) hag
    change frameEquiv (matrixRepresentation g u - u) ∈
      subspaceCommutator parabolicRepresentation markedLine A
    have hh : parabolicRepresentation a (frameEquiv u) - frameEquiv u ∈
        subspaceCommutator parabolicRepresentation markedLine A :=
      Submodule.subset_span ⟨a, ha, frameEquiv u,
        by rw [markedLine_eq_map]; exact ⟨u, hu, rfl⟩, rfl⟩
    have happ : matrixRepresentation g u = (g : MatSix) *ᵥ u := rfl
    simpa only [he, modelAction_frameEquiv, map_sub, happ] using hh

theorem second_commutator_card (A : Subgroup parabolic)
    (hA : A.map parabolicRepresentation.asGroupHom = secondImage) :
    Nat.card (subspaceCommutator parabolicRepresentation markedLine A) = 4 := by
  rw [second_commutator_eq_movedPlane A hA]
  exact movedPlane_card

end
end CFSG.Quasithin.Chapter14.Section04.LargerDimension.Mathieu.ModuleGeometry.Native.RadicalAction
