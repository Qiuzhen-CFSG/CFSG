module

public import Theory.AtlasPort.ExceptionalIsomorphisms.Elementary
public import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# The literal generators of the binary endpoint induction

The shear in coordinates zero and one and the coordinate four-cycle are
the two matrices used in the endpoint induction data. Cycle conjugates
supply the four directed cycle roots; elementary commutators supply the
remaining eight roots. Elementary generation then proves that this exact
pair generates SL₄(2), without assuming a presentation or trusting a
computer algebra group calculation.

Source context: the binary-four carrier in Aschbacher--Smith 15.3.23.
The literal matrices agree with the group_generators field of
Scratch/DirectBinaryThreeAmbient/FourInducedBoundary/SpectralfalseCoordinates.json.
-/

public section
open Matrix Subgroup
open scoped MatrixGroups commutatorElement
namespace BinaryEndpointInduction

/-- The literal shear used by both endpoint induction coordinate tables. -/
@[expose] def transvectionGenerator : SL(4, ZMod 2) :=
  ⟨!![1,1,0,0; 0,1,0,0; 0,0,1,0; 0,0,0,1], by decide⟩

/-- The literal four-cycle; on columns it sends coordinate i to i+1. -/
@[expose] def cycleGenerator : SL(4, ZMod 2) :=
  ⟨!![0,0,0,1; 1,0,0,0; 0,1,0,0; 0,0,1,0], by decide⟩

private theorem shear_root : transvectionGenerator =
    SpecialLinearGroup.transvection (show (0 : Fin 4) ≠ 1 by decide) (1 : ZMod 2) := by
  decide

private theorem cycle_roots :
    cycleGenerator * transvectionGenerator * cycleGenerator ^ 3 =
      SpecialLinearGroup.transvection (show (1 : Fin 4) ≠ 2 by decide) (1 : ZMod 2) ∧
    cycleGenerator ^ 2 * transvectionGenerator * cycleGenerator ^ 2 =
      SpecialLinearGroup.transvection (show (2 : Fin 4) ≠ 3 by decide) (1 : ZMod 2) ∧
    cycleGenerator ^ 3 * transvectionGenerator * cycleGenerator =
      SpecialLinearGroup.transvection (show (3 : Fin 4) ≠ 0 by decide) (1 : ZMod 2) := by
  decide +kernel

private theorem chain_mem (H : Subgroup SL(4, ZMod 2))
    {i j k : Fin 4} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)
    (hi : SpecialLinearGroup.transvection hij (1 : ZMod 2) ∈ H)
    (hj : SpecialLinearGroup.transvection hjk (1 : ZMod 2) ∈ H) :
    SpecialLinearGroup.transvection hik (1 : ZMod 2) ∈ H := by
  have he := Atlas.elementary_commutator hik hij hjk (1 : ZMod 2) 1
  rw [one_mul] at he
  rw [← he, commutatorElement_def]
  exact H.mul_mem (H.mul_mem (H.mul_mem hi hj) (H.inv_mem hi)) (H.inv_mem hj)

/-- These exact two marked matrices generate the entire binary four-group. -/
theorem generator_closure :
    Subgroup.closure ({transvectionGenerator, cycleGenerator} : Set SL(4, ZMod 2)) = ⊤ := by
  let H := Subgroup.closure ({transvectionGenerator, cycleGenerator} : Set SL(4, ZMod 2))
  have ht : transvectionGenerator ∈ H := subset_closure (by simp)
  have hc : cycleGenerator ∈ H := subset_closure (by simp)
  have h01 : SpecialLinearGroup.transvection (show (0 : Fin 4) ≠ 1 by decide) (1 : ZMod 2) ∈ H :=
    shear_root ▸ ht
  have h12 : SpecialLinearGroup.transvection (show (1 : Fin 4) ≠ 2 by decide) (1 : ZMod 2) ∈ H :=
    cycle_roots.1 ▸ H.mul_mem (H.mul_mem hc ht) (H.pow_mem hc 3)
  have h23 : SpecialLinearGroup.transvection (show (2 : Fin 4) ≠ 3 by decide) (1 : ZMod 2) ∈ H :=
    cycle_roots.2.1 ▸ H.mul_mem (H.mul_mem (H.pow_mem hc 2) ht) (H.pow_mem hc 2)
  have h30 : SpecialLinearGroup.transvection (show (3 : Fin 4) ≠ 0 by decide) (1 : ZMod 2) ∈ H :=
    cycle_roots.2.2 ▸ H.mul_mem (H.mul_mem (H.pow_mem hc 3) ht) hc
  have h02 := chain_mem H (by decide) (by decide) (by decide) h01 h12
  have h13 := chain_mem H (by decide) (by decide) (by decide) h12 h23
  have h20 := chain_mem H (by decide) (by decide) (by decide) h23 h30
  have h31 := chain_mem H (by decide) (by decide) (by decide) h30 h01
  have h03 := chain_mem H (by decide) (by decide) (by decide) h02 h23
  have h10 := chain_mem H (by decide) (by decide) (by decide) h13 h30
  have h21 := chain_mem H (by decide) (by decide) (by decide) h20 h01
  have h32 := chain_mem H (by decide) (by decide) (by decide) h31 h12
  have hroot (i j : Fin 4) (hij : i ≠ j) :
      SpecialLinearGroup.transvection hij (1 : ZMod 2) ∈ H := by
    fin_cases i <;> fin_cases j <;> first | exact (hij rfl).elim | assumption
  apply top_unique
  intro g _
  apply Atlas.sl_elementary_induction (fun g => g ∈ H) ?_ (fun _ _ => H.mul_mem) g
  intro i j hij a
  rcases (by decide : ∀ a : ZMod 2, a = 0 ∨ a = 1) a with rfl | rfl
  · simp
  · exact hroot i j hij

end BinaryEndpointInduction
