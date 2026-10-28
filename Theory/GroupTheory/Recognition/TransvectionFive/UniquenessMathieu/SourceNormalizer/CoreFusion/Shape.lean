module
public import Theory.GroupTheory.Recognition.TransvectionFive.UniquenessMathieu.SourceNormalizer.Plane
public import Theory.GroupTheory.Recognition.TransvectionFive.UniquenessLinearSourceSylow
import Mathlib.Tactic.FinCases

/-!
# The actual two-core has the extraspecial matrix shape

A normal two-subgroup lies in the standard Sylow. Conjugating it by the
middle-coordinate reversal leaves it in that Sylow, forcing all three
strictly upper entries of the middle block to vanish. Thus every element
of the literal two-core has only first-row and last-column coordinates.
This uses no assumed extraspecial classification or identification of the core.

Source: Aschbacher, *Sporadic Groups* (1994), 39.1(1),(5), pp.213–214.
-/

public noncomputable section
open Subgroup BinaryLinear.TransvectionFiveLocal
namespace Theory.GroupTheory.TransvectionFive.UniquenessMathieu.SourceNormalizer.CoreFusion
open UniquenessLinear Theory.SpecificGroups.LinearSylowNormalizers
private abbrev B := ZMod 2
private abbrev Mat := Matrix (Fin 5) (Fin 5) B

private theorem core_unipotent (q : centralizer) (hq : q ∈ pCore 2 centralizer) :
    (q : SL) ∈ unipotent 5 B := by
  have hinc : (standardSylow 5 B (by decide) : Subgroup SL) ≤ centralizer := by
    rw [coe_standardSylow, ← model_upper_eq_unipotent]
    exact upper_le_centralizer
  have hp := pCore_isPGroup.le_sylow_of_normal
    ((standardSylow 5 B (by decide)).subtype hinc) hq
  change (q : SL) ∈ (standardSylow 5 B (by decide) : Subgroup SL) at hp
  rwa [coe_standardSylow] at hp

private def reverseMiddle : SL :=
  Matrix.SpecialLinearGroup.transvection (by decide : (1 : Fin 5) ≠ 3) 1 *
  Matrix.SpecialLinearGroup.transvection (by decide : (3 : Fin 5) ≠ 1) 1 *
  Matrix.SpecialLinearGroup.transvection (by decide : (1 : Fin 5) ≠ 3) 1
private theorem reverseMiddle_inv : reverseMiddle⁻¹ = reverseMiddle := by decide +kernel
private theorem reverseMiddle_centralizer : reverseMiddle ∈ centralizer := by
  apply mem_centralizer_singleton_iff.mpr
  decide +kernel
private theorem reverseMiddle_val : reverseMiddle.val =
    !![1,0,0,0,0;0,0,0,1,0;0,0,1,0,0;0,1,0,0,0;0,0,0,0,1] := by decide +kernel
private theorem reverseMiddle_entries (m : Mat) :
    reverseMiddle.val * m * reverseMiddle.val =
      fun i j => m ((Equiv.swap 1 3) i) ((Equiv.swap 1 3) j) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [reverseMiddle_val, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_succ, Equiv.swap_apply_def]

/-- Every element of the literal two-core has only the first-row and
last-column entries: conjugating by middle reversal keeps it unipotent. -/
theorem core_shape (q : centralizer) (hq : q ∈ pCore 2 centralizer) :
    (q : SL).val = !![
      1, q.val 0 1, q.val 0 2, q.val 0 3, q.val 0 4;
      0, 1, 0, 0, q.val 1 4;
      0, 0, 1, 0, q.val 2 4;
      0, 0, 0, 1, q.val 3 4;
      0, 0, 0, 0, 1] := by
  let w : centralizer := ⟨reverseMiddle, reverseMiddle_centralizer⟩
  have hwq : w * q * w⁻¹ ∈ pCore 2 centralizer :=
    (pCore_normal (p := 2) (G := centralizer)).conj_mem q hq w
  obtain ⟨hu,hd⟩ := (mem_unipotent 5 B _).mp (core_unipotent q hq)
  have hu := (mem_borel 5 B _).mp hu
  obtain ⟨hv,_⟩ := (mem_unipotent 5 B _).mp (core_unipotent _ hwq)
  have hv := (mem_borel 5 B _).mp hv
  have hm : ((w * q * w⁻¹ : centralizer) : SL).val =
      fun i j => q.val ((Equiv.swap 1 3) i) ((Equiv.swap 1 3) j) := by
    change reverseMiddle.val * q.val.val * reverseMiddle⁻¹.val = _
    rw [reverseMiddle_inv, reverseMiddle_entries]
  have h12 : q.val 1 2 = 0 := by
    have he := hv (show (2 : Fin 5) < 3 by decide)
    change ((w * q * w⁻¹ : centralizer) : SL).val 3 2 = 0 at he
    rw [hm] at he
    exact he
  have h13 : q.val 1 3 = 0 := by
    have he := hv (show (1 : Fin 5) < 3 by decide)
    change ((w * q * w⁻¹ : centralizer) : SL).val 3 1 = 0 at he
    rw [hm] at he
    exact he
  have h23 : q.val 2 3 = 0 := by
    have he := hv (show (1 : Fin 5) < 2 by decide)
    change ((w * q * w⁻¹ : centralizer) : SL).val 2 1 = 0 at he
    rw [hm] at he
    exact he
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hd,h12,h13,h23]
  all_goals exact hu (by decide)

end Theory.GroupTheory.TransvectionFive.UniquenessMathieu.SourceNormalizer.CoreFusion
