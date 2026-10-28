module
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.LocalSetup.Geometry

/-!
# The cubic image of the two-residual of the vector stabilizer

In the binary five-point core the stabilizer of e₁₂ has order six. Its
pointwise stabilizer of the first two coordinates is the displayed cubic
subgroup, of index two. Thus its two-residual lies in that cubic subgroup.
The actual residual in `ResidualModule` supplies the reverse inclusion by
lifting the three-cycle. The same cubic fixes e₁₃₄₅.

Source: Aschbacher–Smith, combined 1 March 2004 manuscript, printed p.926
and the permutation-module conventions of §B.3.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.A5Module.ResidualCoordinates
open Subgroup BinaryPermutation BinaryPermutation.FiveCentralizerGeometry

def stabilizer : Subgroup (alternatingGroup (Fin 5)) where
  carrier := {g | act g v = v}
  one_mem' := by simp [act]
  mul_mem' {g h} hg hh := by
    change coreRepresentation (Fin 5) (g.val * h.val) v = v
    rw [map_mul, Module.End.mul_apply, hh, hg]
  inv_mem' {g} hg := by
    have h := congrArg (act g⁻¹) hg
    change act g⁻¹ v = v
    simpa only [act, Subgroup.coe_inv, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
      Module.End.one_apply] using h.symm

local instance : DecidablePred (· ∈ stabilizer) := fun g =>
  inferInstanceAs (Decidable (act g v = v))
local instance : Fintype stabilizer := Subtype.fintype _

def cubicGroup : Subgroup (alternatingGroup (Fin 5)) :=
  MulAction.stabilizer (alternatingGroup (Fin 5)) (0 : Fin 5) ⊓
    MulAction.stabilizer (alternatingGroup (Fin 5)) (1 : Fin 5)
local instance : DecidablePred (· ∈ cubicGroup) := fun g =>
  inferInstanceAs (Decidable (g.val 0 = 0 ∧ g.val 1 = 1))
local instance : Fintype cubicGroup := Subtype.fintype _

theorem cubic_mem : cubic ∈ cubicGroup := by decide +kernel

theorem cubic_cases (g : alternatingGroup (Fin 5)) (hg : g ∈ cubicGroup) :
    g = 1 ∨ g = cubic ∨ g = cubic ^ 2 := by
  have hc : ∀ g : alternatingGroup (Fin 5), g.val 0 = 0 → g.val 1 = 1 →
      g = 1 ∨ g = cubic ∨ g = cubic ^ 2 := by decide +kernel
  exact hc g hg.1 hg.2

theorem cubicGroup_eq_zpowers : cubicGroup = zpowers cubic := by
  apply le_antisymm
  · intro g hg
    rcases cubic_cases g hg with rfl | rfl | rfl
    · exact one_mem _
    · exact mem_zpowers _
    · exact pow_mem (mem_zpowers _) _
  · exact zpowers_le.mpr cubic_mem

theorem cubicGroup_le_stabilizer : cubicGroup ≤ stabilizer := by
  intro g hg
  rcases cubic_cases g hg with rfl | rfl | rfl
  · exact stabilizer.one_mem
  · exact cubic_fixes_v
  · exact stabilizer.pow_mem cubic_fixes_v 2

theorem stabilizer_card : Nat.card stabilizer = 6 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

theorem cubicGroup_card : Nat.card cubicGroup = 3 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

def cubicInStabilizer : Subgroup stabilizer := cubicGroup.subgroupOf stabilizer

theorem cubicInStabilizer_index : cubicInStabilizer.index = 2 := by
  have hc : Nat.card cubicInStabilizer = 3 := by
    change Nat.card (cubicGroup.subgroupOf stabilizer) = 3
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe cubicGroup_le_stabilizer).toEquiv]
    exact cubicGroup_card
  have hh := cubicInStabilizer.card_mul_index
  rw [hc, stabilizer_card] at hh
  omega

instance : cubicInStabilizer.Normal :=
  Subgroup.normal_of_index_eq_two cubicInStabilizer_index

theorem residual_le_cubic : pResidual 2 stabilizer ≤ cubicInStabilizer := by
  apply sInf_le
  refine ⟨inferInstance, IsPGroup.of_card (n := 1) ?_⟩
  exact cubicInStabilizer_index

theorem cubic_fixes_a (g : cubicGroup) : act g.val a = a := by
  rcases cubic_cases g g.property with he | he | he
  · rw [he]; simp [act]
  · rw [he]; exact BinaryPermutation.FiveCentralizerGeometry.cubic_fixes_a
  · rw [he, pow_two]
    change coreRepresentation (Fin 5) (cubic.val * cubic.val) a = a
    rw [map_mul, Module.End.mul_apply, BinaryPermutation.FiveCentralizerGeometry.cubic_fixes_a,
      BinaryPermutation.FiveCentralizerGeometry.cubic_fixes_a]

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.A5Module.ResidualCoordinates
