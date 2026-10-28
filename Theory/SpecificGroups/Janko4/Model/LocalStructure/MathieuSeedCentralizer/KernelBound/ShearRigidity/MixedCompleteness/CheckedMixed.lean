module

public import Theory.SpecificGroups.Janko4.Model.LocalStructure.MathieuSeedCentralizer.KernelBound.ShearRigidity.MixedCompleteness.Reduction

/-!
# Kernel-checked mixed identities

Every index is covered by bounded batches. The equations are evaluated by
Lean's kernel; no external computation supplies a proof premise.
-/

public section
set_option Elab.async false
namespace Janko4.LocalStructure.MathieuSeedCentralizer.KernelBound.ShearRigidity.MixedCompleteness

set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
private theorem checked00 : ∀ j : Fin 16,
    MixedCheck ⟨0 + j.val, by omega⟩ := by
  unfold MixedCheck
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
private theorem checked01 : ∀ j : Fin 16,
    MixedCheck ⟨16 + j.val, by omega⟩ := by
  unfold MixedCheck
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
private theorem checked02 : ∀ j : Fin 16,
    MixedCheck ⟨32 + j.val, by omega⟩ := by
  unfold MixedCheck
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
private theorem checked03 : ∀ j : Fin 16,
    MixedCheck ⟨48 + j.val, by omega⟩ := by
  unfold MixedCheck
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
private theorem checked04 : ∀ j : Fin 16,
    MixedCheck ⟨64 + j.val, by omega⟩ := by
  unfold MixedCheck
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
private theorem checked05 : ∀ j : Fin 16,
    MixedCheck ⟨80 + j.val, by omega⟩ := by
  unfold MixedCheck
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
private theorem checked06 : ∀ j : Fin 16,
    MixedCheck ⟨96 + j.val, by omega⟩ := by
  unfold MixedCheck
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
private theorem checked07 : ∀ j : Fin 16,
    MixedCheck ⟨112 + j.val, by omega⟩ := by
  unfold MixedCheck
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
private theorem checked08 : ∀ j : Fin 16,
    MixedCheck ⟨128 + j.val, by omega⟩ := by
  unfold MixedCheck
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
private theorem checked09 : ∀ j : Fin 16,
    MixedCheck ⟨144 + j.val, by omega⟩ := by
  unfold MixedCheck
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
private theorem checked10 : ∀ j : Fin 16,
    MixedCheck ⟨160 + j.val, by omega⟩ := by
  unfold MixedCheck
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
private theorem checked11 : ∀ j : Fin 16,
    MixedCheck ⟨176 + j.val, by omega⟩ := by
  unfold MixedCheck
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
private theorem checked12 : ∀ j : Fin 16,
    MixedCheck ⟨192 + j.val, by omega⟩ := by
  unfold MixedCheck
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
private theorem checked13 : ∀ j : Fin 16,
    MixedCheck ⟨208 + j.val, by omega⟩ := by
  unfold MixedCheck
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
private theorem checked14 : ∀ j : Fin 16,
    MixedCheck ⟨224 + j.val, by omega⟩ := by
  unfold MixedCheck
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
private theorem checked15 : ∀ j : Fin 16,
    MixedCheck ⟨240 + j.val, by omega⟩ := by
  unfold MixedCheck
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
private theorem checked16 : ∀ j : Fin 16,
    MixedCheck ⟨256 + j.val, by omega⟩ := by
  unfold MixedCheck
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
private theorem checked17 : ∀ j : Fin 16,
    MixedCheck ⟨272 + j.val, by omega⟩ := by
  unfold MixedCheck
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
private theorem checked18 : ∀ j : Fin 16,
    MixedCheck ⟨288 + j.val, by omega⟩ := by
  unfold MixedCheck
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
private theorem checked19 : ∀ j : Fin 16,
    MixedCheck ⟨304 + j.val, by omega⟩ := by
  unfold MixedCheck
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
private theorem checked20 : ∀ j : Fin 16,
    MixedCheck ⟨320 + j.val, by omega⟩ := by
  unfold MixedCheck
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
private theorem checked21 : ∀ j : Fin 16,
    MixedCheck ⟨336 + j.val, by omega⟩ := by
  unfold MixedCheck
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
private theorem checked22 : ∀ j : Fin 16,
    MixedCheck ⟨352 + j.val, by omega⟩ := by
  unfold MixedCheck
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
private theorem checked23 : ∀ j : Fin 16,
    MixedCheck ⟨368 + j.val, by omega⟩ := by
  unfold MixedCheck
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
private theorem checked24 : ∀ j : Fin 16,
    MixedCheck ⟨384 + j.val, by omega⟩ := by
  unfold MixedCheck
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
private theorem checked25 : ∀ j : Fin 16,
    MixedCheck ⟨400 + j.val, by omega⟩ := by
  unfold MixedCheck
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
private theorem checked26 : ∀ j : Fin 16,
    MixedCheck ⟨416 + j.val, by omega⟩ := by
  unfold MixedCheck
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
private theorem checked27 : ∀ j : Fin 16,
    MixedCheck ⟨432 + j.val, by omega⟩ := by
  unfold MixedCheck
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
private theorem checked28 : ∀ j : Fin 16,
    MixedCheck ⟨448 + j.val, by omega⟩ := by
  unfold MixedCheck
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
private theorem checked29 : ∀ j : Fin 16,
    MixedCheck ⟨464 + j.val, by omega⟩ := by
  unfold MixedCheck
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
private theorem checked30 : ∀ j : Fin 16,
    MixedCheck ⟨480 + j.val, by omega⟩ := by
  unfold MixedCheck
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
private theorem checked31 : ∀ j : Fin 16,
    MixedCheck ⟨496 + j.val, by omega⟩ := by
  unfold MixedCheck
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
private theorem checked32 : ∀ j : Fin 16,
    MixedCheck ⟨512 + j.val, by omega⟩ := by
  unfold MixedCheck
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
private theorem checked33 : ∀ j : Fin 16,
    MixedCheck ⟨528 + j.val, by omega⟩ := by
  unfold MixedCheck
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
private theorem checked34 : ∀ j : Fin 16,
    MixedCheck ⟨544 + j.val, by omega⟩ := by
  unfold MixedCheck
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
private theorem checked35 : ∀ j : Fin 16,
    MixedCheck ⟨560 + j.val, by omega⟩ := by
  unfold MixedCheck
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
private theorem checked36 : ∀ j : Fin 16,
    MixedCheck ⟨576 + j.val, by omega⟩ := by
  unfold MixedCheck
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
private theorem checked37 : ∀ j : Fin 16,
    MixedCheck ⟨592 + j.val, by omega⟩ := by
  unfold MixedCheck
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
private theorem checked38 : ∀ j : Fin 16,
    MixedCheck ⟨608 + j.val, by omega⟩ := by
  unfold MixedCheck
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
private theorem checked39 : ∀ j : Fin 2,
    MixedCheck ⟨624 + j.val, by omega⟩ := by
  unfold MixedCheck
  decide +kernel

set_option maxRecDepth 10000 in
/-- All 626 identities are checked. -/
theorem allMixedChecks (i : Fin 626) : MixedCheck i := by
  by_cases hi : i.val < 624
  · have h : ∀ b : Fin 39, ∀ j : Fin 16,
          MixedCheck ⟨16 * b.val + j.val, by omega⟩ := by
        intro b
        fin_cases b
        · exact checked00
        · exact checked01
        · exact checked02
        · exact checked03
        · exact checked04
        · exact checked05
        · exact checked06
        · exact checked07
        · exact checked08
        · exact checked09
        · exact checked10
        · exact checked11
        · exact checked12
        · exact checked13
        · exact checked14
        · exact checked15
        · exact checked16
        · exact checked17
        · exact checked18
        · exact checked19
        · exact checked20
        · exact checked21
        · exact checked22
        · exact checked23
        · exact checked24
        · exact checked25
        · exact checked26
        · exact checked27
        · exact checked28
        · exact checked29
        · exact checked30
        · exact checked31
        · exact checked32
        · exact checked33
        · exact checked34
        · exact checked35
        · exact checked36
        · exact checked37
        · exact checked38
    have hb : i.val / 16 < 39 := by omega
    have hm : i.val % 16 < 16 := Nat.mod_lt _ (by decide)
    have hx := h ⟨i.val / 16, hb⟩ ⟨i.val % 16, hm⟩
    have heq : (⟨16 * (i.val / 16) + i.val % 16, by omega⟩ : Fin 626) = i :=
      Fin.ext (Nat.div_add_mod i.val 16)
    exact heq ▸ hx
  · have hx := checked39 ⟨i.val - 624, by omega⟩
    have heq : (⟨624 + (i.val - 624), by omega⟩ : Fin 626) = i :=
      Fin.ext (show 624 + (i.val - 624) = i.val by omega)
    exact heq ▸ hx

end Janko4.LocalStructure.MathieuSeedCentralizer.KernelBound.ShearRigidity.MixedCompleteness
