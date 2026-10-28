module

public import Theory.SpecificGroups.Janko4.Model.LocalStructure.MathieuSeedCentralizer.KernelBound.ShearRigidity.MixedCompleteness.Reduction

/-!
# Kernel-checked recovery identities

These 1221 identities certify every row of `D T = I + K F`: scanning the
recovery mask against the 595 evaluation rows gives the coordinate unit word
XOR the free-coordinate words selected by that row of the 626 kernel vectors.
They supply exactly the hypothesis consumed by `reconstruct` in Reduction.

The right-hand side is first rewritten as a simultaneous traversal of the two
literal tables. This avoids repeated indexing during kernel reduction while
preserving the published `RecoveryCheck`. Every index is then covered by a
bounded batch evaluated by Lean's kernel.

Source: `MixedCompleteness/source/README.md` and the untrusted tables in Data.
The batching follows the retained `Scratch/MixedCompleteness/CheckedRecovery.lean`
draft from the mixed-completeness assembly task.
-/

public section
set_option Elab.async false
namespace Janko4.LocalStructure.MathieuSeedCentralizer.KernelBound.ShearRigidity.MixedCompleteness

open GeneratorCertificates
open OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound.OrbitCoverCoordinates.LinearMembership.FiniteAlgebra

private theorem zipWith_ofFn {α β γ : Type*} {n : Nat}
    (f : α → β → γ) (a : Fin n → α) (b : Fin n → β) :
    List.zipWith f (List.ofFn a) (List.ofFn b) = List.ofFn (fun i => f (a i) (b i)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.ofFn_succ, List.ofFn_succ, List.ofFn_succ, List.zipWith_cons_cons, ih]

attribute [local irreducible] evaluationRows kernelCoefficients recoveryRows freeIndices

/-- Traverse the coefficient and free-coordinate tables in their published order. -/
private theorem recoveryCheck_iff (i : Fin 1221) : RecoveryCheck i ↔
    scan (recoveryRows.get i) evaluationRows.toList =
      2 ^ i.val ^^^ xorList (List.zipWith (fun (c : Nat) (f : Fin 1221) =>
        if c.testBit i.val then 2 ^ f.val else 0) kernelCoefficients.toList freeIndices.toList) := by
  rw [RecoveryCheck, ← ofFn_get kernelCoefficients, ← ofFn_get freeIndices, zipWith_ofFn]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
private theorem checked00 : ∀ j : Fin 16,
    RecoveryCheck ⟨0 + j.val, by omega⟩ := by
  simp only [recoveryCheck_iff]
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
private theorem checked01 : ∀ j : Fin 16,
    RecoveryCheck ⟨16 + j.val, by omega⟩ := by
  simp only [recoveryCheck_iff]
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
private theorem checked02 : ∀ j : Fin 16,
    RecoveryCheck ⟨32 + j.val, by omega⟩ := by
  simp only [recoveryCheck_iff]
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
private theorem checked03 : ∀ j : Fin 16,
    RecoveryCheck ⟨48 + j.val, by omega⟩ := by
  simp only [recoveryCheck_iff]
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
private theorem checked04 : ∀ j : Fin 16,
    RecoveryCheck ⟨64 + j.val, by omega⟩ := by
  simp only [recoveryCheck_iff]
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
private theorem checked05 : ∀ j : Fin 16,
    RecoveryCheck ⟨80 + j.val, by omega⟩ := by
  simp only [recoveryCheck_iff]
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
private theorem checked06 : ∀ j : Fin 16,
    RecoveryCheck ⟨96 + j.val, by omega⟩ := by
  simp only [recoveryCheck_iff]
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
private theorem checked07 : ∀ j : Fin 16,
    RecoveryCheck ⟨112 + j.val, by omega⟩ := by
  simp only [recoveryCheck_iff]
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
private theorem checked08 : ∀ j : Fin 16,
    RecoveryCheck ⟨128 + j.val, by omega⟩ := by
  simp only [recoveryCheck_iff]
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
private theorem checked09 : ∀ j : Fin 16,
    RecoveryCheck ⟨144 + j.val, by omega⟩ := by
  simp only [recoveryCheck_iff]
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
private theorem checked10 : ∀ j : Fin 16,
    RecoveryCheck ⟨160 + j.val, by omega⟩ := by
  simp only [recoveryCheck_iff]
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
private theorem checked11 : ∀ j : Fin 16,
    RecoveryCheck ⟨176 + j.val, by omega⟩ := by
  simp only [recoveryCheck_iff]
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
private theorem checked12 : ∀ j : Fin 16,
    RecoveryCheck ⟨192 + j.val, by omega⟩ := by
  simp only [recoveryCheck_iff]
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
private theorem checked13 : ∀ j : Fin 16,
    RecoveryCheck ⟨208 + j.val, by omega⟩ := by
  simp only [recoveryCheck_iff]
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
private theorem checked14 : ∀ j : Fin 16,
    RecoveryCheck ⟨224 + j.val, by omega⟩ := by
  simp only [recoveryCheck_iff]
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
private theorem checked15 : ∀ j : Fin 16,
    RecoveryCheck ⟨240 + j.val, by omega⟩ := by
  simp only [recoveryCheck_iff]
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
private theorem checked16 : ∀ j : Fin 16,
    RecoveryCheck ⟨256 + j.val, by omega⟩ := by
  simp only [recoveryCheck_iff]
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
private theorem checked17 : ∀ j : Fin 16,
    RecoveryCheck ⟨272 + j.val, by omega⟩ := by
  simp only [recoveryCheck_iff]
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
private theorem checked18 : ∀ j : Fin 16,
    RecoveryCheck ⟨288 + j.val, by omega⟩ := by
  simp only [recoveryCheck_iff]
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
private theorem checked19 : ∀ j : Fin 16,
    RecoveryCheck ⟨304 + j.val, by omega⟩ := by
  simp only [recoveryCheck_iff]
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
private theorem checked20 : ∀ j : Fin 16,
    RecoveryCheck ⟨320 + j.val, by omega⟩ := by
  simp only [recoveryCheck_iff]
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
private theorem checked21 : ∀ j : Fin 16,
    RecoveryCheck ⟨336 + j.val, by omega⟩ := by
  simp only [recoveryCheck_iff]
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
private theorem checked22 : ∀ j : Fin 16,
    RecoveryCheck ⟨352 + j.val, by omega⟩ := by
  simp only [recoveryCheck_iff]
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
private theorem checked23 : ∀ j : Fin 16,
    RecoveryCheck ⟨368 + j.val, by omega⟩ := by
  simp only [recoveryCheck_iff]
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
private theorem checked24 : ∀ j : Fin 16,
    RecoveryCheck ⟨384 + j.val, by omega⟩ := by
  simp only [recoveryCheck_iff]
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
private theorem checked25 : ∀ j : Fin 16,
    RecoveryCheck ⟨400 + j.val, by omega⟩ := by
  simp only [recoveryCheck_iff]
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
private theorem checked26 : ∀ j : Fin 16,
    RecoveryCheck ⟨416 + j.val, by omega⟩ := by
  simp only [recoveryCheck_iff]
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
private theorem checked27 : ∀ j : Fin 16,
    RecoveryCheck ⟨432 + j.val, by omega⟩ := by
  simp only [recoveryCheck_iff]
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
private theorem checked28 : ∀ j : Fin 16,
    RecoveryCheck ⟨448 + j.val, by omega⟩ := by
  simp only [recoveryCheck_iff]
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
private theorem checked29 : ∀ j : Fin 16,
    RecoveryCheck ⟨464 + j.val, by omega⟩ := by
  simp only [recoveryCheck_iff]
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
private theorem checked30 : ∀ j : Fin 16,
    RecoveryCheck ⟨480 + j.val, by omega⟩ := by
  simp only [recoveryCheck_iff]
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
private theorem checked31 : ∀ j : Fin 16,
    RecoveryCheck ⟨496 + j.val, by omega⟩ := by
  simp only [recoveryCheck_iff]
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
private theorem checked32 : ∀ j : Fin 16,
    RecoveryCheck ⟨512 + j.val, by omega⟩ := by
  simp only [recoveryCheck_iff]
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
private theorem checked33 : ∀ j : Fin 16,
    RecoveryCheck ⟨528 + j.val, by omega⟩ := by
  simp only [recoveryCheck_iff]
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
private theorem checked34 : ∀ j : Fin 16,
    RecoveryCheck ⟨544 + j.val, by omega⟩ := by
  simp only [recoveryCheck_iff]
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
private theorem checked35 : ∀ j : Fin 16,
    RecoveryCheck ⟨560 + j.val, by omega⟩ := by
  simp only [recoveryCheck_iff]
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
private theorem checked36 : ∀ j : Fin 16,
    RecoveryCheck ⟨576 + j.val, by omega⟩ := by
  simp only [recoveryCheck_iff]
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
private theorem checked37 : ∀ j : Fin 16,
    RecoveryCheck ⟨592 + j.val, by omega⟩ := by
  simp only [recoveryCheck_iff]
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
private theorem checked38 : ∀ j : Fin 16,
    RecoveryCheck ⟨608 + j.val, by omega⟩ := by
  simp only [recoveryCheck_iff]
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
private theorem checked39 : ∀ j : Fin 16,
    RecoveryCheck ⟨624 + j.val, by omega⟩ := by
  simp only [recoveryCheck_iff]
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
private theorem checked40 : ∀ j : Fin 16,
    RecoveryCheck ⟨640 + j.val, by omega⟩ := by
  simp only [recoveryCheck_iff]
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
private theorem checked41 : ∀ j : Fin 16,
    RecoveryCheck ⟨656 + j.val, by omega⟩ := by
  simp only [recoveryCheck_iff]
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
private theorem checked42 : ∀ j : Fin 16,
    RecoveryCheck ⟨672 + j.val, by omega⟩ := by
  simp only [recoveryCheck_iff]
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
private theorem checked43 : ∀ j : Fin 16,
    RecoveryCheck ⟨688 + j.val, by omega⟩ := by
  simp only [recoveryCheck_iff]
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
private theorem checked44 : ∀ j : Fin 16,
    RecoveryCheck ⟨704 + j.val, by omega⟩ := by
  simp only [recoveryCheck_iff]
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
private theorem checked45 : ∀ j : Fin 16,
    RecoveryCheck ⟨720 + j.val, by omega⟩ := by
  simp only [recoveryCheck_iff]
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
private theorem checked46 : ∀ j : Fin 16,
    RecoveryCheck ⟨736 + j.val, by omega⟩ := by
  simp only [recoveryCheck_iff]
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
private theorem checked47 : ∀ j : Fin 16,
    RecoveryCheck ⟨752 + j.val, by omega⟩ := by
  simp only [recoveryCheck_iff]
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
private theorem checked48 : ∀ j : Fin 16,
    RecoveryCheck ⟨768 + j.val, by omega⟩ := by
  simp only [recoveryCheck_iff]
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
private theorem checked49 : ∀ j : Fin 16,
    RecoveryCheck ⟨784 + j.val, by omega⟩ := by
  simp only [recoveryCheck_iff]
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
private theorem checked50 : ∀ j : Fin 16,
    RecoveryCheck ⟨800 + j.val, by omega⟩ := by
  simp only [recoveryCheck_iff]
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
private theorem checked51 : ∀ j : Fin 16,
    RecoveryCheck ⟨816 + j.val, by omega⟩ := by
  simp only [recoveryCheck_iff]
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
private theorem checked52 : ∀ j : Fin 16,
    RecoveryCheck ⟨832 + j.val, by omega⟩ := by
  simp only [recoveryCheck_iff]
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
private theorem checked53 : ∀ j : Fin 16,
    RecoveryCheck ⟨848 + j.val, by omega⟩ := by
  simp only [recoveryCheck_iff]
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
private theorem checked54 : ∀ j : Fin 16,
    RecoveryCheck ⟨864 + j.val, by omega⟩ := by
  simp only [recoveryCheck_iff]
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
private theorem checked55 : ∀ j : Fin 16,
    RecoveryCheck ⟨880 + j.val, by omega⟩ := by
  simp only [recoveryCheck_iff]
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
private theorem checked56 : ∀ j : Fin 16,
    RecoveryCheck ⟨896 + j.val, by omega⟩ := by
  simp only [recoveryCheck_iff]
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
private theorem checked57 : ∀ j : Fin 16,
    RecoveryCheck ⟨912 + j.val, by omega⟩ := by
  simp only [recoveryCheck_iff]
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
private theorem checked58 : ∀ j : Fin 16,
    RecoveryCheck ⟨928 + j.val, by omega⟩ := by
  simp only [recoveryCheck_iff]
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
private theorem checked59 : ∀ j : Fin 16,
    RecoveryCheck ⟨944 + j.val, by omega⟩ := by
  simp only [recoveryCheck_iff]
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
private theorem checked60 : ∀ j : Fin 16,
    RecoveryCheck ⟨960 + j.val, by omega⟩ := by
  simp only [recoveryCheck_iff]
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
private theorem checked61 : ∀ j : Fin 16,
    RecoveryCheck ⟨976 + j.val, by omega⟩ := by
  simp only [recoveryCheck_iff]
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
private theorem checked62 : ∀ j : Fin 16,
    RecoveryCheck ⟨992 + j.val, by omega⟩ := by
  simp only [recoveryCheck_iff]
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
private theorem checked63 : ∀ j : Fin 16,
    RecoveryCheck ⟨1008 + j.val, by omega⟩ := by
  simp only [recoveryCheck_iff]
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
private theorem checked64 : ∀ j : Fin 16,
    RecoveryCheck ⟨1024 + j.val, by omega⟩ := by
  simp only [recoveryCheck_iff]
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
private theorem checked65 : ∀ j : Fin 16,
    RecoveryCheck ⟨1040 + j.val, by omega⟩ := by
  simp only [recoveryCheck_iff]
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
private theorem checked66 : ∀ j : Fin 16,
    RecoveryCheck ⟨1056 + j.val, by omega⟩ := by
  simp only [recoveryCheck_iff]
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
private theorem checked67 : ∀ j : Fin 16,
    RecoveryCheck ⟨1072 + j.val, by omega⟩ := by
  simp only [recoveryCheck_iff]
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
private theorem checked68 : ∀ j : Fin 16,
    RecoveryCheck ⟨1088 + j.val, by omega⟩ := by
  simp only [recoveryCheck_iff]
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
private theorem checked69 : ∀ j : Fin 16,
    RecoveryCheck ⟨1104 + j.val, by omega⟩ := by
  simp only [recoveryCheck_iff]
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
private theorem checked70 : ∀ j : Fin 16,
    RecoveryCheck ⟨1120 + j.val, by omega⟩ := by
  simp only [recoveryCheck_iff]
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
private theorem checked71 : ∀ j : Fin 16,
    RecoveryCheck ⟨1136 + j.val, by omega⟩ := by
  simp only [recoveryCheck_iff]
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
private theorem checked72 : ∀ j : Fin 16,
    RecoveryCheck ⟨1152 + j.val, by omega⟩ := by
  simp only [recoveryCheck_iff]
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
private theorem checked73 : ∀ j : Fin 16,
    RecoveryCheck ⟨1168 + j.val, by omega⟩ := by
  simp only [recoveryCheck_iff]
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
private theorem checked74 : ∀ j : Fin 16,
    RecoveryCheck ⟨1184 + j.val, by omega⟩ := by
  simp only [recoveryCheck_iff]
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
private theorem checked75 : ∀ j : Fin 16,
    RecoveryCheck ⟨1200 + j.val, by omega⟩ := by
  simp only [recoveryCheck_iff]
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
private theorem checked76 : ∀ j : Fin 5,
    RecoveryCheck ⟨1216 + j.val, by omega⟩ := by
  simp only [recoveryCheck_iff]
  decide +kernel

set_option maxRecDepth 10000 in
/-- All 1221 identities are checked. -/
theorem allRecoveryChecks (i : Fin 1221) : RecoveryCheck i := by
  by_cases hi : i.val < 1216
  · have h : ∀ b : Fin 76, ∀ j : Fin 16,
          RecoveryCheck ⟨16 * b.val + j.val, by omega⟩ := by
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
        · exact checked39
        · exact checked40
        · exact checked41
        · exact checked42
        · exact checked43
        · exact checked44
        · exact checked45
        · exact checked46
        · exact checked47
        · exact checked48
        · exact checked49
        · exact checked50
        · exact checked51
        · exact checked52
        · exact checked53
        · exact checked54
        · exact checked55
        · exact checked56
        · exact checked57
        · exact checked58
        · exact checked59
        · exact checked60
        · exact checked61
        · exact checked62
        · exact checked63
        · exact checked64
        · exact checked65
        · exact checked66
        · exact checked67
        · exact checked68
        · exact checked69
        · exact checked70
        · exact checked71
        · exact checked72
        · exact checked73
        · exact checked74
        · exact checked75
    have hb : i.val / 16 < 76 := by omega
    have hm : i.val % 16 < 16 := Nat.mod_lt _ (by decide)
    have hx := h ⟨i.val / 16, hb⟩ ⟨i.val % 16, hm⟩
    have heq : (⟨16 * (i.val / 16) + i.val % 16, by omega⟩ : Fin 1221) = i :=
      Fin.ext (Nat.div_add_mod i.val 16)
    exact heq ▸ hx
  · have hx := checked76 ⟨i.val - 1216, by omega⟩
    have heq : (⟨1216 + (i.val - 1216), by omega⟩ : Fin 1221) = i :=
      Fin.ext (show 1216 + (i.val - 1216) = i.val by omega)
    exact heq ▸ hx

end Janko4.LocalStructure.MathieuSeedCentralizer.KernelBound.ShearRigidity.MixedCompleteness
