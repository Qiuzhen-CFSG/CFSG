module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.PermutationClassification.Enumeration.Encoding
import Mathlib.Tactic.FinCases

/-!
# Kernel certificates for the four-candidate enumeration

The 22⁴ · 2 tables of `Encoding` include every permutation under consideration.
The condition `n²(1) = 1` first forces one representative image whenever
`n(1) ≠ 1`. The remaining certificates therefore have only two free point
images. The case `n(1) = 1` is subdivided by the image of 2.

All computations use `decide +kernel`. No external enumeration result is
imported into Lean. The four surviving tuples are checked against the actual
source permutations in `Encoding`.

Source: Janko, *A characterization of the Mathieu simple groups, I* (1968),
Section 9, p.18.
-/

namespace Theory.GroupTheory.HeldM22A10.M22Identification.PermutationClassification.Enumeration

set_option maxRecDepth 100000

private theorem phase0_eq_one : ∀ x : Fin 22,
    mSquare^[0] x = 1 → x = 1 := by decide +kernel

private theorem phase1_eq_one : ∀ x : Fin 22,
    mSquare^[1] x = 1 → x = 9 := by decide +kernel

private theorem phase2_eq_one : ∀ x : Fin 22,
    mSquare^[2] x = 1 → x = 4 := by decide +kernel

private theorem phase3_eq_one : ∀ x : Fin 22,
    mSquare^[3] x = 1 → x = 3 := by decide +kernel

private theorem phase4_eq_one : ∀ x : Fin 22,
    mSquare^[4] x = 1 → x = 5 := by decide +kernel

private theorem row01_00 : ∀ (c d : Fin 22) (s : Fin 2),
    PassesTests (candidateTable 1 0 c d s) → IsSurvivor 1 0 c d s := by
  decide +kernel

private theorem row01_01 : ∀ (c d : Fin 22) (s : Fin 2),
    PassesTests (candidateTable 1 1 c d s) → IsSurvivor 1 1 c d s := by
  decide +kernel

private theorem row01_02 : ∀ (c d : Fin 22) (s : Fin 2),
    PassesTests (candidateTable 1 2 c d s) → IsSurvivor 1 2 c d s := by
  decide +kernel

private theorem row01_03 : ∀ (c d : Fin 22) (s : Fin 2),
    PassesTests (candidateTable 1 3 c d s) → IsSurvivor 1 3 c d s := by
  decide +kernel

private theorem row01_04 : ∀ (c d : Fin 22) (s : Fin 2),
    PassesTests (candidateTable 1 4 c d s) → IsSurvivor 1 4 c d s := by
  decide +kernel

private theorem row01_05 : ∀ (c d : Fin 22) (s : Fin 2),
    PassesTests (candidateTable 1 5 c d s) → IsSurvivor 1 5 c d s := by
  decide +kernel

private theorem row01_06 : ∀ (c d : Fin 22) (s : Fin 2),
    PassesTests (candidateTable 1 6 c d s) → IsSurvivor 1 6 c d s := by
  decide +kernel

private theorem row01_07 : ∀ (c d : Fin 22) (s : Fin 2),
    PassesTests (candidateTable 1 7 c d s) → IsSurvivor 1 7 c d s := by
  decide +kernel

private theorem row01_08 : ∀ (c d : Fin 22) (s : Fin 2),
    PassesTests (candidateTable 1 8 c d s) → IsSurvivor 1 8 c d s := by
  decide +kernel

private theorem row01_09 : ∀ (c d : Fin 22) (s : Fin 2),
    PassesTests (candidateTable 1 9 c d s) → IsSurvivor 1 9 c d s := by
  decide +kernel

private theorem row01_10 : ∀ (c d : Fin 22) (s : Fin 2),
    PassesTests (candidateTable 1 10 c d s) → IsSurvivor 1 10 c d s := by
  decide +kernel

private theorem row01_11 : ∀ (c d : Fin 22) (s : Fin 2),
    PassesTests (candidateTable 1 11 c d s) → IsSurvivor 1 11 c d s := by
  decide +kernel

private theorem row01_12 : ∀ (c d : Fin 22) (s : Fin 2),
    PassesTests (candidateTable 1 12 c d s) → IsSurvivor 1 12 c d s := by
  decide +kernel

private theorem row01_13 : ∀ (c d : Fin 22) (s : Fin 2),
    PassesTests (candidateTable 1 13 c d s) → IsSurvivor 1 13 c d s := by
  decide +kernel

private theorem row01_14 : ∀ (c d : Fin 22) (s : Fin 2),
    PassesTests (candidateTable 1 14 c d s) → IsSurvivor 1 14 c d s := by
  decide +kernel

private theorem row01_15 : ∀ (c d : Fin 22) (s : Fin 2),
    PassesTests (candidateTable 1 15 c d s) → IsSurvivor 1 15 c d s := by
  decide +kernel

private theorem row01_16 : ∀ (c d : Fin 22) (s : Fin 2),
    PassesTests (candidateTable 1 16 c d s) → IsSurvivor 1 16 c d s := by
  decide +kernel

private theorem row01_17 : ∀ (c d : Fin 22) (s : Fin 2),
    PassesTests (candidateTable 1 17 c d s) → IsSurvivor 1 17 c d s := by
  decide +kernel

private theorem row01_18 : ∀ (c d : Fin 22) (s : Fin 2),
    PassesTests (candidateTable 1 18 c d s) → IsSurvivor 1 18 c d s := by
  decide +kernel

private theorem row01_19 : ∀ (c d : Fin 22) (s : Fin 2),
    PassesTests (candidateTable 1 19 c d s) → IsSurvivor 1 19 c d s := by
  decide +kernel

private theorem row01_20 : ∀ (c d : Fin 22) (s : Fin 2),
    PassesTests (candidateTable 1 20 c d s) → IsSurvivor 1 20 c d s := by
  decide +kernel

private theorem row01_21 : ∀ (c d : Fin 22) (s : Fin 2),
    PassesTests (candidateTable 1 21 c d s) → IsSurvivor 1 21 c d s := by
  decide +kernel

private theorem row01 : ∀ (b c d : Fin 22) (s : Fin 2),
    PassesTests (candidateTable 1 b c d s) → IsSurvivor 1 b c d s := by
  intro b
  fin_cases b
  · exact row01_00
  · exact row01_01
  · exact row01_02
  · exact row01_03
  · exact row01_04
  · exact row01_05
  · exact row01_06
  · exact row01_07
  · exact row01_08
  · exact row01_09
  · exact row01_10
  · exact row01_11
  · exact row01_12
  · exact row01_13
  · exact row01_14
  · exact row01_15
  · exact row01_16
  · exact row01_17
  · exact row01_18
  · exact row01_19
  · exact row01_20
  · exact row01_21

private theorem row02 : ∀ (c d : Fin 22) (s : Fin 2),
    PassesTests (candidateTable 2 1 c d s) → IsSurvivor 2 1 c d s := by
  decide +kernel

private theorem row08 : ∀ (c d : Fin 22) (s : Fin 2),
    PassesTests (candidateTable 8 9 c d s) → IsSurvivor 8 9 c d s := by
  decide +kernel

private theorem row10 : ∀ (c d : Fin 22) (s : Fin 2),
    PassesTests (candidateTable 10 4 c d s) → IsSurvivor 10 4 c d s := by
  decide +kernel

private theorem row07 : ∀ (c d : Fin 22) (s : Fin 2),
    PassesTests (candidateTable 7 3 c d s) → IsSurvivor 7 3 c d s := by
  decide +kernel

private theorem row06 : ∀ (c d : Fin 22) (s : Fin 2),
    PassesTests (candidateTable 6 5 c d s) → IsSurvivor 6 5 c d s := by
  decide +kernel

private theorem row12 : ∀ (b d : Fin 22) (s : Fin 2),
    PassesTests (candidateTable 12 b 1 d s) → IsSurvivor 12 b 1 d s := by
  decide +kernel

private theorem row15 : ∀ (b d : Fin 22) (s : Fin 2),
    PassesTests (candidateTable 15 b 9 d s) → IsSurvivor 15 b 9 d s := by
  decide +kernel

private theorem row16 : ∀ (b d : Fin 22) (s : Fin 2),
    PassesTests (candidateTable 16 b 4 d s) → IsSurvivor 16 b 4 d s := by
  decide +kernel

private theorem row20 : ∀ (b d : Fin 22) (s : Fin 2),
    PassesTests (candidateTable 20 b 3 d s) → IsSurvivor 20 b 3 d s := by
  decide +kernel

private theorem row14 : ∀ (b d : Fin 22) (s : Fin 2),
    PassesTests (candidateTable 14 b 5 d s) → IsSurvivor 14 b 5 d s := by
  decide +kernel

private theorem row13 : ∀ (b c : Fin 22) (s : Fin 2),
    PassesTests (candidateTable 13 b c 1 s) → IsSurvivor 13 b c 1 s := by
  decide +kernel

private theorem row19 : ∀ (b c : Fin 22) (s : Fin 2),
    PassesTests (candidateTable 19 b c 9 s) → IsSurvivor 19 b c 9 s := by
  decide +kernel

private theorem row21 : ∀ (b c : Fin 22) (s : Fin 2),
    PassesTests (candidateTable 21 b c 4 s) → IsSurvivor 21 b c 4 s := by
  decide +kernel

private theorem row18 : ∀ (b c : Fin 22) (s : Fin 2),
    PassesTests (candidateTable 18 b c 3 s) → IsSurvivor 18 b c 3 s := by
  decide +kernel

private theorem row17 : ∀ (b c : Fin 22) (s : Fin 2),
    PassesTests (candidateTable 17 b c 5 s) → IsSurvivor 17 b c 5 s := by
  decide +kernel

/-- Exhaustive filtering of the finite table parametrization. -/
public theorem exhaustive (a b c d : Fin 22) (s : Fin 2)
    (h : PassesTests (candidateTable a b c d s)) : IsSurvivor a b c d s := by
  have hs := h.1
  fin_cases a
  · have hn : ∀ s : Fin 2, (if s = 0 then 0 else 11 : Fin 22) ≠ 1 := by decide +kernel
    exact False.elim (hn s hs)
  · exact row01 b c d s h
  · have he : b = 1 := phase0_eq_one b hs
    subst b
    exact row02 c d s h
  · have hn : mSquare^[4] (3 : Fin 22) ≠ 1 := by decide +kernel
    exact False.elim (hn hs)
  · have hn : mSquare^[1] (4 : Fin 22) ≠ 1 := by decide +kernel
    exact False.elim (hn hs)
  · have hn : mSquare^[2] (5 : Fin 22) ≠ 1 := by decide +kernel
    exact False.elim (hn hs)
  · have he : b = 5 := phase4_eq_one b hs
    subst b
    exact row06 c d s h
  · have he : b = 3 := phase3_eq_one b hs
    subst b
    exact row07 c d s h
  · have he : b = 9 := phase1_eq_one b hs
    subst b
    exact row08 c d s h
  · have hn : mSquare^[3] (9 : Fin 22) ≠ 1 := by decide +kernel
    exact False.elim (hn hs)
  · have he : b = 4 := phase2_eq_one b hs
    subst b
    exact row10 c d s h
  · have hn : ∀ s : Fin 2, (if s = 0 then 11 else 0 : Fin 22) ≠ 1 := by decide +kernel
    exact False.elim (hn s hs)
  · have he : c = 1 := phase0_eq_one c hs
    subst c
    exact row12 b d s h
  · have he : d = 1 := phase0_eq_one d hs
    subst d
    exact row13 b c s h
  · have he : c = 5 := phase4_eq_one c hs
    subst c
    exact row14 b d s h
  · have he : c = 9 := phase1_eq_one c hs
    subst c
    exact row15 b d s h
  · have he : c = 4 := phase2_eq_one c hs
    subst c
    exact row16 b d s h
  · have he : d = 5 := phase4_eq_one d hs
    subst d
    exact row17 b c s h
  · have he : d = 3 := phase3_eq_one d hs
    subst d
    exact row18 b c s h
  · have he : d = 9 := phase1_eq_one d hs
    subst d
    exact row19 b c s h
  · have he : c = 3 := phase3_eq_one c hs
    subst c
    exact row20 b d s h
  · have he : d = 4 := phase2_eq_one d hs
    subst d
    exact row21 b c s h

end Theory.GroupTheory.HeldM22A10.M22Identification.PermutationClassification.Enumeration
