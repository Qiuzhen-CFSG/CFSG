module
public import Theory.SpecificGroups.Tits.MinimumIndex.LargeTwoOvergroups.SeedCoverage.Schreier
public import Mathlib.Data.Fintype.Pi

/-! Kernel-checked binary Schreier words for level 3, node 18.
Source: Parrott (1972), §5; witness discovery in `source/`.
The words certify both containments after conjugation in the marked Sylow group. -/
namespace Tits.MinimumIndex.LargeTwoOvergroups.SeedCoverage
set_option maxRecDepth 20000
private def pivot : Fin 16 → Fin 4 :=
  ![0, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0]
private def data : Fin 16 → BranchData 3 4 :=
  ![⟨55, 0, ⟨(![[], [0], [1], [2], [], [0], [0, 0, 1, 0, 0], [2]] : Fin 8 → List (Fin 3)), (![[1], [2], [3]] : Fin 3 → List (Fin 8))⟩⟩, ⟨55, 0, ⟨(![[], [0], [1], [2], [], [0], [0, 0, 1, 0, 0], [2]] : Fin 8 → List (Fin 3)), (![[1], [2], [3]] : Fin 3 → List (Fin 8))⟩⟩, ⟨19, 12, ⟨(![[0], [], [0, 1, 3, 3, 3], [4, 2, 3], [0], [1], [0, 2, 3, 3, 3], [4, 3]] : Fin 8 → List (Fin 5)), (![[0], [5], [2, 7, 2, 3], [0, 7, 6, 3], [3, 6, 0]] : Fin 5 → List (Fin 8))⟩⟩, ⟨59, 0, ⟨(![[], [0], [1], [2], [], [0], [0, 0, 1, 0, 0], [2]] : Fin 8 → List (Fin 3)), (![[1], [2], [3]] : Fin 3 → List (Fin 8))⟩⟩, ⟨38, 0, ⟨(![[0], [2], [], [3], [0, 1, 1, 2, 2], [1, 1, 3, 2, 3], [1, 1, 1, 3, 2, 3], [1, 1, 1, 3, 2]] : Fin 8 → List (Fin 4)), (![[0], [3, 1, 7], [1], [3]] : Fin 4 → List (Fin 8))⟩⟩, ⟨54, 0, ⟨(![[], [0], [0, 0, 1, 0, 0], [2], [], [0], [1], [2]] : Fin 8 → List (Fin 3)), (![[1], [6], [3]] : Fin 3 → List (Fin 8))⟩⟩, ⟨19, 0, ⟨(![[1], [], [2, 3], [4], [1], [0], [0, 3], [0, 2, 4]] : Fin 8 → List (Fin 5)), (![[5], [0], [3, 7, 5], [5, 6], [3]] : Fin 5 → List (Fin 8))⟩⟩, ⟨58, 0, ⟨(![[], [0], [0, 0, 1, 0, 0], [2], [], [0], [1], [2]] : Fin 8 → List (Fin 3)), (![[1], [6], [3]] : Fin 3 → List (Fin 8))⟩⟩, ⟨39, 1, ⟨(![[0], [1, 1, 1], [2, 1, 1], [], [0], [2, 1, 2, 2, 2], [1, 1, 2, 2, 2], []] : Fin 8 → List (Fin 3)), (![[0], [1, 1, 1], [2, 1, 1]] : Fin 3 → List (Fin 8))⟩⟩, ⟨59, 2, ⟨(![[], [0, 2, 0, 0, 2], [0, 0, 1], [0, 0, 0, 2, 0], [], [0, 2, 0, 0, 2], [1, 0, 0], [0, 0, 0, 2, 0]] : Fin 8 → List (Fin 3)), (![[1, 3, 1, 1, 3], [1, 1, 2], [1, 1, 1, 3, 1]] : Fin 3 → List (Fin 8))⟩⟩, ⟨20, 768, ⟨(![[3, 0, 3], [], [3, 2, 3], [0, 2, 0, 2, 3, 2], [3, 0, 3], [0, 1, 3, 0, 3], [2, 2, 2], [0, 2, 0, 3]] : Fin 8 → List (Fin 4)), (![[0, 3, 5, 7, 5], [3, 5, 7], [2, 2, 6], [0, 2, 0, 3]] : Fin 4 → List (Fin 8))⟩⟩, ⟨55, 2, ⟨(![[], [0, 2, 0, 0, 2], [0, 0, 1], [0, 0, 0, 2, 0], [], [0, 2, 0, 0, 2], [1, 0, 0], [0, 0, 0, 2, 0]] : Fin 8 → List (Fin 3)), (![[1, 3, 1, 1, 3], [1, 1, 2], [1, 1, 1, 3, 1]] : Fin 3 → List (Fin 8))⟩⟩, ⟨22, 12, ⟨(![[0], [3, 4, 0, 4], [], [1, 4, 3], [4, 0, 4], [0, 2, 4, 0, 4], [1, 1, 1, 2], [1, 4, 3]] : Fin 8 → List (Fin 5)), (![[0], [0, 4, 5, 6], [0, 4, 5], [1, 4], [0, 1, 3, 5, 6]] : Fin 5 → List (Fin 8))⟩⟩, ⟨58, 2, ⟨(![[], [0, 2, 0, 0, 2], [1, 0, 0], [0, 0, 0, 2, 0], [], [0, 2, 0, 0, 2], [0, 0, 1], [0, 0, 0, 2, 0]] : Fin 8 → List (Fin 3)), (![[1, 3, 1, 1, 3], [1, 1, 6], [1, 1, 1, 3, 1]] : Fin 3 → List (Fin 8))⟩⟩, ⟨21, 12, ⟨(![[0], [], [0, 1, 3, 2, 3], [2, 3, 2, 2], [0], [1], [2, 0, 2, 2], [0, 3, 0, 2]] : Fin 8 → List (Fin 4)), (![[0], [5], [0, 2, 2, 6], [0, 7, 6]] : Fin 4 → List (Fin 8))⟩⟩, ⟨54, 2, ⟨(![[], [0, 2, 0, 0, 2], [1, 0, 0], [0, 0, 0, 2, 0], [], [0, 2, 0, 0, 2], [0, 0, 1], [0, 0, 0, 2, 0]] : Fin 8 → List (Fin 3)), (![[1, 3, 1, 1, 3], [1, 1, 6], [1, 1, 1, 3, 1]] : Fin 3 → List (Fin 8))⟩⟩]
set_option maxHeartbeats 1600000 in
public theorem step_3_18 : Step 3 18 := by
  apply step_of_checks 3 18
    (fun σ => pivot ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩)
    (fun σ => data ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩)
  unfold BranchData.Valid PointValid
  decide +kernel
end Tits.MinimumIndex.LargeTwoOvergroups.SeedCoverage
