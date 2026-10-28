module
public import Theory.SpecificGroups.Tits.MinimumIndex.LargeTwoOvergroups.SeedCoverage.Schreier
public import Mathlib.Data.Fintype.Pi

/-! Kernel-checked binary Schreier words for level 4, node 17.
Source: Parrott (1972), §5; witness discovery in `source/`.
The words certify both containments after conjugation in the marked Sylow group. -/
namespace Tits.MinimumIndex.LargeTwoOvergroups.SeedCoverage
set_option maxRecDepth 20000
private def pivot : Fin 16 → Fin 4 :=
  ![0, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0]
private def data : Fin 16 → BranchData 4 4 :=
  ![⟨40, 0, ⟨(![[], [1, 2], [3], [0, 5, 3], [], [1, 2], [3], [3, 5, 1]] : Fin 8 → List (Fin 6)), (![[1, 2, 2, 3, 7], [1, 3, 7], [3, 7], [2], [3, 1, 7], [1, 7, 2]] : Fin 6 → List (Fin 8))⟩⟩, ⟨40, 0, ⟨(![[], [1, 2], [3], [0, 5, 3], [], [1, 2], [3], [3, 5, 1]] : Fin 8 → List (Fin 6)), (![[1, 2, 2, 3, 7], [1, 3, 7], [3, 7], [2], [3, 1, 7], [1, 7, 2]] : Fin 6 → List (Fin 8))⟩⟩, ⟨74, 0, ⟨(![[1, 2], [], [3], [0, 5, 3], [1, 2], [], [3], [3, 5, 1]] : Fin 8 → List (Fin 6)), (![[2, 2, 3, 0, 3], [3, 0, 3], [0, 3, 0, 3], [2], [7, 0, 3], [3, 0, 2]] : Fin 6 → List (Fin 8))⟩⟩, ⟨38, 0, ⟨(![[], [0], [3], [0, 5, 3], [], [0], [3], [0, 2, 5, 3]] : Fin 8 → List (Fin 6)), (![[1], [1, 2, 2], [3, 7], [2], [3, 1, 7, 1], [2, 3, 1]] : Fin 6 → List (Fin 8))⟩⟩, ⟨36, 0, ⟨(![[2, 3], [0, 2, 3], [], [1, 5, 0], [2, 3], [0, 2, 3], [0, 1, 2], [2, 5]] : Fin 8 → List (Fin 6)), (![[0, 1], [3, 1, 7], [3, 0, 3], [0, 3, 0, 3], [1, 3, 7], [7, 0]] : Fin 6 → List (Fin 8))⟩⟩, ⟨38, 128, ⟨(![[], [1, 2], [0, 1, 3], [0, 2, 5, 3], [], [1, 2], [0, 1, 3], [0, 5, 3]] : Fin 8 → List (Fin 6)), (![[1, 2, 2, 3, 7], [1, 3, 7], [3, 7], [2, 2, 2], [3, 1, 7, 1], [2, 3, 1]] : Fin 6 → List (Fin 8))⟩⟩, ⟨79, 0, ⟨(![[1, 2], [], [1, 2, 3], [3, 5, 4], [1, 2], [], [1, 2, 3], [3, 5, 1]] : Fin 8 → List (Fin 6)), (![[2, 2, 3, 0, 3], [3, 0, 3], [0, 3, 0, 3], [0, 2], [7, 0, 3], [0, 7, 0, 2]] : Fin 6 → List (Fin 8))⟩⟩, ⟨40, 128, ⟨(![[], [0], [0, 1, 3], [3, 5, 1], [], [0], [0, 1, 3], [0, 5, 3]] : Fin 8 → List (Fin 6)), (![[1], [1, 2, 2], [3, 7], [2, 2, 2], [1, 3, 1, 3, 1], [1, 7, 2]] : Fin 6 → List (Fin 8))⟩⟩, ⟨34, 12, ⟨(![[0, 1, 2, 3], [1, 2, 3], [1, 4], [], [0, 1, 2], [4, 5, 0], [0, 5], []] : Fin 8 → List (Fin 6)), (![[0, 1], [5, 2, 6], [2, 2], [0, 4], [5, 6], [0, 1, 6]] : Fin 6 → List (Fin 8))⟩⟩, ⟨39, 0, ⟨(![[], [1, 2], [3], [0, 1, 5, 3], [], [1, 2], [3], [0, 3, 5, 0]] : Fin 8 → List (Fin 6)), (![[1, 2, 2, 3, 3], [1, 3, 3], [3, 3], [2], [3, 1, 3], [3, 2]] : Fin 6 → List (Fin 8))⟩⟩, ⟨75, 0, ⟨(![[1, 2], [], [3], [3, 5], [1, 2], [], [3], [0, 3, 4, 5]] : Fin 8 → List (Fin 6)), (![[2, 2, 3, 0, 7], [3, 0, 7], [0, 3, 0, 7], [2], [7, 0, 7], [0, 7, 0, 2]] : Fin 6 → List (Fin 8))⟩⟩, ⟨37, 0, ⟨(![[], [0], [3], [0, 1, 5, 3], [], [0], [3], [4, 3, 5]] : Fin 8 → List (Fin 6)), (![[1], [1, 2, 2], [3, 3], [2], [3, 1, 3, 1], [3, 2]] : Fin 6 → List (Fin 8))⟩⟩, ⟨35, 0, ⟨(![[2, 3], [0, 2, 3], [], [0, 1, 5], [2, 3], [0, 2, 3], [0, 1, 2], [1, 5, 0]] : Fin 8 → List (Fin 6)), (![[0, 1], [3, 1, 3, 6], [3, 0, 7], [0, 3, 0, 7], [1, 7, 7], [3, 0, 6]] : Fin 6 → List (Fin 8))⟩⟩, ⟨37, 128, ⟨(![[], [1, 2], [0, 1, 3], [4, 3, 5], [], [1, 2], [0, 1, 3], [0, 1, 5, 3]] : Fin 8 → List (Fin 6)), (![[1, 2, 2, 3, 3], [1, 3, 3], [3, 3], [2, 2, 2], [3, 1, 3, 1], [1, 2, 7, 1]] : Fin 6 → List (Fin 8))⟩⟩, ⟨78, 0, ⟨(![[1, 2], [], [1, 2, 3], [3, 5], [1, 2], [], [1, 2, 3], [0, 4, 5, 3]] : Fin 8 → List (Fin 6)), (![[2, 2, 3, 0, 7], [3, 0, 7], [0, 3, 0, 7], [0, 2], [7, 0, 7], [3, 0, 2]] : Fin 6 → List (Fin 8))⟩⟩, ⟨39, 128, ⟨(![[], [0], [0, 1, 3], [0, 3, 5, 0], [], [0], [0, 1, 3], [0, 1, 5, 3]] : Fin 8 → List (Fin 6)), (![[1], [1, 2, 2], [3, 3], [2, 2, 2], [1, 3, 1, 7, 1], [1, 2, 3, 1]] : Fin 6 → List (Fin 8))⟩⟩]
set_option maxHeartbeats 1600000 in
public theorem step_4_17 : Step 4 17 := by
  apply step_of_checks 4 17
    (fun σ => pivot ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩)
    (fun σ => data ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩)
  unfold BranchData.Valid PointValid
  decide +kernel
end Tits.MinimumIndex.LargeTwoOvergroups.SeedCoverage
