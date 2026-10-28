module
public import Theory.SpecificGroups.Tits.MinimumIndex.LargeTwoOvergroups.SeedCoverage.Schreier
public import Mathlib.Data.Fintype.Pi

/-! Kernel-checked binary Schreier words for level 3, node 12.
Source: Parrott (1972), §5; witness discovery in `source/`.
The words certify both containments after conjugation in the marked Sylow group. -/
namespace Tits.MinimumIndex.LargeTwoOvergroups.SeedCoverage
set_option maxRecDepth 20000
private def pivot : Fin 16 → Fin 4 :=
  ![0, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0]
private def data : Fin 16 → BranchData 3 4 :=
  ![⟨38, 0, ⟨(![[], [1], [2], [3], [], [0, 1, 2, 2], [0, 1, 1, 2], [0, 1, 1, 2, 3, 2]] : Fin 8 → List (Fin 4)), (![[1, 1, 1, 2, 1, 6], [1], [2], [3]] : Fin 4 → List (Fin 8))⟩⟩, ⟨38, 0, ⟨(![[], [1], [2], [3], [], [0, 1, 2, 2], [0, 1, 1, 2], [0, 1, 1, 2, 3, 2]] : Fin 8 → List (Fin 4)), (![[1, 1, 1, 2, 1, 6], [1], [2], [3]] : Fin 4 → List (Fin 8))⟩⟩, ⟨36, 0, ⟨(![[0], [], [1], [2], [2, 0, 1, 2, 1], [2, 1, 1, 2], [0, 1, 2, 0, 1, 2, 1], [1, 2, 1, 1, 1]] : Fin 8 → List (Fin 3)), (![[0], [2], [3]] : Fin 3 → List (Fin 8))⟩⟩, ⟨51, 0, ⟨(![[], [1, 0, 1, 1, 1], [1], [2], [], [0], [0, 0, 1, 1, 1], [0, 1, 2, 0, 1]] : Fin 8 → List (Fin 3)), (![[5], [2], [3]] : Fin 3 → List (Fin 8))⟩⟩, ⟨32, 0, ⟨(![[0], [1], [], [2], [2, 0, 1, 2, 1], [0, 1, 2, 0, 1, 2, 1], [2, 1, 1, 2], [1, 2, 1, 1, 1]] : Fin 8 → List (Fin 3)), (![[0], [1], [3]] : Fin 3 → List (Fin 8))⟩⟩, ⟨46, 0, ⟨(![[], [0], [0, 0, 0, 1, 0], [2], [], [0, 0, 0, 1, 1], [1], [1, 0, 2, 1, 0]] : Fin 8 → List (Fin 3)), (![[1], [6], [3]] : Fin 3 → List (Fin 8))⟩⟩, ⟨18, 0, ⟨(![[1], [], [0, 1, 3, 1], [4], [0, 1, 2], [4, 0, 4], [1, 3, 1], [1, 2, 4, 1]] : Fin 8 → List (Fin 5)), (![[2, 6], [0], [0, 2, 6, 4], [2, 5], [3]] : Fin 5 → List (Fin 8))⟩⟩, ⟨22, 0, ⟨(![[], [0, 1, 3, 3], [0, 1, 1, 2], [4], [], [1], [2], [2, 4, 3]] : Fin 8 → List (Fin 5)), (![[2, 6], [5], [6], [3, 7, 6], [3]] : Fin 5 → List (Fin 8))⟩⟩, ⟨30, 0, ⟨(![[0], [1], [2], [], [1, 2, 3, 1], [0, 2, 3, 1], [0, 2, 3, 2], []] : Fin 8 → List (Fin 4)), (![[0], [1], [2], [4, 2]] : Fin 4 → List (Fin 8))⟩⟩, ⟨38, 1, ⟨(![[], [0, 1, 2, 2], [1, 2, 1], [1, 2, 1, 3], [], [1], [0, 1, 1, 1, 2, 1], [3, 2]] : Fin 8 → List (Fin 4)), (![[1, 1, 1, 2, 1, 6], [5], [1, 2, 1], [7, 2]] : Fin 4 → List (Fin 8))⟩⟩, ⟨36, 1024, ⟨(![[2, 1, 0, 1, 2], [], [1, 2, 1, 1, 2], [0, 1, 2, 0, 1, 1], [1, 1, 2, 0, 2], [2, 1, 1, 2], [1, 1, 1], [1, 2, 1, 1]] : Fin 8 → List (Fin 3)), (![[0, 3, 3, 5], [2, 5], [3, 2]] : Fin 3 → List (Fin 8))⟩⟩, ⟨51, 1, ⟨(![[], [0], [1, 1, 1], [1, 1, 1, 2], [], [1, 0, 1, 1, 1], [0, 0, 1], [2, 1]] : Fin 8 → List (Fin 3)), (![[1], [1, 1, 6], [7, 2]] : Fin 3 → List (Fin 8))⟩⟩, ⟨32, 1, ⟨(![[0], [0, 1, 0], [], [0, 1, 1, 2], [2, 0, 1, 2, 1], [0, 1, 1, 2, 0, 1, 2], [2, 1, 1, 2], [2, 0, 1, 1]] : Fin 8 → List (Fin 3)), (![[0], [0, 1, 0], [0, 3, 6]] : Fin 3 → List (Fin 8))⟩⟩, ⟨46, 1024, ⟨(![[], [0, 0, 0], [0, 1, 2, 0, 2], [0, 1, 1, 2, 1], [], [0, 0, 1, 0, 1, 1, 1], [0, 2, 0, 2, 1], [2, 0, 1]] : Fin 8 → List (Fin 3)), (![[1, 1, 1], [2, 3, 3], [1, 1, 1, 2, 7]] : Fin 3 → List (Fin 8))⟩⟩, ⟨18, 1, ⟨(![[1], [], [0, 1, 2, 3, 1], [1, 2, 3, 4], [0, 1, 2], [4, 0, 4], [1, 2, 3, 1], [2, 4, 3, 1]] : Fin 8 → List (Fin 5)), (![[2, 6], [0], [0, 2, 6, 4], [0, 2, 4], [0, 3, 6]] : Fin 5 → List (Fin 8))⟩⟩, ⟨52, 0, ⟨(![[], [0, 0, 2, 2, 2, 0, 2], [0, 0, 2, 2, 2, 1, 2], [2, 2, 2], [], [0], [1], [2]] : Fin 8 → List (Fin 3)), (![[5], [6], [7]] : Fin 3 → List (Fin 8))⟩⟩]
set_option maxHeartbeats 1600000 in
public theorem step_3_12 : Step 3 12 := by
  apply step_of_checks 3 12
    (fun σ => pivot ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩)
    (fun σ => data ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩)
  unfold BranchData.Valid PointValid
  decide +kernel
end Tits.MinimumIndex.LargeTwoOvergroups.SeedCoverage
