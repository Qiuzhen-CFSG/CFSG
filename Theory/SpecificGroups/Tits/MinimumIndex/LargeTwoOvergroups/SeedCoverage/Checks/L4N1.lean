module
public import Theory.SpecificGroups.Tits.MinimumIndex.LargeTwoOvergroups.SeedCoverage.Schreier
public import Mathlib.Data.Fintype.Pi

/-! Kernel-checked binary Schreier words for level 4, node 1.
Source: Parrott (1972), §5; witness discovery in `source/`.
The words certify both containments after conjugation in the marked Sylow group. -/
namespace Tits.MinimumIndex.LargeTwoOvergroups.SeedCoverage
set_option maxRecDepth 20000
private def pivot : Fin 16 → Fin 4 :=
  ![0, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0]
private def data : Fin 16 → BranchData 4 4 :=
  ![⟨32, 0, ⟨(![[], [0, 2, 3], [4], [2, 5], [], [0, 2, 3], [0, 1, 4], [3, 5]] : Fin 8 → List (Fin 6)), (![[1, 3, 7], [1, 2, 3, 2, 3], [2, 2], [2, 2, 3, 7], [2], [2, 2, 3]] : Fin 6 → List (Fin 8))⟩⟩, ⟨32, 0, ⟨(![[], [0, 2, 3], [4], [2, 5], [], [0, 2, 3], [0, 1, 4], [3, 5]] : Fin 8 → List (Fin 6)), (![[1, 3, 7], [1, 2, 3, 2, 3], [2, 2], [2, 2, 3, 7], [2], [2, 2, 3]] : Fin 6 → List (Fin 8))⟩⟩, ⟨8, 0, ⟨(![[0], [], [0, 4], [2, 5], [0], [], [0, 4], [0, 1, 5]] : Fin 8 → List (Fin 6)), (![[0], [0, 2, 2, 3, 7], [2, 2], [0, 2, 3, 2, 7], [0, 2], [2, 2, 3]] : Fin 6 → List (Fin 8))⟩⟩, ⟨21, 0, ⟨(![[], [0, 2, 3], [4], [2, 5], [], [0, 2, 3], [0, 1, 4], [3, 5]] : Fin 8 → List (Fin 6)), (![[1, 3, 7], [1, 2, 3, 2, 3], [2, 2], [2, 2, 3, 7], [2], [2, 2, 3]] : Fin 6 → List (Fin 8))⟩⟩, ⟨4, 0, ⟨(![[0], [1, 3, 4], [], [3, 5], [1, 2], [1, 3, 4], [3], [0, 5, 1, 2]] : Fin 8 → List (Fin 6)), (![[0], [0, 3, 1, 7], [1, 3, 6, 7], [6], [3, 7, 4], [3, 6]] : Fin 6 → List (Fin 8))⟩⟩, ⟨34, 12, ⟨(![[], [1, 2, 3], [0, 4], [1, 3, 4, 5], [], [1, 2, 3], [1, 4], [4, 5, 0]] : Fin 8 → List (Fin 6)), (![[1, 3, 7], [1, 2, 3, 6, 7], [2, 2], [2, 3, 7, 6], [1, 2, 3, 7], [2, 7]] : Fin 6 → List (Fin 8))⟩⟩, ⟨32, 1792, ⟨(![[2, 5], [], [0, 5, 0, 4], [0, 3], [2, 5], [], [0, 5, 0, 4], [0, 2, 3]] : Fin 8 → List (Fin 6)), (![[2, 3, 2], [2, 2, 7], [3, 7], [2, 3, 2, 3], [0, 3, 2, 7], [0, 3, 7]] : Fin 6 → List (Fin 8))⟩⟩, ⟨19, 0, ⟨(![[], [0, 2, 3], [0, 1, 4], [2, 5], [], [0, 2, 3], [4], [3, 5]] : Fin 8 → List (Fin 6)), (![[1, 3, 7], [1, 2, 3, 6, 7], [2, 6], [2, 3, 7, 6], [6], [2, 6, 3]] : Fin 6 → List (Fin 8))⟩⟩, ⟨3, 0, ⟨(![[0], [1, 3, 4], [0, 5], [], [3, 4], [0, 2, 4], [5, 4], []] : Fin 8 → List (Fin 6)), (![[0], [1, 4], [1, 2, 6], [2, 2], [2, 2, 4], [0, 2]] : Fin 6 → List (Fin 8))⟩⟩, ⟨33, 0, ⟨(![[], [0, 2, 3], [4], [3, 5], [], [0, 2, 3], [0, 1, 4], [2, 5]] : Fin 8 → List (Fin 6)), (![[1, 3, 3], [1, 2, 3, 6, 7], [2, 2], [2, 2, 3, 3], [2], [2, 2, 7]] : Fin 6 → List (Fin 8))⟩⟩, ⟨9, 0, ⟨(![[0], [], [0, 4], [5, 1], [0], [], [0, 4], [3, 5]] : Fin 8 → List (Fin 6)), (![[0], [0, 2, 2, 3, 3], [2, 2], [0, 2, 3, 2, 3], [0, 2], [0, 2, 3, 2]] : Fin 6 → List (Fin 8))⟩⟩, ⟨22, 0, ⟨(![[], [0, 2, 3], [4], [3, 5], [], [0, 2, 3], [0, 1, 4], [2, 5]] : Fin 8 → List (Fin 6)), (![[1, 3, 3], [1, 2, 3, 6, 7], [2, 2], [2, 2, 3, 3], [2], [2, 2, 7]] : Fin 6 → List (Fin 8))⟩⟩, ⟨56, 1024, ⟨(![[2, 2, 4], [0, 1, 3, 4], [], [2, 3], [1, 4], [0, 1, 3, 4], [1], [0, 1, 2, 3]] : Fin 8 → List (Fin 5)), (![[3, 3, 6], [6], [0, 1, 3], [0, 3, 1, 3], [4, 6]] : Fin 5 → List (Fin 8))⟩⟩, ⟨51, 1792, ⟨(![[], [0, 2, 2, 3, 4], [1, 2, 4], [2, 2, 4], [], [0, 2, 2, 3, 4], [4, 2], [0, 1, 2, 2, 4]] : Fin 8 → List (Fin 5)), (![[1, 3, 1, 3], [2, 2], [3, 2], [3, 1], [2, 7, 2]] : Fin 5 → List (Fin 8))⟩⟩, ⟨10, 12, ⟨(![[0], [], [5, 4, 5], [0, 4, 5], [0], [], [5, 4, 5], [3, 5, 4]] : Fin 8 → List (Fin 6)), (![[0], [0, 2, 2, 3, 3], [3, 3], [0, 2, 3, 2, 7], [0, 2, 3, 0, 7], [2, 7, 0]] : Fin 6 → List (Fin 8))⟩⟩, ⟨20, 0, ⟨(![[], [0, 2, 3], [0, 1, 4], [3, 5], [], [0, 2, 3], [4], [2, 5]] : Fin 8 → List (Fin 6)), (![[1, 3, 3], [1, 2, 3, 2, 3], [2, 6], [2, 3, 3, 6], [6], [2, 6, 7]] : Fin 6 → List (Fin 8))⟩⟩]
set_option maxHeartbeats 1600000 in
public theorem step_4_1 : Step 4 1 := by
  apply step_of_checks 4 1
    (fun σ => pivot ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩)
    (fun σ => data ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩)
  unfold BranchData.Valid PointValid
  decide +kernel
end Tits.MinimumIndex.LargeTwoOvergroups.SeedCoverage
