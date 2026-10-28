module
public import Theory.SpecificGroups.Tits.MinimumIndex.LargeTwoOvergroups.SeedCoverage.Schreier
public import Mathlib.Data.Fintype.Pi

/-! Kernel-checked binary Schreier words for level 4, node 25.
Source: Parrott (1972), §5; witness discovery in `source/`.
The words certify both containments after conjugation in the marked Sylow group. -/
namespace Tits.MinimumIndex.LargeTwoOvergroups.SeedCoverage
set_option maxRecDepth 20000
private def pivot : Fin 16 → Fin 4 :=
  ![0, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0]
private def data : Fin 16 → BranchData 4 4 :=
  ![⟨33, 1024, ⟨(![[], [2, 4], [5], [1, 3], [], [2, 4], [0, 3, 5, 0], [1, 2, 3]] : Fin 8 → List (Fin 6)), (![[2, 3, 2], [2, 2, 7], [1, 1], [1, 1, 2, 2], [1, 1, 1], [2]] : Fin 6 → List (Fin 8))⟩⟩, ⟨33, 1024, ⟨(![[], [2, 4], [5], [1, 3], [], [2, 4], [0, 3, 5, 0], [1, 2, 3]] : Fin 8 → List (Fin 6)), (![[2, 3, 2], [2, 2, 7], [1, 1], [1, 1, 2, 2], [1, 1, 1], [2]] : Fin 6 → List (Fin 8))⟩⟩, ⟨30, 0, ⟨(![[0, 2, 3], [], [2, 5], [1, 5, 4], [0, 2, 3], [2], [2, 3, 5], [1, 5, 4]] : Fin 8 → List (Fin 6)), (![[0, 2, 2], [2, 0, 2, 5], [5], [2, 2, 5], [0, 2, 3], [2, 5]] : Fin 6 → List (Fin 8))⟩⟩, ⟨10, 1804, ⟨(![[], [5, 3], [4, 5, 3], [3, 4, 4], [], [5, 3], [0, 4, 5], [1]] : Fin 8 → List (Fin 6)), (![[2, 6, 7], [7], [2, 2], [2, 7, 2], [1, 1, 2, 1], [1, 2, 7, 2]] : Fin 6 → List (Fin 8))⟩⟩, ⟨34, 0, ⟨(![[0, 2, 3], [4], [], [3, 4, 5, 1], [1, 3], [3, 4], [2, 3], [0, 4, 5]] : Fin 8 → List (Fin 6)), (![[0, 6], [0, 3, 7], [1, 1], [1, 1, 6], [1], [0, 5, 7]] : Fin 6 → List (Fin 8))⟩⟩, ⟨53, 0, ⟨(![[], [2, 3], [2, 4, 2], [0, 4, 3], [], [2, 3], [0, 3, 4, 3], [0, 1, 4, 3]] : Fin 8 → List (Fin 5)), (![[2, 3, 6, 7], [1, 1], [1, 6, 3], [6, 3], [3, 2, 7]] : Fin 5 → List (Fin 8))⟩⟩, ⟨8, 780, ⟨(![[0], [], [2, 5, 4], [2, 5], [0], [0, 2, 3], [5, 4], [2, 5]] : Fin 8 → List (Fin 6)), (![[0], [2, 0, 2, 5], [2, 6], [0, 2, 5, 6], [3, 2], [2, 6, 3]] : Fin 6 → List (Fin 8))⟩⟩, ⟨46, 12, ⟨(![[], [0, 1, 3, 2], [0, 1, 3, 4], [1, 4], [], [0, 1, 3, 2], [0, 3, 4], [0, 4]] : Fin 8 → List (Fin 5)), (![[2, 3, 6, 7], [1, 2, 1, 6], [1, 3, 6], [6, 7], [2, 3, 6]] : Fin 5 → List (Fin 8))⟩⟩, ⟨33, 0, ⟨(![[0, 2, 3], [4], [2, 5], [], [0, 3], [4], [0, 1, 3, 5], []] : Fin 8 → List (Fin 6)), (![[0, 2, 2], [2, 4, 2], [0, 4], [0, 2, 2, 4], [1], [0, 4, 2]] : Fin 6 → List (Fin 8))⟩⟩, ⟨52, 0, ⟨(![[], [2, 3], [1, 4], [0, 3, 4], [], [2, 3], [0, 4], [0, 1, 3, 4]] : Fin 8 → List (Fin 5)), (![[2, 3, 6, 7], [1, 1], [1, 6, 7], [6, 7], [1, 1, 2]] : Fin 5 → List (Fin 8))⟩⟩, ⟨10, 780, ⟨(![[0], [], [4, 3, 5], [1, 5], [0], [0, 2, 3], [1, 4, 5], [5, 1]] : Fin 8 → List (Fin 6)), (![[0], [2, 0, 6], [2, 2], [0, 2, 2, 5], [3, 6], [0, 2, 3, 6]] : Fin 6 → List (Fin 8))⟩⟩, ⟨48, 12, ⟨(![[], [0, 1, 3, 2], [0, 1, 4, 3], [2, 2, 4], [], [0, 1, 3, 2], [0, 4, 3], [0, 3, 4, 3]] : Fin 8 → List (Fin 5)), (![[2, 3, 6, 7], [1, 2, 1, 2], [1, 3, 2], [6, 3], [2, 6, 7]] : Fin 5 → List (Fin 8))⟩⟩, ⟨53, 1024, ⟨(![[0, 1, 3, 4], [1, 2, 3], [], [0, 1, 4], [0, 4, 3], [1, 3, 2], [2, 2], [2, 2, 4]] : Fin 8 → List (Fin 5)), (![[0, 4, 6], [1, 1], [1, 4, 3], [0, 7], [6, 7]] : Fin 5 → List (Fin 8))⟩⟩, ⟨58, 0, ⟨(![[], [0, 2, 3], [2, 2, 4], [3, 4], [], [0, 2, 3], [0, 2, 4, 2], [1, 3, 4]] : Fin 8 → List (Fin 5)), (![[2, 3, 2, 3], [1, 1], [1, 7, 2], [7, 2], [3, 6, 3]] : Fin 5 → List (Fin 8))⟩⟩, ⟨46, 1036, ⟨(![[0, 3, 4, 3], [], [2, 4], [0, 3, 2], [0, 3, 4, 3], [0, 1], [0, 4, 2], [1, 3, 2]] : Fin 8 → List (Fin 5)), (![[0, 2, 0, 6], [2, 3, 6, 3], [5, 6, 0], [0, 2, 3], [0, 2, 5, 6]] : Fin 5 → List (Fin 8))⟩⟩, ⟨49, 780, ⟨(![[], [0, 3, 2, 3], [3, 4], [1, 2, 2, 4], [], [0, 3, 2, 3], [2, 4, 3, 2], [1, 4]] : Fin 8 → List (Fin 5)), (![[2, 3, 2, 3], [2, 6], [1, 2, 2], [3, 2], [2, 6, 7]] : Fin 5 → List (Fin 8))⟩⟩]
set_option maxHeartbeats 1600000 in
public theorem step_4_25 : Step 4 25 := by
  apply step_of_checks 4 25
    (fun σ => pivot ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩)
    (fun σ => data ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩)
  unfold BranchData.Valid PointValid
  decide +kernel
end Tits.MinimumIndex.LargeTwoOvergroups.SeedCoverage
