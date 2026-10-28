module
public import Theory.SpecificGroups.Tits.MinimumIndex.LargeTwoOvergroups.SeedCoverage.Schreier
public import Mathlib.Data.Fintype.Pi

/-! Kernel-checked binary Schreier words for level 2, node 3.
Source: Parrott (1972), §5; witness discovery in `source/`.
The words certify both containments after conjugation in the marked Sylow group. -/
namespace Tits.MinimumIndex.LargeTwoOvergroups.SeedCoverage
set_option maxRecDepth 20000
private def pivot : Fin 16 → Fin 4 :=
  ![0, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0]
private def data : Fin 16 → BranchData 2 4 :=
  ![⟨18, 0, ⟨(![[], [1], [2], [3], [], [0, 1, 3, 1, 1, 3], [2, 1, 1], [0, 1, 2, 1, 3, 2]] : Fin 8 → List (Fin 4)), (![[1, 1, 1, 7, 1, 3], [1], [2], [3]] : Fin 4 → List (Fin 8))⟩⟩, ⟨18, 0, ⟨(![[], [1], [2], [3], [], [0, 1, 3, 1, 1, 3], [2, 1, 1], [0, 1, 2, 1, 3, 2]] : Fin 8 → List (Fin 4)), (![[1, 1, 1, 7, 1, 3], [1], [2], [3]] : Fin 4 → List (Fin 8))⟩⟩, ⟨8, 12, ⟨(![[0, 2, 1, 2, 2, 2], [], [0, 1, 2, 1, 2, 2], [1, 3, 0, 2, 1], [0, 1, 3, 0, 3], [1, 2, 1, 2, 2, 2], [1, 3, 2, 1, 3], [3, 2]] : Fin 8 → List (Fin 4)), (![[0, 3, 0, 7], [3, 0, 7, 5], [0, 2, 2, 4, 2], [0, 4, 7, 2]] : Fin 4 → List (Fin 8))⟩⟩, ⟨18, 12, ⟨(![[], [0, 1, 1, 3, 1, 3], [3, 1, 2, 0, 3], [1, 3, 2], [], [0, 2, 0, 3, 2, 1, 3], [3, 1, 2, 3], [0, 3, 1, 2, 0]] : Fin 8 → List (Fin 4)), (![[1, 5], [3, 7, 5], [1, 3, 2, 7], [1, 3, 2, 5]] : Fin 4 → List (Fin 8))⟩⟩, ⟨12, 0, ⟨(![[0], [2], [], [3], [0, 1, 1], [1, 1, 3, 2, 3], [0, 3, 1, 0, 2, 3], [0, 3, 1, 0, 2]] : Fin 8 → List (Fin 4)), (![[0], [3, 1, 7], [1], [3]] : Fin 4 → List (Fin 8))⟩⟩, ⟨19, 0, ⟨(![[], [0], [1, 0, 0], [2], [], [1, 2, 1, 0, 2], [1], [1, 0, 0, 2, 1]] : Fin 8 → List (Fin 3)), (![[1], [6], [3]] : Fin 3 → List (Fin 8))⟩⟩, ⟨8, 0, ⟨(![[1], [], [0, 3, 1, 3, 2, 1], [3], [0, 2, 2, 2, 1, 2], [0], [0, 2], [2, 1, 3, 2, 1]] : Fin 8 → List (Fin 4)), (![[5], [0], [5, 6], [3]] : Fin 4 → List (Fin 8))⟩⟩, ⟨18, 768, ⟨(![[], [1], [0, 3, 2, 1, 3], [0, 2, 0, 3], [], [0, 1, 3, 1, 1, 3], [3, 2, 1, 3], [0, 2, 1, 3, 1]] : Fin 8 → List (Fin 4)), (![[2, 2, 6, 2], [1], [2, 5, 2, 2], [2, 1, 7]] : Fin 4 → List (Fin 8))⟩⟩, ⟨15, 0, ⟨(![[0], [1], [2], [], [1, 2, 0, 1, 2, 2, 2], [0, 2, 0, 1, 2, 2, 2], [2, 2, 2], []] : Fin 8 → List (Fin 3)), (![[0], [1], [2]] : Fin 3 → List (Fin 8))⟩⟩, ⟨19, 1, ⟨(![[], [0, 0, 0], [1, 0, 0], [0, 0, 0, 2], [], [0, 0, 1, 2, 1, 0, 2], [1], [2, 0]] : Fin 8 → List (Fin 3)), (![[1, 1, 1], [6], [7, 1]] : Fin 3 → List (Fin 8))⟩⟩, ⟨8, 768, ⟨(![[2, 2, 2, 1, 2], [], [3, 1, 2, 3], [0, 2, 0, 3, 1], [0, 1], [1, 2, 2, 2, 1, 2], [2, 2, 2, 1], [0, 1, 2, 0, 3]] : Fin 8 → List (Fin 4)), (![[0, 4, 5], [0, 5], [2, 2, 6, 0], [2, 0, 7, 0]] : Fin 4 → List (Fin 8))⟩⟩, ⟨19, 768, ⟨(![[], [0], [2, 1, 2, 0], [1, 2, 0, 2, 0, 2], [], [1, 2, 1, 0, 2], [0, 0, 0, 2, 1, 0, 2, 0], [0, 1, 0, 0, 2, 0]] : Fin 8 → List (Fin 3)), (![[1], [1, 3, 6, 3], [2, 5, 3]] : Fin 3 → List (Fin 8))⟩⟩, ⟨12, 12, ⟨(![[1, 0, 1, 1, 1], [3, 2, 3, 0], [], [0, 1, 0, 3, 2], [0, 1, 1], [0, 1, 1, 1, 2, 1], [1, 1, 1, 2], [0, 1, 0, 3, 2]] : Fin 8 → List (Fin 4)), (![[1, 4, 1], [5, 0, 6], [5, 0], [0, 3, 0, 6]] : Fin 4 → List (Fin 8))⟩⟩, ⟨18, 1, ⟨(![[], [1, 1, 1], [2], [1, 1, 1, 3], [], [1, 2, 0, 2, 2, 2], [2, 1, 1], [3, 1]] : Fin 8 → List (Fin 4)), (![[1, 1, 1, 7, 5, 7], [1, 1, 1], [2], [7, 1]] : Fin 4 → List (Fin 8))⟩⟩, ⟨8, 1, ⟨(![[1], [], [2, 0, 3, 1, 3], [1, 3, 0], [0, 2, 2, 2, 1, 2], [0], [2, 1], [0, 3, 1]] : Fin 8 → List (Fin 4)), (![[5], [0], [6, 0], [0, 3, 5]] : Fin 4 → List (Fin 8))⟩⟩, ⟨19, 12, ⟨(![[], [0, 1, 2, 1, 2], [2, 1, 0, 2], [0, 0, 1, 2, 1, 0, 1], [], [0, 0, 0, 2, 0, 2, 0], [0, 0, 1, 0, 1, 1], [0, 0, 0, 1, 2, 1, 1]] : Fin 8 → List (Fin 3)), (![[3, 3, 5], [2, 1, 2, 6], [1, 3, 6, 5]] : Fin 3 → List (Fin 8))⟩⟩]
set_option maxHeartbeats 1600000 in
public theorem step_2_3 : Step 2 3 := by
  apply step_of_checks 2 3
    (fun σ => pivot ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩)
    (fun σ => data ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩)
  unfold BranchData.Valid PointValid
  decide +kernel
end Tits.MinimumIndex.LargeTwoOvergroups.SeedCoverage
