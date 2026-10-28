module
public import Theory.SpecificGroups.Tits.MinimumIndex.LargeTwoOvergroups.SeedCoverage.Schreier
public import Mathlib.Data.Fintype.Pi

/-! Kernel-checked binary Schreier words for level 3, node 8.
Source: Parrott (1972), §5; witness discovery in `source/`.
The words certify both containments after conjugation in the marked Sylow group. -/
namespace Tits.MinimumIndex.LargeTwoOvergroups.SeedCoverage
set_option maxRecDepth 20000
private def pivot : Fin 16 → Fin 4 :=
  ![0, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0]
private def data : Fin 16 → BranchData 3 4 :=
  ![⟨35, 0, ⟨(![[], [0], [1], [2], [], [0], [0, 1, 1, 0, 1, 1, 1], [0, 1, 0, 2, 0, 1, 0]] : Fin 8 → List (Fin 3)), (![[1], [2], [3]] : Fin 3 → List (Fin 8))⟩⟩, ⟨35, 0, ⟨(![[], [0], [1], [2], [], [0], [0, 1, 1, 0, 1, 1, 1], [0, 1, 0, 2, 0, 1, 0]] : Fin 8 → List (Fin 3)), (![[1], [2], [3]] : Fin 3 → List (Fin 8))⟩⟩, ⟨19, 0, ⟨(![[0], [], [3], [4], [0], [], [1, 3], [0, 1, 2, 4]] : Fin 8 → List (Fin 5)), (![[0], [2, 2, 6, 2], [0, 2, 7, 6, 3], [2], [3]] : Fin 5 → List (Fin 8))⟩⟩, ⟨11, 0, ⟨(![[], [0], [1], [2], [], [0], [0, 1, 1, 0, 1, 1, 1], [0, 1, 0, 2, 0, 1, 0]] : Fin 8 → List (Fin 3)), (![[1], [2], [3]] : Fin 3 → List (Fin 8))⟩⟩, ⟨18, 0, ⟨(![[0], [1], [], [4], [4, 0, 4], [1, 2], [0, 3], [0, 3, 4]] : Fin 8 → List (Fin 5)), (![[0], [1], [1, 5], [0, 6], [3]] : Fin 5 → List (Fin 8))⟩⟩, ⟨11, 864, ⟨(![[], [1, 1, 0, 1, 1], [2, 0, 2, 1, 0], [1, 0, 1, 2, 0], [], [1, 1, 0, 1, 1], [0, 1, 2, 0, 2], [0, 2, 1, 0, 1]] : Fin 8 → List (Fin 3)), (![[1, 3, 7], [1, 2, 3, 1, 3], [1, 3, 2, 1, 2]] : Fin 3 → List (Fin 8))⟩⟩, ⟨20, 0, ⟨(![[0], [], [1, 2], [3], [0], [], [2], [2, 1, 3, 2]] : Fin 8 → List (Fin 4)), (![[0], [2, 2, 6, 2], [6], [3]] : Fin 4 → List (Fin 8))⟩⟩, ⟨35, 864, ⟨(![[], [0], [2, 0, 2, 1, 0], [1, 0, 1, 2, 0], [], [0], [0, 1, 2, 0, 2], [0, 2, 1, 0, 1]] : Fin 8 → List (Fin 3)), (![[1], [1, 2, 3, 1, 3], [1, 3, 2, 1, 2]] : Fin 3 → List (Fin 8))⟩⟩, ⟨26, 12, ⟨(![[1], [1, 3, 3, 3, 0, 3], [0, 3, 1, 3, 3], [], [3, 1, 3, 3, 3], [1, 3, 3, 2, 3, 3], [1, 3, 0], []] : Fin 8 → List (Fin 4)), (![[0, 2, 1, 6], [0], [4, 5], [0, 1, 4, 6]] : Fin 4 → List (Fin 8))⟩⟩, ⟨34, 0, ⟨(![[], [0], [1], [1, 2, 1], [], [0], [1, 2, 2], [2]] : Fin 8 → List (Fin 3)), (![[1], [2], [7]] : Fin 3 → List (Fin 8))⟩⟩, ⟨23, 0, ⟨(![[0], [], [1], [2, 2, 2], [0], [], [1, 1, 2, 2, 2, 1, 2], [2]] : Fin 8 → List (Fin 3)), (![[0], [2], [7]] : Fin 3 → List (Fin 8))⟩⟩, ⟨10, 0, ⟨(![[], [0], [1], [1, 2, 1], [], [0], [1, 2, 2], [2]] : Fin 8 → List (Fin 3)), (![[1], [2], [7]] : Fin 3 → List (Fin 8))⟩⟩, ⟨18, 768, ⟨(![[0, 2, 4, 0, 4], [2, 3, 1, 3], [], [2, 4], [2], [0, 1, 2], [0, 1, 2, 4, 1, 4, 3], [2, 4]] : Fin 8 → List (Fin 5)), (![[0, 1, 4, 5], [0, 1], [4], [0, 1, 3, 6, 5, 3], [3, 4]] : Fin 5 → List (Fin 8))⟩⟩, ⟨10, 864, ⟨(![[], [0, 2, 2], [0, 1, 2, 0, 2], [1, 0, 1, 2, 0], [], [0, 2, 2], [2, 0, 2, 1, 0], [0, 2, 1, 0, 1]] : Fin 8 → List (Fin 3)), (![[1, 3, 3], [1, 2, 3, 1, 7], [1, 3, 2, 1, 2]] : Fin 3 → List (Fin 8))⟩⟩, ⟨21, 768, ⟨(![[0, 1, 3, 0, 3], [], [0, 2, 0, 2, 2], [1, 2, 2, 3, 2], [0, 1, 3, 0, 3], [], [0, 2, 2, 2], [1, 2, 3]] : Fin 8 → List (Fin 4)), (![[2, 2, 2, 6], [3, 0, 7], [2, 6, 6], [2, 0, 7]] : Fin 4 → List (Fin 8))⟩⟩, ⟨34, 864, ⟨(![[], [0], [0, 1, 2, 0, 2], [1, 0, 1, 2, 0], [], [0], [2, 0, 2, 1, 0], [0, 2, 1, 0, 1]] : Fin 8 → List (Fin 3)), (![[1], [1, 2, 3, 1, 7], [1, 3, 2, 1, 2]] : Fin 3 → List (Fin 8))⟩⟩]
set_option maxHeartbeats 1600000 in
public theorem step_3_8 : Step 3 8 := by
  apply step_of_checks 3 8
    (fun σ => pivot ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩)
    (fun σ => data ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩)
  unfold BranchData.Valid PointValid
  decide +kernel
end Tits.MinimumIndex.LargeTwoOvergroups.SeedCoverage
