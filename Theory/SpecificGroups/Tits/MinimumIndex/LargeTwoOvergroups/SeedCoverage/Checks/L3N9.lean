module
public import Theory.SpecificGroups.Tits.MinimumIndex.LargeTwoOvergroups.SeedCoverage.Schreier
public import Mathlib.Data.Fintype.Pi

/-! Kernel-checked binary Schreier words for level 3, node 9.
Source: Parrott (1972), §5; witness discovery in `source/`.
The words certify both containments after conjugation in the marked Sylow group. -/
namespace Tits.MinimumIndex.LargeTwoOvergroups.SeedCoverage
set_option maxRecDepth 20000
private def pivot : Fin 16 → Fin 4 :=
  ![0, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0]
private def data : Fin 16 → BranchData 3 4 :=
  ![⟨43, 0, ⟨(![[], [0], [1], [2], [], [0], [0, 1, 0, 1, 1], [1, 0, 2, 0, 1]] : Fin 8 → List (Fin 3)), (![[1], [2], [3]] : Fin 3 → List (Fin 8))⟩⟩, ⟨43, 0, ⟨(![[], [0], [1], [2], [], [0], [0, 1, 0, 1, 1], [1, 0, 2, 0, 1]] : Fin 8 → List (Fin 3)), (![[1], [2], [3]] : Fin 3 → List (Fin 8))⟩⟩, ⟨7, 1024, ⟨(![[1, 0, 2, 2, 1], [], [0, 1, 0, 1, 1], [1, 0, 1, 1, 2], [1, 0, 2, 2, 1], [2, 2, 2, 2], [1, 1, 1], [2, 1, 0]] : Fin 8 → List (Fin 3)), (![[7, 0, 7], [2, 2, 6], [0, 7, 6]] : Fin 3 → List (Fin 8))⟩⟩, ⟨22, 0, ⟨(![[], [1], [3], [4], [], [1], [3, 4, 0, 4], [0, 2, 4]] : Fin 8 → List (Fin 5)), (![[1, 1, 2, 6], [1], [2, 6, 3, 7], [2], [3]] : Fin 5 → List (Fin 8))⟩⟩, ⟨17, 0, ⟨(![[1], [2], [], [3], [1, 3, 0, 3], [0, 2], [0, 2, 2, 3, 0, 3], [0, 2, 2, 3, 0]] : Fin 8 → List (Fin 4)), (![[1, 1, 1, 5], [0], [1], [3]] : Fin 4 → List (Fin 8))⟩⟩, ⟨41, 0, ⟨(![[], [0], [0, 0, 0, 2, 1, 0, 2], [2], [], [0], [1], [0, 0, 0, 1, 0, 2, 1]] : Fin 8 → List (Fin 3)), (![[1], [6], [3]] : Fin 3 → List (Fin 8))⟩⟩, ⟨5, 1026, ⟨(![[2, 1, 2, 1, 0], [], [0, 1, 2, 0, 1, 2, 1], [0, 1, 0, 2, 0], [2, 1, 2, 1, 0], [0, 1, 1, 2, 0, 1, 2, 1], [0, 1, 1, 2, 0, 1, 2], [1, 1, 2, 0, 1]] : Fin 8 → List (Fin 3)), (![[7, 0, 7], [0, 5, 6, 0], [0, 7, 6]] : Fin 3 → List (Fin 8))⟩⟩, ⟨50, 1024, ⟨(![[], [1, 2, 0, 2], [2, 1, 2], [0, 0, 0, 1, 2], [], [1, 2, 0, 2], [0, 0, 2, 1, 2], [0, 2, 0, 1, 0]] : Fin 8 → List (Fin 3)), (![[6, 1], [3, 7, 2], [1, 2, 2, 7]] : Fin 3 → List (Fin 8))⟩⟩, ⟨25, 12, ⟨(![[0, 2, 3, 2, 3], [1, 1, 1, 2, 0, 2], [2], [], [0, 2, 0, 2, 3], [2, 1, 3, 2], [1, 2, 1], []] : Fin 8 → List (Fin 4)), (![[0, 2, 4, 2, 4], [4, 5], [2], [0, 2, 0, 2, 4]] : Fin 4 → List (Fin 8))⟩⟩, ⟨42, 0, ⟨(![[], [0], [1], [0, 0, 2, 2, 2], [], [0], [0, 1, 0, 1, 1], [2]] : Fin 8 → List (Fin 3)), (![[1], [2], [7]] : Fin 3 → List (Fin 8))⟩⟩, ⟨6, 1024, ⟨(![[2, 0, 2], [], [0, 1, 0, 1, 1], [0, 1, 0, 1, 2, 0], [2, 0, 2], [1, 1, 1, 2, 1, 2], [1, 1, 1], [0, 2, 0, 1, 0, 1]] : Fin 8 → List (Fin 3)), (![[7, 0, 3], [2, 2, 6], [0, 2, 6, 3]] : Fin 3 → List (Fin 8))⟩⟩, ⟨53, 1024, ⟨(![[], [2, 1, 2, 0], [0, 0, 2, 1, 2, 2, 2], [0, 0, 0, 1, 2], [], [2, 1, 2, 0], [1, 2, 2, 2, 2], [2, 0, 2, 2, 1]] : Fin 8 → List (Fin 3)), (![[1, 2, 7, 7], [1, 1, 6], [1, 2, 6, 7]] : Fin 3 → List (Fin 8))⟩⟩, ⟨17, 1, ⟨(![[1], [0, 1, 3, 1, 2, 3], [], [0, 2, 2, 3, 0], [1, 3, 0, 3], [1, 3, 1, 2, 3], [0, 2, 2, 3, 0, 3], [0, 2, 2, 3, 0]] : Fin 8 → List (Fin 4)), (![[1, 1, 1, 5], [0], [5, 6], [3, 6]] : Fin 4 → List (Fin 8))⟩⟩, ⟨41, 1, ⟨(![[], [0, 2, 1, 1, 2], [0, 1, 0], [0, 0, 1, 1, 2, 1], [], [0, 2, 1, 1, 2], [2, 1, 0, 2, 0], [2, 1, 0, 2, 0, 2]] : Fin 8 → List (Fin 3)), (![[2, 1, 6], [1, 2, 1], [3, 6]] : Fin 3 → List (Fin 8))⟩⟩, ⟨5, 1024, ⟨(![[2, 0, 2], [], [0, 1, 1, 2, 0, 1, 2], [1, 0, 2, 0, 1, 0], [2, 0, 2], [0, 1, 1, 2, 0, 1, 2, 1], [0, 1, 2, 0, 1, 2, 1], [1, 2, 1, 0]] : Fin 8 → List (Fin 3)), (![[7, 0, 3], [0, 2, 0, 5], [0, 2, 7, 6]] : Fin 3 → List (Fin 8))⟩⟩, ⟨50, 1026, ⟨(![[], [0, 0, 2, 1, 2, 0], [2, 1, 2], [0, 0, 2, 0, 0, 0], [], [0, 0, 2, 1, 2, 0], [0, 0, 2, 1, 2], [0, 2, 0, 0]] : Fin 8 → List (Fin 3)), (![[1, 1, 1, 2], [7, 7, 6], [1, 3, 6]] : Fin 3 → List (Fin 8))⟩⟩]
set_option maxHeartbeats 1600000 in
public theorem step_3_9 : Step 3 9 := by
  apply step_of_checks 3 9
    (fun σ => pivot ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩)
    (fun σ => data ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩)
  unfold BranchData.Valid PointValid
  decide +kernel
end Tits.MinimumIndex.LargeTwoOvergroups.SeedCoverage
