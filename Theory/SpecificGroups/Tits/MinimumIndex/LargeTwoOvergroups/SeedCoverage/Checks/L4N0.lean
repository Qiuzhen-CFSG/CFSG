module
public import Theory.SpecificGroups.Tits.MinimumIndex.LargeTwoOvergroups.SeedCoverage.Schreier
public import Mathlib.Data.Fintype.Pi

/-! Kernel-checked binary Schreier words for level 4, node 0.
Source: Parrott (1972), §5; witness discovery in `source/`.
The words certify both containments after conjugation in the marked Sylow group. -/
namespace Tits.MinimumIndex.LargeTwoOvergroups.SeedCoverage
set_option maxRecDepth 20000
private def pivot : Fin 16 → Fin 4 :=
  ![0, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0]
private def data : Fin 16 → BranchData 4 4 :=
  ![⟨6, 780, ⟨(![[], [4, 3, 2], [2], [0, 1, 4], [], [4, 3, 2], [2], [4]] : Fin 8 → List (Fin 5)), (![[1, 2, 1], [1, 1, 2], [2], [2, 3, 1], [7]] : Fin 5 → List (Fin 8))⟩⟩, ⟨6, 780, ⟨(![[], [4, 3, 2], [2], [0, 1, 4], [], [4, 3, 2], [2], [4]] : Fin 8 → List (Fin 5)), (![[1, 2, 1], [1, 1, 2], [2], [2, 3, 1], [7]] : Fin 5 → List (Fin 8))⟩⟩, ⟨13, 1024, ⟨(![[0, 2, 5, 0], [], [2, 3], [0, 3], [0, 2, 5, 0], [0, 4, 5], [0, 1, 2], [1, 2]] : Fin 8 → List (Fin 6)), (![[6, 7], [0, 3, 0], [0, 3, 0, 7], [3, 6, 7], [0, 2, 3, 5], [0, 3, 7]] : Fin 6 → List (Fin 8))⟩⟩, ⟨6, 768, ⟨(![[], [0, 3, 4], [0, 1, 2], [0, 1, 2, 4], [], [0, 3, 4], [0, 1, 2], [2, 4]] : Fin 8 → List (Fin 5)), (![[1, 2, 1], [1, 1, 2], [2, 3, 7], [1, 1, 1, 3], [2, 3]] : Fin 5 → List (Fin 8))⟩⟩, ⟨2, 0, ⟨(![[0], [2], [], [2, 4, 2], [0], [2, 4, 4], [], [2, 4, 2]] : Fin 8 → List (Fin 5)), (![[0], [0, 1, 5], [1], [1, 1, 1, 3, 1, 3], [1, 3, 5]] : Fin 5 → List (Fin 8))⟩⟩, ⟨2, 512, ⟨(![[], [1, 2, 4, 0], [0], [2, 4, 2], [], [1, 2, 4, 0], [0], [1, 3, 4, 0]] : Fin 8 → List (Fin 5)), (![[2], [1, 2, 3, 1, 7], [7, 1], [1, 1, 1, 3, 1, 3], [1, 1, 3]] : Fin 5 → List (Fin 8))⟩⟩, ⟨28, 608, ⟨(![[2, 3, 4, 4], [], [0, 1, 4, 3], [4, 0], [2, 3, 4, 4], [0, 2], [3, 4, 1], [2, 4, 0]] : Fin 8 → List (Fin 5)), (![[3, 7, 5], [0, 2, 7], [3, 7], [3, 0, 7], [7, 5]] : Fin 5 → List (Fin 8))⟩⟩, ⟨28, 96, ⟨(![[], [0, 2, 1], [2, 3, 4, 4], [4, 0], [], [0, 2, 1], [2, 3, 4, 4], [0, 4]] : Fin 8 → List (Fin 5)), (![[1, 1], [1, 1, 3, 1, 7], [1, 1, 1, 3, 1, 3], [1, 1, 1, 2, 3, 1, 3], [1, 1, 7]] : Fin 5 → List (Fin 8))⟩⟩, ⟨0, 0, ⟨(![[0], [2], [0, 3, 4], [], [1, 2, 2], [2, 3], [0, 3, 4], []] : Fin 8 → List (Fin 5)), (![[0], [0, 5, 5], [1], [1, 1, 1, 5], [0, 1, 1, 1, 5, 2]] : Fin 5 → List (Fin 8))⟩⟩, ⟨29, 0, ⟨(![[], [1], [2, 3], [2, 3, 4, 0], [], [1], [2, 3], [0, 2, 3, 4]] : Fin 8 → List (Fin 5)), (![[1, 1, 3, 3], [1], [1, 1, 1, 3, 1, 7], [1, 1, 1, 2, 3, 1, 3], [1, 1, 2, 3]] : Fin 5 → List (Fin 8))⟩⟩, ⟨0, 512, ⟨(![[3, 4], [], [0, 3, 4], [0, 1, 3, 2], [3, 4], [0, 1, 3], [1, 2, 2, 3, 4], [3, 2]] : Fin 8 → List (Fin 5)), (![[0, 2], [0, 2, 3, 3], [5, 3], [3, 3, 5], [0, 3, 3, 5]] : Fin 5 → List (Fin 8))⟩⟩, ⟨29, 96, ⟨(![[], [0, 2, 1], [0, 1, 1, 2, 3], [0, 4], [], [0, 2, 1], [0, 1, 1, 2, 3], [4, 0]] : Fin 8 → List (Fin 5)), (![[1, 1], [1, 1, 3, 1, 3], [1, 1, 1, 3, 1, 7], [1, 1, 1, 2, 3, 1, 7], [1, 1, 3]] : Fin 5 → List (Fin 8))⟩⟩, ⟨2, 96, ⟨(![[0], [1, 3, 2], [], [2, 4, 2], [0], [1, 2, 3], [], [2, 4, 2]] : Fin 8 → List (Fin 5)), (![[0], [0, 1, 1], [0, 1, 1, 3, 5, 3], [1, 1, 1, 3, 1, 3], [1, 3, 1]] : Fin 5 → List (Fin 8))⟩⟩, ⟨28, 0, ⟨(![[], [1], [2, 3], [0, 2, 4, 3], [], [1], [2, 3], [0, 2, 3, 4]] : Fin 8 → List (Fin 5)), (![[1, 1, 3, 3], [1], [1, 1, 1, 3, 1, 7], [1, 1, 1, 2, 3, 1, 3], [1, 1, 2, 3]] : Fin 5 → List (Fin 8))⟩⟩, ⟨28, 512, ⟨(![[2, 3], [], [4, 1, 2], [0, 2, 1], [2, 3], [0, 2], [0, 4, 1], [2, 1]] : Fin 8 → List (Fin 5)), (![[3, 3], [5, 3], [3, 3, 5], [0, 3, 3, 5], [7, 6]] : Fin 5 → List (Fin 8))⟩⟩, ⟨2, 608, ⟨(![[], [2, 3, 4], [0], [2, 4, 0, 2], [], [2, 3, 4], [0], [1, 3, 4]] : Fin 8 → List (Fin 5)), (![[2], [1, 2, 3, 1, 3], [1, 1, 2, 7, 1], [1, 1, 1, 3, 1, 7], [1, 1, 2, 7]] : Fin 5 → List (Fin 8))⟩⟩]
set_option maxHeartbeats 1600000 in
public theorem step_4_0 : Step 4 0 := by
  apply step_of_checks 4 0
    (fun σ => pivot ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩)
    (fun σ => data ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩)
  unfold BranchData.Valid PointValid
  decide +kernel
end Tits.MinimumIndex.LargeTwoOvergroups.SeedCoverage
