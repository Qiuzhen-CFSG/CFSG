module
public import Theory.SpecificGroups.Tits.MinimumIndex.LargeTwoOvergroups.SeedCoverage.Schreier
public import Mathlib.Data.Fintype.Pi

/-! Kernel-checked binary Schreier words for level 4, node 4.
Source: Parrott (1972), §5; witness discovery in `source/`.
The words certify both containments after conjugation in the marked Sylow group. -/
namespace Tits.MinimumIndex.LargeTwoOvergroups.SeedCoverage
set_option maxRecDepth 20000
private def pivot : Fin 16 → Fin 4 :=
  ![0, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0]
private def data : Fin 16 → BranchData 4 4 :=
  ![⟨51, 0, ⟨(![[], [2, 3], [1, 2, 2, 4], [0, 2, 2, 4, 3], [], [0, 2, 3], [1, 4], [4, 3]] : Fin 8 → List (Fin 5)), (![[1, 1, 1, 5], [1, 1], [1, 6, 7], [2, 3], [1, 1, 6]] : Fin 5 → List (Fin 8))⟩⟩, ⟨51, 0, ⟨(![[], [2, 3], [1, 2, 2, 4], [0, 2, 2, 4, 3], [], [0, 2, 3], [1, 4], [4, 3]] : Fin 8 → List (Fin 5)), (![[1, 1, 1, 5], [1, 1], [1, 6, 7], [2, 3], [1, 1, 6]] : Fin 5 → List (Fin 8))⟩⟩, ⟨30, 768, ⟨(![[1, 3], [], [0, 3, 5, 0], [1, 5, 4], [0, 3], [0, 1, 2, 3], [2, 5], [1, 5, 4]] : Fin 8 → List (Fin 6)), (![[2, 0, 2], [2, 4, 2], [0, 2, 6, 4], [2, 5, 6], [3, 2, 0], [2, 5]] : Fin 6 → List (Fin 8))⟩⟩, ⟨9, 1804, ⟨(![[], [4, 3, 5], [5, 0], [3, 4, 4], [], [0, 4, 5], [3, 5], [0]] : Fin 8 → List (Fin 6)), (![[7], [1, 5, 3], [1, 1, 2, 6], [1, 1, 3], [6, 1], [2, 7]] : Fin 6 → List (Fin 8))⟩⟩, ⟨32, 1024, ⟨(![[4, 5, 4], [2, 4], [], [1, 3], [0, 1, 5], [0, 1, 2, 4], [0, 1, 2, 3], [1, 2, 3]] : Fin 8 → List (Fin 6)), (![[6, 7], [0, 4, 7], [1, 1], [1, 5, 6], [0, 5, 4], [0, 6]] : Fin 6 → List (Fin 8))⟩⟩, ⟨53, 0, ⟨(![[], [2, 3], [1, 4], [0, 4, 3], [], [0, 2, 3], [0, 3, 4, 3], [0, 1, 3, 4]] : Fin 8 → List (Fin 5)), (![[1, 1, 1, 5], [1, 1], [1, 6, 3], [6, 3], [1, 1, 2]] : Fin 5 → List (Fin 8))⟩⟩, ⟨32, 780, ⟨(![[1, 3], [], [1, 5, 4], [2, 5], [0, 3], [2, 3], [5, 1, 4], [2, 5]] : Fin 8 → List (Fin 6)), (![[2, 2, 4], [0, 2, 2], [2, 2, 5], [2, 2], [0, 6, 3], [0, 3, 4]] : Fin 6 → List (Fin 8))⟩⟩, ⟨47, 0, ⟨(![[], [0, 2, 3], [1, 4], [0, 4, 3], [], [2, 3], [0, 3, 4, 3], [0, 1, 3, 4]] : Fin 8 → List (Fin 5)), (![[1, 1, 1, 5], [1, 5], [1, 2, 7], [6, 3], [1, 5, 2]] : Fin 5 → List (Fin 8))⟩⟩, ⟨9, 0, ⟨(![[0], [0, 4], [3, 5], [], [3, 4, 4], [0, 4], [5, 0], []] : Fin 8 → List (Fin 6)), (![[0], [0, 2, 6], [1, 1], [1, 4, 1], [0, 1], [6, 0]] : Fin 6 → List (Fin 8))⟩⟩, ⟨54, 0, ⟨(![[], [2, 3], [3, 4, 3], [1, 3, 4], [], [0, 2, 3], [1, 4], [0, 4, 3]] : Fin 8 → List (Fin 5)), (![[1, 1, 1, 5], [1, 1], [1, 6, 7], [6, 7], [1, 1, 6]] : Fin 5 → List (Fin 8))⟩⟩, ⟨51, 1804, ⟨(![[0, 2, 2, 3, 4], [], [2, 2, 4], [1, 2], [4, 3], [2, 2], [0, 2, 2, 4], [3, 2, 3]] : Fin 8 → List (Fin 5)), (![[0, 2, 0, 2], [2, 6], [0, 3, 0], [2, 0], [2, 5]] : Fin 5 → List (Fin 8))⟩⟩, ⟨48, 0, ⟨(![[], [0, 2, 3], [3, 4, 3], [1, 3, 4], [], [2, 3], [1, 4], [0, 4, 3]] : Fin 8 → List (Fin 5)), (![[1, 1, 1, 5], [1, 5], [1, 2, 3], [6, 7], [1, 5, 6]] : Fin 5 → List (Fin 8))⟩⟩, ⟨53, 1804, ⟨(![[0, 1, 4, 3], [0, 1, 2], [], [1, 4], [0, 4, 3], [1, 2], [0, 1], [2, 4, 2]] : Fin 8 → List (Fin 5)), (![[0, 4, 6], [0, 4], [1, 6], [4, 3, 6], [0, 4, 3]] : Fin 5 → List (Fin 8))⟩⟩, ⟨50, 0, ⟨(![[], [2, 3], [1, 4], [4, 3], [], [0, 2, 3], [0, 4, 4, 4], [2, 3, 4, 2]] : Fin 8 → List (Fin 5)), (![[1, 1, 1, 5], [1, 1], [1, 6, 3], [2, 7], [1, 1, 2]] : Fin 5 → List (Fin 8))⟩⟩, ⟨47, 1036, ⟨(![[0, 1, 3, 4], [], [0, 3, 4, 2], [0, 3, 2], [0, 1, 4, 3], [0, 1], [0, 2, 3, 4], [1, 3, 2]] : Fin 8 → List (Fin 5)), (![[0, 2, 2, 4], [0, 3, 4, 7], [0, 6], [0, 2, 3], [0, 2, 7, 0]] : Fin 5 → List (Fin 8))⟩⟩, ⟨50, 1804, ⟨(![[], [3, 2, 4], [3], [0, 3, 4], [], [2, 3, 4], [1, 3], [2, 2, 3, 4]] : Fin 8 → List (Fin 5)), (![[2, 2], [1, 1, 2, 2], [1, 1, 1, 3], [2], [2, 3]] : Fin 5 → List (Fin 8))⟩⟩]
set_option maxHeartbeats 1600000 in
public theorem step_4_4 : Step 4 4 := by
  apply step_of_checks 4 4
    (fun σ => pivot ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩)
    (fun σ => data ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩)
  unfold BranchData.Valid PointValid
  decide +kernel
end Tits.MinimumIndex.LargeTwoOvergroups.SeedCoverage
