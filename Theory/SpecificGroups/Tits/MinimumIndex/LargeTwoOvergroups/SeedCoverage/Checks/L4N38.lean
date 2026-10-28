module
public import Theory.SpecificGroups.Tits.MinimumIndex.LargeTwoOvergroups.SeedCoverage.Schreier
public import Mathlib.Data.Fintype.Pi

/-! Kernel-checked binary Schreier words for level 4, node 38.
Source: Parrott (1972), §5; witness discovery in `source/`.
The words certify both containments after conjugation in the marked Sylow group. -/
namespace Tits.MinimumIndex.LargeTwoOvergroups.SeedCoverage
set_option maxRecDepth 20000
private def pivot : Fin 16 → Fin 4 :=
  ![0, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0]
private def data : Fin 16 → BranchData 4 4 :=
  ![⟨94, 0, ⟨(![[], [1, 2], [0, 3], [0, 3, 2, 4], [], [1, 2], [0, 3], [0, 3, 2, 4]] : Fin 8 → List (Fin 5)), (![[1, 1], [1, 1, 3, 1, 3], [1, 3, 1, 3], [1, 1, 2], [3, 2]] : Fin 5 → List (Fin 8))⟩⟩, ⟨94, 0, ⟨(![[], [1, 2], [0, 3], [0, 3, 2, 4], [], [1, 2], [0, 3], [0, 3, 2, 4]] : Fin 8 → List (Fin 5)), (![[1, 1], [1, 1, 3, 1, 3], [1, 3, 1, 3], [1, 1, 2], [3, 2]] : Fin 5 → List (Fin 8))⟩⟩, ⟨64, 0, ⟨(![[0, 1, 2], [], [1, 4], [5, 0, 4], [0, 1, 2], [1], [1, 2, 4], [0, 4, 5]] : Fin 8 → List (Fin 6)), (![[0, 2, 2], [5], [2, 2, 5], [3, 5, 7], [2, 5], [0, 2, 5, 7]] : Fin 6 → List (Fin 8))⟩⟩, ⟨95, 1026, ⟨(![[], [1, 2], [2, 3, 2], [1, 2, 4], [], [1, 2], [2, 3, 2], [1, 2, 4]] : Fin 8 → List (Fin 5)), (![[1, 1], [1, 1, 3, 1, 3], [1, 3, 1, 3], [1, 1, 1, 2, 1], [1, 1, 1, 3]] : Fin 5 → List (Fin 8))⟩⟩, ⟨55, 0, ⟨(![[0, 2, 2], [2, 3], [], [0, 4, 0], [0, 2, 2], [3, 2], [2, 2], [1, 3, 4]] : Fin 8 → List (Fin 5)), (![[0, 6], [1, 1], [1, 3, 7, 6], [3, 7, 6], [6, 3, 6]] : Fin 5 → List (Fin 8))⟩⟩, ⟨95, 0, ⟨(![[], [1, 2], [2, 3, 2], [4, 3], [], [1, 2], [2, 3, 2], [4, 3]] : Fin 8 → List (Fin 5)), (![[1, 1], [1, 1, 3, 1, 3], [1, 3, 1, 3], [1, 1, 1, 2, 1], [1, 2, 3, 1]] : Fin 5 → List (Fin 8))⟩⟩, ⟨70, 0, ⟨(![[0, 1, 2], [], [3, 4], [1, 3, 4, 5], [0, 1, 2], [1], [1, 2, 3, 4], [5, 4]] : Fin 8 → List (Fin 6)), (![[0, 2, 6], [5], [2, 5, 6], [3, 5, 7], [3, 7, 6], [3, 6]] : Fin 6 → List (Fin 8))⟩⟩, ⟨98, 0, ⟨(![[], [0, 2, 1], [2, 3, 2], [4, 3], [], [0, 2, 1], [2, 3, 2], [4, 3]] : Fin 8 → List (Fin 5)), (![[1, 1], [1, 1, 1, 2, 3, 2, 3], [1, 3, 1, 3], [1, 1, 1, 2, 1], [1, 2, 3, 1]] : Fin 5 → List (Fin 8))⟩⟩, ⟨52, 0, ⟨(![[0, 2, 2], [2, 3], [1, 4], [], [0, 2, 2], [1, 2], [4, 3], []] : Fin 8 → List (Fin 5)), (![[0, 2, 2], [1, 1], [1, 1, 5], [1, 5], [1, 1, 2]] : Fin 5 → List (Fin 8))⟩⟩, ⟨98, 2, ⟨(![[], [1, 2], [1, 1, 3], [0, 2, 4, 3], [], [1, 2], [1, 1, 3], [0, 2, 4, 3]] : Fin 8 → List (Fin 5)), (![[1, 1], [1, 1, 3, 1, 3], [1, 3, 1, 3], [1, 2, 1], [1, 1, 1, 2, 1, 3]] : Fin 5 → List (Fin 8))⟩⟩, ⟨64, 1024, ⟨(![[0, 1], [], [4], [5, 0], [0, 1], [1], [2, 4], [3, 5, 0]] : Fin 8 → List (Fin 6)), (![[0, 5], [5], [2, 2, 5], [3, 3], [2], [0, 3, 5]] : Fin 6 → List (Fin 8))⟩⟩, ⟨95, 2, ⟨(![[], [0, 2, 1], [1, 1, 3], [0, 2, 4, 3], [], [0, 2, 1], [1, 1, 3], [0, 2, 4, 3]] : Fin 8 → List (Fin 5)), (![[1, 1], [1, 1, 1, 2, 3, 2, 3], [1, 3, 1, 3], [1, 2, 1], [1, 1, 1, 2, 1, 3]] : Fin 5 → List (Fin 8))⟩⟩, ⟨55, 1024, ⟨(![[0, 1], [1, 2, 3], [], [2, 4, 1], [0, 1], [1, 3, 2], [2, 2], [4, 2]] : Fin 8 → List (Fin 5)), (![[0, 1, 1], [1, 1], [3, 5, 7], [1, 3, 5, 7], [3, 5]] : Fin 5 → List (Fin 8))⟩⟩, ⟨95, 1024, ⟨(![[], [0, 1, 2], [0, 3], [1, 4, 0], [], [0, 1, 2], [0, 3], [1, 4, 0]] : Fin 8 → List (Fin 5)), (![[1, 1], [3, 1, 3], [1, 3, 1, 3], [1, 1, 2], [3, 1]] : Fin 5 → List (Fin 8))⟩⟩, ⟨69, 1, ⟨(![[0, 1, 2], [], [1, 4, 5, 5], [0, 5], [0, 1, 2], [1], [0, 3, 4], [3, 5]] : Fin 8 → List (Fin 6)), (![[0, 2, 6], [5], [2, 5, 6], [0, 3, 5, 3], [3, 3, 6], [0, 3, 5]] : Fin 6 → List (Fin 8))⟩⟩, ⟨94, 2, ⟨(![[], [0, 2, 1], [3], [0, 3, 4, 0], [], [0, 2, 1], [3], [0, 3, 4, 0]] : Fin 8 → List (Fin 5)), (![[1, 1], [1, 1, 1, 2, 3, 2, 3], [1, 3, 1, 3], [2], [1, 1, 2, 3]] : Fin 5 → List (Fin 8))⟩⟩]
set_option maxHeartbeats 1600000 in
public theorem step_4_38 : Step 4 38 := by
  apply step_of_checks 4 38
    (fun σ => pivot ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩)
    (fun σ => data ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩)
  unfold BranchData.Valid PointValid
  decide +kernel
end Tits.MinimumIndex.LargeTwoOvergroups.SeedCoverage
