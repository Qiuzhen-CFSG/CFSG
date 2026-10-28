module
public import Theory.SpecificGroups.Tits.MinimumIndex.LargeTwoOvergroups.SeedCoverage.Schreier
public import Mathlib.Data.Fintype.Pi

/-! Kernel-checked binary Schreier words for level 4, node 43.
Source: Parrott (1972), §5; witness discovery in `source/`.
The words certify both containments after conjugation in the marked Sylow group. -/
namespace Tits.MinimumIndex.LargeTwoOvergroups.SeedCoverage
set_option maxRecDepth 20000
private def pivot : Fin 8 → Fin 3 :=
  ![0, 0, 1, 0, 2, 0, 1, 0]
private def data : Fin 8 → BranchData 4 3 :=
  ![⟨65, 0, ⟨(![[], [0, 4, 3], [0, 3, 5, 4], [0, 1], [0, 1, 3, 4], [3, 5]] : Fin 6 → List (Fin 6)), (![[1, 4], [1, 3, 4], [1, 1, 3], [1, 2, 5], [1, 5, 2, 4], [1, 2]] : Fin 6 → List (Fin 6))⟩⟩, ⟨65, 0, ⟨(![[], [0, 4, 3], [0, 3, 5, 4], [0, 1], [0, 1, 3, 4], [3, 5]] : Fin 6 → List (Fin 6)), (![[1, 4], [1, 3, 4], [1, 1, 3], [1, 2, 5], [1, 5, 2, 4], [1, 2]] : Fin 6 → List (Fin 6))⟩⟩, ⟨74, 0, ⟨(![[3], [], [0, 5, 3], [1, 2, 3], [0, 1, 2], [4, 3, 5]] : Fin 6 → List (Fin 6)), (![[2, 0, 3, 2], [0, 3, 4], [0, 0, 4], [0], [2, 3, 5, 0], [2, 3]] : Fin 6 → List (Fin 6))⟩⟩, ⟨77, 1026, ⟨(![[], [1, 3], [3, 5], [0, 1, 2], [0, 1, 3], [4, 5, 1]] : Fin 6 → List (Fin 6)), (![[1, 1, 1, 4], [1, 1], [1, 3, 4], [1, 1, 1], [1, 2, 5], [1, 2]] : Fin 6 → List (Fin 6))⟩⟩, ⟨48, 0, ⟨(![[2, 3], [0, 4, 3], [], [3, 2, 4], [1, 3, 4], []] : Fin 6 → List (Fin 5)), (![[1, 3, 4, 3], [0, 1, 0, 1], [3, 4], [1, 0, 3], [1, 0, 4, 3]] : Fin 5 → List (Fin 6))⟩⟩, ⟨66, 1024, ⟨(![[], [0, 4], [1, 5], [0, 1, 2], [0, 1, 2, 4], [4, 3, 5]] : Fin 6 → List (Fin 6)), (![[2, 1, 4, 5], [1, 3, 4], [1, 1, 3], [1, 5, 5], [3, 4], [1, 2, 1]] : Fin 6 → List (Fin 6))⟩⟩, ⟨74, 1, ⟨(![[0, 3], [], [4, 3, 5], [5, 3, 5], [0, 1, 2], [4, 3, 5]] : Fin 6 → List (Fin 6)), (![[2, 0, 3, 2], [0, 3, 4], [0, 0, 4], [3, 4], [0, 2, 3, 2], [2, 0]] : Fin 6 → List (Fin 6))⟩⟩, ⟨77, 1024, ⟨(![[], [0, 1, 3], [1, 5], [0, 1, 2], [1, 3], [5, 4, 3]] : Fin 6 → List (Fin 6)), (![[1, 1, 1, 4], [1, 1], [1, 3, 4], [1, 1, 4], [2, 2, 1], [1, 1, 2]] : Fin 6 → List (Fin 6))⟩⟩]
set_option maxHeartbeats 1600000 in
public theorem step_4_43 : Step 4 43 := by
  apply step_of_checks 4 43
    (fun σ => pivot ⟨signatureIndex σ % 8, Nat.mod_lt _ (by decide)⟩)
    (fun σ => data ⟨signatureIndex σ % 8, Nat.mod_lt _ (by decide)⟩)
  unfold BranchData.Valid PointValid
  decide +kernel
end Tits.MinimumIndex.LargeTwoOvergroups.SeedCoverage
