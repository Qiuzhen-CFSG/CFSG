module
public import Theory.SpecificGroups.Tits.MinimumIndex.LargeTwoOvergroups.SeedCoverage.Schreier
public import Mathlib.Data.Fintype.Pi

/-! Kernel-checked binary Schreier words for level 4, node 15.
Source: Parrott (1972), §5; witness discovery in `source/`.
The words certify both containments after conjugation in the marked Sylow group. -/
namespace Tits.MinimumIndex.LargeTwoOvergroups.SeedCoverage
set_option maxRecDepth 20000
private def pivot : Fin 8 → Fin 3 :=
  ![0, 0, 1, 0, 2, 0, 1, 0]
private def data : Fin 8 → BranchData 4 3 :=
  ![⟨86, 0, ⟨(![[], [0, 2, 3], [1, 4], [], [2, 3], [1, 4]] : Fin 6 → List (Fin 5)), (![[1, 1, 1, 4], [1, 4], [2, 1, 2], [1, 1, 1, 2, 4, 2], [1, 4, 2]] : Fin 5 → List (Fin 6))⟩⟩, ⟨86, 0, ⟨(![[], [0, 2, 3], [1, 4], [], [2, 3], [1, 4]] : Fin 6 → List (Fin 5)), (![[1, 1, 1, 4], [1, 4], [2, 1, 2], [1, 1, 1, 2, 4, 2], [1, 4, 2]] : Fin 5 → List (Fin 6))⟩⟩, ⟨4, 1024, ⟨(![[3], [], [1, 2], [1, 2, 3, 4], [5], [0, 2, 4]] : Fin 6 → List (Fin 6)), (![[3, 4, 2, 4], [0, 4, 2, 4, 5], [3, 4, 5, 4], [0], [0, 2, 3], [4]] : Fin 6 → List (Fin 6))⟩⟩, ⟨87, 0, ⟨(![[], [1, 2, 3], [1, 4], [], [2, 1, 3], [1, 4]] : Fin 6 → List (Fin 5)), (![[1, 1, 1, 4], [1, 1], [1, 1, 2, 4, 2], [1, 1, 1, 2, 4, 2], [1, 1, 2]] : Fin 5 → List (Fin 6))⟩⟩, ⟨6, 0, ⟨(![[2], [0, 1, 3, 4], [], [2], [3], []] : Fin 6 → List (Fin 5)), (![[1, 0, 1], [0, 1, 1], [0], [4], [1, 4, 1, 1]] : Fin 5 → List (Fin 6))⟩⟩, ⟨86, 2, ⟨(![[], [2, 3], [0, 4, 1], [], [0, 2, 3], [0, 4, 1]] : Fin 6 → List (Fin 5)), (![[1, 1, 1, 4], [1, 4], [2, 1, 2], [1, 1, 1, 2, 1, 2], [2, 1, 1]] : Fin 5 → List (Fin 6))⟩⟩, ⟨7, 0, ⟨(![[2], [], [5, 1], [0, 1, 2], [1, 2], [2, 5, 4]] : Fin 6 → List (Fin 6)), (![[3, 4], [0, 4], [0], [5, 4, 2], [4, 2, 2], [2, 0, 4]] : Fin 6 → List (Fin 6))⟩⟩, ⟨87, 2, ⟨(![[], [2, 1, 3], [0, 4, 1], [], [1, 2, 3], [0, 4, 1]] : Fin 6 → List (Fin 5)), (![[1, 1, 1, 4], [1, 1], [1, 1, 2, 4, 2], [1, 1, 1, 2, 1, 2], [2, 1, 4]] : Fin 5 → List (Fin 6))⟩⟩]
set_option maxHeartbeats 1600000 in
public theorem step_4_15 : Step 4 15 := by
  apply step_of_checks 4 15
    (fun σ => pivot ⟨signatureIndex σ % 8, Nat.mod_lt _ (by decide)⟩)
    (fun σ => data ⟨signatureIndex σ % 8, Nat.mod_lt _ (by decide)⟩)
  unfold BranchData.Valid PointValid
  decide +kernel
end Tits.MinimumIndex.LargeTwoOvergroups.SeedCoverage
