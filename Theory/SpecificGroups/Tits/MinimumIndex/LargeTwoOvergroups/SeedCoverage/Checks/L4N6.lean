module
public import Theory.SpecificGroups.Tits.MinimumIndex.LargeTwoOvergroups.SeedCoverage.Schreier
public import Mathlib.Data.Fintype.Pi

/-! Kernel-checked binary Schreier words for level 4, node 6.
Source: Parrott (1972), §5; witness discovery in `source/`.
The words certify both containments after conjugation in the marked Sylow group. -/
namespace Tits.MinimumIndex.LargeTwoOvergroups.SeedCoverage
set_option maxRecDepth 20000
private def pivot : Fin 8 → Fin 3 :=
  ![0, 0, 1, 0, 2, 0, 1, 0]
private def data : Fin 8 → BranchData 4 3 :=
  ![⟨65, 0, ⟨(![[], [2, 4], [0, 3, 5, 4], [], [1, 4], [0, 5, 1]] : Fin 6 → List (Fin 6)), (![[2, 1, 4, 2], [1, 5, 4, 5], [1, 2, 1, 2], [4, 2, 5], [1, 1, 2, 1, 2], [2, 5, 2]] : Fin 6 → List (Fin 6))⟩⟩, ⟨65, 0, ⟨(![[], [2, 4], [0, 3, 5, 4], [], [1, 4], [0, 5, 1]] : Fin 6 → List (Fin 6)), (![[2, 1, 4, 2], [1, 5, 4, 5], [1, 2, 1, 2], [4, 2, 5], [1, 1, 2, 1, 2], [2, 5, 2]] : Fin 6 → List (Fin 6))⟩⟩, ⟨35, 1024, ⟨(![[0, 3, 4, 0], [], [0, 5, 2], [0, 1, 4], [0, 1, 2, 3], [1, 3, 5]] : Fin 6 → List (Fin 6)), (![[2, 3, 4, 5], [2, 0, 2, 4], [2, 0, 3, 2], [2, 4, 5], [0, 4], [2, 0]] : Fin 6 → List (Fin 6))⟩⟩, ⟨72, 0, ⟨(![[], [1, 4], [4, 3, 5], [], [2, 4], [0, 5, 1]] : Fin 6 → List (Fin 6)), (![[2, 1, 1, 2], [1, 2, 1, 5], [1, 5, 4, 2], [1, 2, 5], [1, 1, 2, 1, 5], [2, 5, 2]] : Fin 6 → List (Fin 6))⟩⟩, ⟨30, 768, ⟨(![[1, 3], [0, 3, 5, 0], [], [5, 0, 4], [0, 1, 3, 5], []] : Fin 6 → List (Fin 6)), (![[1, 0, 1], [0, 1, 4], [0, 3, 0, 3], [1, 4], [3, 4, 0], [3, 1, 3]] : Fin 6 → List (Fin 6))⟩⟩, ⟨66, 0, ⟨(![[], [2, 4], [0, 5, 1], [], [1, 4], [3, 5, 4]] : Fin 6 → List (Fin 6)), (![[2, 1, 4, 5], [1, 5, 1, 2], [1, 2, 4, 5], [4, 2, 2], [1, 1, 2, 4, 5], [5, 5, 5]] : Fin 6 → List (Fin 6))⟩⟩, ⟨35, 1025, ⟨(![[0, 1, 4], [], [1, 2, 5], [0, 3, 4, 0], [0, 1, 2, 3], [1, 5, 2]] : Fin 6 → List (Fin 6)), (![[2, 0, 2], [2, 3, 4, 5], [0, 2, 2, 3], [2, 2], [3, 4], [2, 0, 4]] : Fin 6 → List (Fin 6))⟩⟩, ⟨72, 2, ⟨(![[], [0, 1, 2, 4], [5, 1, 4], [], [0, 4], [5, 1, 3]] : Fin 6 → List (Fin 6)), (![[2, 1, 1, 5], [1, 2, 4, 2], [1, 5, 1, 5], [1, 2, 2], [2, 4, 2], [2, 1]] : Fin 6 → List (Fin 6))⟩⟩]
set_option maxHeartbeats 1600000 in
public theorem step_4_6 : Step 4 6 := by
  apply step_of_checks 4 6
    (fun σ => pivot ⟨signatureIndex σ % 8, Nat.mod_lt _ (by decide)⟩)
    (fun σ => data ⟨signatureIndex σ % 8, Nat.mod_lt _ (by decide)⟩)
  unfold BranchData.Valid PointValid
  decide +kernel
end Tits.MinimumIndex.LargeTwoOvergroups.SeedCoverage
