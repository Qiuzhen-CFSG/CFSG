module
public import Theory.SpecificGroups.Tits.MinimumIndex.LargeTwoOvergroups.SeedCoverage.Schreier
public import Mathlib.Data.Fintype.Pi

/-! Kernel-checked binary Schreier words for level 4, node 11.
Source: Parrott (1972), §5; witness discovery in `source/`.
The words certify both containments after conjugation in the marked Sylow group. -/
namespace Tits.MinimumIndex.LargeTwoOvergroups.SeedCoverage
set_option maxRecDepth 20000
private def pivot : Fin 8 → Fin 3 :=
  ![0, 0, 1, 0, 2, 0, 1, 0]
private def data : Fin 8 → BranchData 4 3 :=
  ![⟨117, 0, ⟨(![[], [3, 2], [0, 4, 3], [], [0, 3, 2], [0, 4, 2, 3]] : Fin 6 → List (Fin 5)), (![[1, 1, 4, 1], [1, 1, 4, 4], [1, 5, 1, 2], [2, 5, 1], [4, 5]] : Fin 5 → List (Fin 6))⟩⟩, ⟨117, 0, ⟨(![[], [3, 2], [0, 4, 3], [], [0, 3, 2], [0, 4, 2, 3]] : Fin 6 → List (Fin 5)), (![[1, 1, 4, 1], [1, 1, 4, 4], [1, 5, 1, 2], [2, 5, 1], [4, 5]] : Fin 5 → List (Fin 6))⟩⟩, ⟨44, 864, ⟨(![[1, 2], [], [5, 0], [0], [3, 4], [4, 5]] : Fin 6 → List (Fin 6)), (![[3], [4, 0, 4], [0, 4, 0, 4], [5, 3, 5], [5, 3, 2], [2, 3]] : Fin 6 → List (Fin 6))⟩⟩, ⟨120, 0, ⟨(![[], [0, 3, 2], [2, 4, 3], [], [3, 2], [1, 4, 3]] : Fin 6 → List (Fin 5)), (![[1, 1, 4, 1], [1, 1, 4, 4], [1, 2, 4, 2], [2, 5, 4], [1, 5]] : Fin 5 → List (Fin 6))⟩⟩, ⟨41, 97, ⟨(![[0], [1, 4], [], [1, 3], [4, 1, 4, 4], []] : Fin 6 → List (Fin 5)), (![[0], [0, 1, 0, 4], [0, 1, 0, 3, 4, 3], [4, 3, 1], [0, 1, 0]] : Fin 5 → List (Fin 6))⟩⟩, ⟨116, 864, ⟨(![[], [1, 3], [1, 3, 4], [], [0, 3], [2, 3, 4]] : Fin 6 → List (Fin 5)), (![[1, 1, 1, 4], [1, 1, 4, 4], [1, 5, 4, 5], [1, 1, 1, 4, 4], [2, 4]] : Fin 5 → List (Fin 6))⟩⟩, ⟨42, 97, ⟨(![[0], [], [3, 5], [0, 1], [1, 2, 4], [3, 5]] : Fin 6 → List (Fin 6)), (![[0], [0, 3], [0, 4, 0, 4], [0, 2, 3, 2, 3], [0, 4, 3], [0, 3, 2, 3]] : Fin 6 → List (Fin 6))⟩⟩, ⟨103, 97, ⟨(![[], [3], [0, 1, 2, 4], [], [0, 3], [1, 4]] : Fin 6 → List (Fin 5)), (![[1, 1, 4, 1], [1, 1, 4, 4], [1, 2, 4, 5], [1], [1, 2, 1]] : Fin 5 → List (Fin 6))⟩⟩]
set_option maxHeartbeats 1600000 in
public theorem step_4_11 : Step 4 11 := by
  apply step_of_checks 4 11
    (fun σ => pivot ⟨signatureIndex σ % 8, Nat.mod_lt _ (by decide)⟩)
    (fun σ => data ⟨signatureIndex σ % 8, Nat.mod_lt _ (by decide)⟩)
  unfold BranchData.Valid PointValid
  decide +kernel
end Tits.MinimumIndex.LargeTwoOvergroups.SeedCoverage
