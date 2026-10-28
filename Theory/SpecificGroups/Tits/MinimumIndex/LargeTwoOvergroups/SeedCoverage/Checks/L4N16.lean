module
public import Theory.SpecificGroups.Tits.MinimumIndex.LargeTwoOvergroups.SeedCoverage.Schreier
public import Mathlib.Data.Fintype.Pi

/-! Kernel-checked binary Schreier words for level 4, node 16.
Source: Parrott (1972), §5; witness discovery in `source/`.
The words certify both containments after conjugation in the marked Sylow group. -/
namespace Tits.MinimumIndex.LargeTwoOvergroups.SeedCoverage
set_option maxRecDepth 20000
private def pivot : Fin 8 → Fin 3 :=
  ![0, 0, 1, 0, 2, 0, 1, 0]
private def data : Fin 8 → BranchData 4 3 :=
  ![⟨84, 0, ⟨(![[], [3, 4, 1], [0, 1, 4, 2], [], [4, 1, 3], [0, 1, 4, 2]] : Fin 6 → List (Fin 5)), (![[1, 1, 1, 1], [2, 1, 2, 4], [4, 2], [1, 2, 2, 1], [2, 4, 2]] : Fin 5 → List (Fin 6))⟩⟩, ⟨84, 0, ⟨(![[], [3, 4, 1], [0, 1, 4, 2], [], [4, 1, 3], [0, 1, 4, 2]] : Fin 6 → List (Fin 5)), (![[1, 1, 1, 1], [2, 1, 2, 4], [4, 2], [1, 2, 2, 1], [2, 4, 2]] : Fin 5 → List (Fin 6))⟩⟩, ⟨46, 1024, ⟨(![[1], [], [0, 1, 2, 3], [0, 2, 2], [0, 4, 3], [0, 3, 2, 3]] : Fin 6 → List (Fin 5)), (![[0, 2, 2], [0], [0, 2, 5, 2], [0, 2, 2, 5, 2], [2, 5, 4]] : Fin 5 → List (Fin 6))⟩⟩, ⟨85, 2, ⟨(![[], [3, 1, 4], [4, 2], [], [1, 3, 4], [4, 2]] : Fin 6 → List (Fin 5)), (![[1, 1, 1, 1], [2, 1, 2, 1], [2, 1, 1, 1], [1, 1, 2, 2], [2, 2, 2, 1, 2]] : Fin 5 → List (Fin 6))⟩⟩, ⟨31, 864, ⟨(![[2, 3], [1, 3, 4, 5], [], [2, 3], [5, 1], [0, 1, 2]] : Fin 6 → List (Fin 6)), (![[1, 4, 5], [4, 1], [1, 4, 4, 1], [0, 1, 4, 4, 1], [0, 1, 1, 4, 1], [4, 4, 1]] : Fin 6 → List (Fin 6))⟩⟩, ⟨85, 0, ⟨(![[], [3, 4, 1], [1, 3, 2, 4], [], [4, 1, 3], [1, 3, 2, 4]] : Fin 6 → List (Fin 5)), (![[1, 1, 1, 1], [2, 1, 2, 1], [2, 1, 1, 4], [1, 2, 2, 1], [2, 1, 2]] : Fin 5 → List (Fin 6))⟩⟩, ⟨29, 768, ⟨(![[0, 1, 1, 2, 3], [], [0, 2, 1], [2, 3], [0, 4], [2, 1, 2]] : Fin 6 → List (Fin 5)), (![[2, 2], [0, 3, 5], [2, 5], [0, 5, 2], [2, 2, 4]] : Fin 5 → List (Fin 6))⟩⟩, ⟨84, 2, ⟨(![[], [3, 1, 4], [4, 2, 1], [], [1, 3, 4], [4, 2, 1]] : Fin 6 → List (Fin 5)), (![[1, 1, 1, 1], [2, 1, 2, 4], [1, 2], [1, 1, 2, 2], [2, 1, 2, 2, 2]] : Fin 5 → List (Fin 6))⟩⟩]
set_option maxHeartbeats 1600000 in
public theorem step_4_16 : Step 4 16 := by
  apply step_of_checks 4 16
    (fun σ => pivot ⟨signatureIndex σ % 8, Nat.mod_lt _ (by decide)⟩)
    (fun σ => data ⟨signatureIndex σ % 8, Nat.mod_lt _ (by decide)⟩)
  unfold BranchData.Valid PointValid
  decide +kernel
end Tits.MinimumIndex.LargeTwoOvergroups.SeedCoverage
