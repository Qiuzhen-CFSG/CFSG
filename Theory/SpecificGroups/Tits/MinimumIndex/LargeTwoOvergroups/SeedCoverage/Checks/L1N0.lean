module
public import Theory.SpecificGroups.Tits.MinimumIndex.LargeTwoOvergroups.SeedCoverage.Schreier
public import Mathlib.Data.Fintype.Pi

/-! Kernel-checked binary Schreier words for level 1, node 0.
Source: Parrott (1972), §5; witness discovery in `source/`.
The words certify both containments after conjugation in the marked Sylow group. -/
namespace Tits.MinimumIndex.LargeTwoOvergroups.SeedCoverage
set_option maxRecDepth 20000
private def pivot : Fin 8 → Fin 3 :=
  ![0, 0, 1, 0, 2, 0, 1, 0]
private def data : Fin 8 → BranchData 1 3 :=
  ![⟨4, 0, ⟨(![[], [1], [2], [], [1, 0], [1, 2, 1, 0]] : Fin 6 → List (Fin 3)), (![[1, 4, 1, 1], [1], [2]] : Fin 3 → List (Fin 6))⟩⟩, ⟨4, 0, ⟨(![[], [1], [2], [], [1, 0], [1, 2, 1, 0]] : Fin 6 → List (Fin 3)), (![[1, 4, 1, 1], [1], [2]] : Fin 3 → List (Fin 6))⟩⟩, ⟨0, 0, ⟨(![[0], [], [3], [1, 2, 2], [0, 2, 3, 0, 3], [3, 1, 2, 0]] : Fin 6 → List (Fin 4)), (![[0], [2, 0, 5, 4], [0, 3, 5, 2], [2]] : Fin 4 → List (Fin 6))⟩⟩, ⟨3, 0, ⟨(![[], [2, 0], [3], [], [2], [0, 3, 1]] : Fin 6 → List (Fin 4)), (![[1, 1, 1, 4], [4, 2, 1, 5], [4], [2]] : Fin 4 → List (Fin 6))⟩⟩, ⟨1, 0, ⟨(![[0], [2], [], [1, 2, 1, 2, 1, 2, 2], [0, 2, 1, 0, 2, 0, 2], []] : Fin 6 → List (Fin 3)), (![[0], [1, 4, 0], [1]] : Fin 3 → List (Fin 6))⟩⟩, ⟨4, 12, ⟨(![[], [2, 1, 2, 0], [1, 1, 0, 1, 2], [], [1, 1, 2, 1, 2, 1, 1], [2, 1, 0]] : Fin 6 → List (Fin 3)), (![[1, 2, 2, 2, 4, 5], [2, 2, 4, 1, 1], [1, 5, 1, 1]] : Fin 3 → List (Fin 6))⟩⟩, ⟨0, 12, ⟨(![[0], [], [0, 1, 2, 0, 3], [1, 2, 2], [0, 3, 0, 2, 3], [1, 2, 0, 3, 0]] : Fin 6 → List (Fin 4)), (![[0], [2, 2, 3, 5, 5], [0, 5, 4, 0, 2], [3, 5, 4]] : Fin 4 → List (Fin 6))⟩⟩, ⟨6, 0, ⟨(![[], [0, 1, 1, 0, 1, 0, 1], [1, 1, 1, 1, 1, 1, 1], [], [0], [1]] : Fin 6 → List (Fin 2)), (![[4], [5]] : Fin 2 → List (Fin 6))⟩⟩]
set_option maxHeartbeats 1600000 in
public theorem step_1_0 : Step 1 0 := by
  apply step_of_checks 1 0
    (fun σ => pivot ⟨signatureIndex σ % 8, Nat.mod_lt _ (by decide)⟩)
    (fun σ => data ⟨signatureIndex σ % 8, Nat.mod_lt _ (by decide)⟩)
  unfold BranchData.Valid PointValid
  decide +kernel
end Tits.MinimumIndex.LargeTwoOvergroups.SeedCoverage
