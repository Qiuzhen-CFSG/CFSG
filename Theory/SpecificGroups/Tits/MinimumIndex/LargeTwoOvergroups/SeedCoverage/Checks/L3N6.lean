module
public import Theory.SpecificGroups.Tits.MinimumIndex.LargeTwoOvergroups.SeedCoverage.Schreier
public import Mathlib.Data.Fintype.Pi

/-! Kernel-checked binary Schreier words for level 3, node 6.
Source: Parrott (1972), §5; witness discovery in `source/`.
The words certify both containments after conjugation in the marked Sylow group. -/
namespace Tits.MinimumIndex.LargeTwoOvergroups.SeedCoverage
set_option maxRecDepth 20000
private def pivot : Fin 8 → Fin 3 :=
  ![0, 0, 1, 0, 2, 0, 1, 0]
private def data : Fin 8 → BranchData 3 3 :=
  ![⟨46, 0, ⟨(![[], [0], [2], [], [0, 0, 0, 1, 1], [0, 2, 1, 0]] : Fin 6 → List (Fin 3)), (![[1], [2, 4, 5, 4], [2]] : Fin 3 → List (Fin 6))⟩⟩, ⟨46, 0, ⟨(![[], [0], [2], [], [0, 0, 0, 1, 1], [0, 2, 1, 0]] : Fin 6 → List (Fin 3)), (![[1], [2, 4, 5, 4], [2]] : Fin 3 → List (Fin 6))⟩⟩, ⟨6, 0, ⟨(![[0], [], [2], [0, 2, 0, 1, 0, 1, 2], [0, 1, 0, 2, 1, 2], [0, 1, 2, 1, 0, 1]] : Fin 6 → List (Fin 3)), (![[0], [3, 2, 3, 5], [2]] : Fin 3 → List (Fin 6))⟩⟩, ⟨43, 0, ⟨(![[], [1, 0, 1], [2], [], [0], [2, 1]] : Fin 6 → List (Fin 3)), (![[4], [2, 5], [2]] : Fin 3 → List (Fin 6))⟩⟩, ⟨4, 0, ⟨(![[0], [1], [], [0, 3, 0], [1, 0, 3, 2], []] : Fin 6 → List (Fin 4)), (![[0], [1], [3, 4, 1, 0], [0, 3, 0]] : Fin 4 → List (Fin 6))⟩⟩, ⟨49, 0, ⟨(![[], [0], [1, 1, 1, 1, 1, 1, 1], [], [0, 1, 0, 0, 1, 1, 1], [1]] : Fin 6 → List (Fin 2)), (![[1], [5]] : Fin 2 → List (Fin 6))⟩⟩, ⟨9, 0, ⟨(![[0], [], [1, 1, 1], [1, 1, 0, 1, 1], [0, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1], [1]] : Fin 6 → List (Fin 2)), (![[0], [5]] : Fin 2 → List (Fin 6))⟩⟩, ⟨45, 0, ⟨(![[], [1, 1, 0, 1, 1], [0, 1, 0, 1, 0, 1, 0], [], [0], [1]] : Fin 6 → List (Fin 2)), (![[4], [5]] : Fin 2 → List (Fin 6))⟩⟩]
set_option maxHeartbeats 1600000 in
public theorem step_3_6 : Step 3 6 := by
  apply step_of_checks 3 6
    (fun σ => pivot ⟨signatureIndex σ % 8, Nat.mod_lt _ (by decide)⟩)
    (fun σ => data ⟨signatureIndex σ % 8, Nat.mod_lt _ (by decide)⟩)
  unfold BranchData.Valid PointValid
  decide +kernel
end Tits.MinimumIndex.LargeTwoOvergroups.SeedCoverage
