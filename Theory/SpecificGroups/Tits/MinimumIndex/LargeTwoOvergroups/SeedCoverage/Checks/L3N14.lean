module
public import Theory.SpecificGroups.Tits.MinimumIndex.LargeTwoOvergroups.SeedCoverage.Schreier
public import Mathlib.Data.Fintype.Pi

/-! Kernel-checked binary Schreier words for level 3, node 14.
Source: Parrott (1972), §5; witness discovery in `source/`.
The words certify both containments after conjugation in the marked Sylow group. -/
namespace Tits.MinimumIndex.LargeTwoOvergroups.SeedCoverage
set_option maxRecDepth 20000
private def pivot : Fin 8 → Fin 3 :=
  ![0, 0, 1, 0, 2, 0, 1, 0]
private def data : Fin 8 → BranchData 3 3 :=
  ![⟨24, 0, ⟨(![[], [1], [2], [], [2, 0, 2, 1, 2, 2], [2, 0]] : Fin 6 → List (Fin 3)), (![[2, 2, 5, 2], [1], [2]] : Fin 3 → List (Fin 6))⟩⟩, ⟨24, 0, ⟨(![[], [1], [2], [], [2, 0, 2, 1, 2, 2], [2, 0]] : Fin 6 → List (Fin 3)), (![[2, 2, 5, 2], [1], [2]] : Fin 3 → List (Fin 6))⟩⟩, ⟨33, 0, ⟨(![[0], [], [2], [1, 2, 0, 1, 2, 2, 2], [], [1, 2]] : Fin 6 → List (Fin 3)), (![[0], [2, 2, 5, 2], [2]] : Fin 3 → List (Fin 6))⟩⟩, ⟨57, 96, ⟨(![[], [0, 1, 0, 1, 0, 1, 1], [0, 0, 0, 1, 1, 1], [], [0, 0, 0, 1, 0, 1, 0, 1, 1], [0, 0, 0, 1, 0, 1, 1, 0]] : Fin 6 → List (Fin 2)), (![[2, 1, 2, 2, 5], [2, 2, 1, 2]] : Fin 2 → List (Fin 6))⟩⟩, ⟨27, 0, ⟨(![[0], [2], [], [1, 0, 1], [3], [3, 1]] : Fin 6 → List (Fin 4)), (![[0], [4, 5], [1], [4]] : Fin 4 → List (Fin 6))⟩⟩, ⟨24, 1, ⟨(![[], [0, 1], [2], [], [0, 2, 0, 2, 1, 2, 2], [2, 0]] : Fin 6 → List (Fin 3)), (![[2, 2, 5, 2], [1, 2, 2, 5, 2], [2]] : Fin 3 → List (Fin 6))⟩⟩, ⟨26, 12, ⟨(![[1, 3, 3, 3, 0, 3], [], [0, 1, 3, 3, 3, 2], [3, 3, 0, 3, 3], [], [0, 3, 1, 3, 3]] : Fin 6 → List (Fin 4)), (![[2, 2, 3, 2, 2], [0, 2, 2, 2, 3, 2], [2, 5, 2, 2], [0, 2, 5, 2]] : Fin 4 → List (Fin 6))⟩⟩, ⟨57, 12, ⟨(![[], [1, 1, 1, 0, 1], [0, 0, 1, 0, 1, 1], [], [0, 0, 1, 1, 1, 0, 1], [1, 1, 1, 0]] : Fin 6 → List (Fin 2)), (![[2, 2, 5, 1, 5], [2, 2, 5, 1]] : Fin 2 → List (Fin 6))⟩⟩]
set_option maxHeartbeats 1600000 in
public theorem step_3_14 : Step 3 14 := by
  apply step_of_checks 3 14
    (fun σ => pivot ⟨signatureIndex σ % 8, Nat.mod_lt _ (by decide)⟩)
    (fun σ => data ⟨signatureIndex σ % 8, Nat.mod_lt _ (by decide)⟩)
  unfold BranchData.Valid PointValid
  decide +kernel
end Tits.MinimumIndex.LargeTwoOvergroups.SeedCoverage
