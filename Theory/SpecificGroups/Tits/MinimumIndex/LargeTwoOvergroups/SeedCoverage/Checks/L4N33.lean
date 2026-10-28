module
public import Theory.SpecificGroups.Tits.MinimumIndex.LargeTwoOvergroups.SeedCoverage.Schreier
public import Mathlib.Data.Fintype.Pi

/-! Kernel-checked binary Schreier words for level 4, node 33.
Source: Parrott (1972), §5; witness discovery in `source/`.
The words certify both containments after conjugation in the marked Sylow group. -/
namespace Tits.MinimumIndex.LargeTwoOvergroups.SeedCoverage
set_option maxRecDepth 20000
private def pivot : Fin 8 → Fin 3 :=
  ![0, 0, 1, 0, 2, 0, 1, 0]
private def data : Fin 8 → BranchData 4 3 :=
  ![⟨24, 1626, ⟨(![[], [1], [0, 4, 4, 4], [], [1], [4, 1, 4, 4]] : Fin 6 → List (Fin 5)), (![[2, 1, 2, 5, 2], [1], [2, 2, 2, 5], [2, 2, 2, 2], [1, 2, 2, 5]] : Fin 5 → List (Fin 6))⟩⟩, ⟨24, 1626, ⟨(![[], [1], [0, 4, 4, 4], [], [1], [4, 1, 4, 4]] : Fin 6 → List (Fin 5)), (![[2, 1, 2, 5, 2], [1], [2, 2, 2, 5], [2, 2, 2, 2], [1, 2, 2, 5]] : Fin 5 → List (Fin 6))⟩⟩, ⟨24, 96, ⟨(![[0, 2, 3], [], [3, 4, 4, 4], [0, 2, 3], [], [4, 2, 4, 4]] : Fin 6 → List (Fin 5)), (![[0, 2, 2, 5, 2], [2, 0, 2, 2, 2], [2, 2, 2, 5], [2, 2, 2, 2], [2, 5, 5]] : Fin 5 → List (Fin 6))⟩⟩, ⟨62, 0, ⟨(![[], [3], [2, 4, 3, 4, 4], [], [3], [4, 1, 3, 4, 4]] : Fin 6 → List (Fin 5)), (![[1, 2, 1, 2, 5, 5], [2, 2, 2, 5], [2, 2, 2, 2], [1], [1, 2, 5, 5]] : Fin 5 → List (Fin 6))⟩⟩, ⟨15, 0, ⟨(![[0, 2, 3], [0, 2, 3, 4], [], [0, 3], [1, 3, 4], [0, 2, 5]] : Fin 6 → List (Fin 6)), (![[3, 5, 5], [0, 1, 4, 5, 5], [0, 3], [5, 5], [0, 1], [5, 0]] : Fin 6 → List (Fin 6))⟩⟩, ⟨24, 1024, ⟨(![[], [0, 3], [0, 4, 4, 4], [], [0, 3], [4, 1, 4, 4]] : Fin 6 → List (Fin 5)), (![[1, 2, 2, 2, 2], [2, 1, 2, 2, 5], [2, 2, 2, 5], [2, 2, 2, 2], [2, 1, 2, 2]] : Fin 5 → List (Fin 6))⟩⟩, ⟨24, 12, ⟨(![[1, 2, 3], [], [0, 4, 4, 4], [1, 2, 3], [], [4, 1, 4, 4]] : Fin 6 → List (Fin 5)), (![[2, 0, 2, 2, 2], [0, 2, 2, 5, 2], [2, 2, 2, 5], [2, 2, 2, 2], [0, 2, 5, 5]] : Fin 5 → List (Fin 6))⟩⟩, ⟨62, 1, ⟨(![[], [0, 3], [2, 4, 3, 4, 4], [], [0, 3], [4, 1, 3, 4, 4]] : Fin 6 → List (Fin 5)), (![[1, 2, 1, 2, 5, 5], [2, 2, 2, 5], [2, 2, 2, 2], [2, 1, 2, 5, 5], [2, 1, 5, 5]] : Fin 5 → List (Fin 6))⟩⟩]
set_option maxHeartbeats 1600000 in
public theorem step_4_33 : Step 4 33 := by
  apply step_of_checks 4 33
    (fun σ => pivot ⟨signatureIndex σ % 8, Nat.mod_lt _ (by decide)⟩)
    (fun σ => data ⟨signatureIndex σ % 8, Nat.mod_lt _ (by decide)⟩)
  unfold BranchData.Valid PointValid
  decide +kernel
end Tits.MinimumIndex.LargeTwoOvergroups.SeedCoverage
