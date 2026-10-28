module
public import Theory.SpecificGroups.Tits.MinimumIndex.LargeTwoOvergroups.SeedCoverage.Schreier
public import Mathlib.Data.Fintype.Pi

/-! Kernel-checked binary Schreier words for level 4, node 3.
Source: Parrott (1972), §5; witness discovery in `source/`.
The words certify both containments after conjugation in the marked Sylow group. -/
namespace Tits.MinimumIndex.LargeTwoOvergroups.SeedCoverage
set_option maxRecDepth 20000
private def pivot : Fin 8 → Fin 3 :=
  ![0, 0, 1, 0, 2, 0, 1, 0]
private def data : Fin 8 → BranchData 4 3 :=
  ![⟨7, 780, ⟨(![[], [0], [5, 4], [], [0], [2, 5, 4]] : Fin 6 → List (Fin 6)), (![[1], [1, 2, 2, 2, 2], [2, 2, 2, 5], [2, 1, 2, 2, 5], [1, 2, 5], [2, 1, 2, 5]] : Fin 6 → List (Fin 6))⟩⟩, ⟨7, 780, ⟨(![[], [0], [5, 4], [], [0], [2, 5, 4]] : Fin 6 → List (Fin 6)), (![[1], [1, 2, 2, 2, 2], [2, 2, 2, 5], [2, 1, 2, 2, 5], [1, 2, 5], [2, 1, 2, 5]] : Fin 6 → List (Fin 6))⟩⟩, ⟨31, 864, ⟨(![[0, 3], [], [1, 3, 4, 5], [0, 3], [], [1, 5, 4]] : Fin 6 → List (Fin 6)), (![[2, 0, 2, 2, 5], [2, 0, 2, 5, 2], [0, 2, 0, 2, 5, 5], [0, 2, 0, 2, 2, 5], [2, 0, 2], [0, 2, 0, 2, 2]] : Fin 6 → List (Fin 6))⟩⟩, ⟨18, 0, ⟨(![[], [0, 2, 3], [4, 5, 1], [], [0, 2, 3], [0, 2, 4, 5]] : Fin 6 → List (Fin 6)), (![[1, 2, 2, 2, 5], [1, 2, 2, 5, 2], [1, 2, 1, 2, 2, 5], [1, 2, 1, 2, 5, 5], [5, 2], [2, 1, 5, 5]] : Fin 6 → List (Fin 6))⟩⟩, ⟨13, 1024, ⟨(![[0, 2, 5, 0], [1, 2, 4, 5], [], [0, 1, 5], [1, 4, 5], [3, 4, 5]] : Fin 6 → List (Fin 6)), (![[4, 5], [0, 1, 5, 3], [1, 4], [0, 1, 3, 4], [3, 5], [0, 1, 4, 5, 5]] : Fin 6 → List (Fin 6))⟩⟩, ⟨7, 768, ⟨(![[], [0], [1, 5], [], [0], [0, 2, 5]] : Fin 6 → List (Fin 6)), (![[1], [1, 2, 2, 2, 2], [2, 2, 5, 2], [2, 1, 2, 2, 5], [1, 2, 5], [1, 2, 2, 2, 2, 2]] : Fin 6 → List (Fin 6))⟩⟩, ⟨31, 768, ⟨(![[1, 3], [], [5], [1, 3], [], [3, 5, 2]] : Fin 6 → List (Fin 6)), (![[2, 0, 2, 5, 2], [2, 0, 2, 2, 5], [0, 2, 0, 2, 2, 2], [0, 2, 0, 2, 2, 5], [2, 0, 2], [2]] : Fin 6 → List (Fin 6))⟩⟩, ⟨18, 12, ⟨(![[], [1, 2, 3], [2, 3, 5], [], [1, 2, 3], [0, 1, 5]] : Fin 6 → List (Fin 6)), (![[1, 2, 2, 2, 5], [1, 2, 2, 5, 2], [1, 2, 1, 2, 5, 2], [1, 2, 1, 2, 5, 5], [1, 2, 1, 5], [2, 2, 2, 2, 5]] : Fin 6 → List (Fin 6))⟩⟩]
set_option maxHeartbeats 1600000 in
public theorem step_4_3 : Step 4 3 := by
  apply step_of_checks 4 3
    (fun σ => pivot ⟨signatureIndex σ % 8, Nat.mod_lt _ (by decide)⟩)
    (fun σ => data ⟨signatureIndex σ % 8, Nat.mod_lt _ (by decide)⟩)
  unfold BranchData.Valid PointValid
  decide +kernel
end Tits.MinimumIndex.LargeTwoOvergroups.SeedCoverage
