module
public import Theory.SpecificGroups.Tits.MinimumIndex.LargeTwoOvergroups.SeedCoverage.Schreier
public import Mathlib.Data.Fintype.Pi

/-! Kernel-checked binary Schreier words for level 4, node 58.
Source: Parrott (1972), §5; witness discovery in `source/`.
The words certify both containments after conjugation in the marked Sylow group. -/
namespace Tits.MinimumIndex.LargeTwoOvergroups.SeedCoverage
set_option maxRecDepth 20000
private def pivot : Fin 8 → Fin 3 :=
  ![0, 0, 1, 0, 2, 0, 1, 0]
private def data : Fin 8 → BranchData 4 3 :=
  ![⟨112, 12, ⟨(![[], [0, 3, 2, 3, 3], [0, 3, 3, 4], [0, 1], [1, 3, 3, 3], [0, 3, 2, 3, 4]] : Fin 6 → List (Fin 5)), (![[2, 3, 2], [1, 2, 1, 2], [1, 2, 1, 5], [5, 4, 5], [5, 1, 4]] : Fin 5 → List (Fin 6))⟩⟩, ⟨112, 12, ⟨(![[], [0, 3, 2, 3, 3], [0, 3, 3, 4], [0, 1], [1, 3, 3, 3], [0, 3, 2, 3, 4]] : Fin 6 → List (Fin 5)), (![[2, 3, 2], [1, 2, 1, 2], [1, 2, 1, 5], [5, 4, 5], [5, 1, 4]] : Fin 5 → List (Fin 6))⟩⟩, ⟨98, 0, ⟨(![[2, 3, 2], [], [4, 3], [3, 2], [0, 1, 3], [4, 1]] : Fin 6 → List (Fin 5)), (![[3, 3], [0, 4], [0, 0, 3, 0], [0, 2, 4, 5], [3, 2]] : Fin 5 → List (Fin 6))⟩⟩, ⟨100, 0, ⟨(![[], [3], [4, 3, 0], [0, 1], [0, 2, 3], [2, 4, 3]] : Fin 6 → List (Fin 5)), (![[2, 3, 2], [1, 2, 4, 5], [2, 5, 3], [1], [1, 2, 3]] : Fin 5 → List (Fin 6))⟩⟩, ⟨97, 3, ⟨(![[1, 3, 3], [2, 3, 3, 3], [], [0, 3, 1, 3], [0, 1, 3, 1], []] : Fin 6 → List (Fin 4)), (![[3, 3], [0, 1, 1], [3, 0], [0, 3, 4]] : Fin 4 → List (Fin 6))⟩⟩, ⟨120, 768, ⟨(![[], [0, 3, 3, 3], [4], [0], [3, 2, 3, 3], [0, 2, 4]] : Fin 6 → List (Fin 5)), (![[3], [1, 2, 4, 5], [2, 2, 3], [1, 1, 1, 3], [2]] : Fin 5 → List (Fin 6))⟩⟩, ⟨106, 768, ⟨(![[3], [], [0, 4, 2], [0, 3, 2], [0, 1, 2, 3], [0, 2, 4]] : Fin 6 → List (Fin 5)), (![[0, 0], [0, 0, 3, 4], [0, 3], [0], [0, 5, 3]] : Fin 5 → List (Fin 6))⟩⟩, ⟨111, 12, ⟨(![[], [1, 3], [0, 4, 2], [0, 1], [1, 2, 3], [4]] : Fin 6 → List (Fin 5)), (![[2, 3, 5], [1, 5, 1, 5], [2, 2, 3], [3, 1, 3], [5]] : Fin 5 → List (Fin 6))⟩⟩]
set_option maxHeartbeats 1600000 in
public theorem step_4_58 : Step 4 58 := by
  apply step_of_checks 4 58
    (fun σ => pivot ⟨signatureIndex σ % 8, Nat.mod_lt _ (by decide)⟩)
    (fun σ => data ⟨signatureIndex σ % 8, Nat.mod_lt _ (by decide)⟩)
  unfold BranchData.Valid PointValid
  decide +kernel
end Tits.MinimumIndex.LargeTwoOvergroups.SeedCoverage
