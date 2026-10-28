module
public import Theory.SpecificGroups.Tits.MinimumIndex.LargeTwoOvergroups.SeedCoverage.Schreier
public import Mathlib.Data.Fintype.Pi

/-! Kernel-checked binary Schreier words for level 2, node 1.
Source: Parrott (1972), §5; witness discovery in `source/`.
The words certify both containments after conjugation in the marked Sylow group. -/
namespace Tits.MinimumIndex.LargeTwoOvergroups.SeedCoverage
set_option maxRecDepth 20000
private def pivot : Fin 8 → Fin 3 :=
  ![0, 0, 1, 0, 2, 0, 1, 0]
private def data : Fin 8 → BranchData 2 3 :=
  ![⟨14, 0, ⟨(![[], [1], [2], [], [0, 2, 0, 2, 2, 2, 1], [2, 0]] : Fin 6 → List (Fin 3)), (![[2, 5, 2, 2], [1], [2]] : Fin 3 → List (Fin 6))⟩⟩, ⟨14, 0, ⟨(![[], [1], [2], [], [0, 2, 0, 2, 2, 2, 1], [2, 0]] : Fin 6 → List (Fin 3)), (![[2, 5, 2, 2], [1], [2]] : Fin 3 → List (Fin 6))⟩⟩, ⟨14, 1036, ⟨(![[0, 2, 1, 2, 2, 0, 2], [], [0, 2, 2, 2, 2, 2], [0, 2, 2, 2, 1, 0, 2], [], [0, 2, 0, 2, 2, 2, 2]] : Fin 6 → List (Fin 3)), (![[2, 5, 2, 2], [2, 3, 5, 5, 2], [2, 2, 2, 5, 2]] : Fin 3 → List (Fin 6))⟩⟩, ⟨16, 0, ⟨(![[], [1, 1, 1], [2], [], [1], [2, 0]] : Fin 6 → List (Fin 3)), (![[2, 5, 2, 2], [4], [2]] : Fin 3 → List (Fin 6))⟩⟩, ⟨2, 0, ⟨(![[0], [3], [], [1, 2, 2], [4], [4, 0, 2]] : Fin 6 → List (Fin 5)), (![[0], [4, 3, 4], [0, 4, 5], [1], [4]] : Fin 5 → List (Fin 6))⟩⟩, ⟨14, 12, ⟨(![[], [2, 0, 2, 2, 1, 0, 2], [0, 2, 1, 2, 2], [], [0, 2, 1, 2, 0, 2, 2], [0, 2, 0, 1, 2, 2]] : Fin 6 → List (Fin 3)), (![[1, 2, 5, 1, 5, 5], [2, 1, 5, 5, 2], [2, 2, 5, 4]] : Fin 3 → List (Fin 6))⟩⟩, ⟨14, 1024, ⟨(![[0, 1, 0], [], [2, 1, 2, 0, 2], [0, 1, 2, 0, 2, 2, 2], [], [0, 2, 1, 2, 2, 0]] : Fin 6 → List (Fin 3)), (![[0, 2, 5, 2, 2, 0], [2, 2, 3, 2, 2], [3, 5, 2, 2]] : Fin 3 → List (Fin 6))⟩⟩, ⟨15, 0, ⟨(![[], [1, 1, 1], [2, 0], [], [1], [2]] : Fin 6 → List (Fin 3)), (![[2, 2, 2, 5], [4], [5]] : Fin 3 → List (Fin 6))⟩⟩]
set_option maxHeartbeats 1600000 in
public theorem step_2_1 : Step 2 1 := by
  apply step_of_checks 2 1
    (fun σ => pivot ⟨signatureIndex σ % 8, Nat.mod_lt _ (by decide)⟩)
    (fun σ => data ⟨signatureIndex σ % 8, Nat.mod_lt _ (by decide)⟩)
  unfold BranchData.Valid PointValid
  decide +kernel
end Tits.MinimumIndex.LargeTwoOvergroups.SeedCoverage
