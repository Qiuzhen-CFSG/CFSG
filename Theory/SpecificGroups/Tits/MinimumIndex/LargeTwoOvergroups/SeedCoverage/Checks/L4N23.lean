module
public import Theory.SpecificGroups.Tits.MinimumIndex.LargeTwoOvergroups.SeedCoverage.Schreier
public import Mathlib.Data.Fintype.Pi

/-! Kernel-checked binary Schreier words for level 4, node 23.
Source: Parrott (1972), §5; witness discovery in `source/`.
The words certify both containments after conjugation in the marked Sylow group. -/
namespace Tits.MinimumIndex.LargeTwoOvergroups.SeedCoverage
set_option maxRecDepth 20000
private def pivot : Fin 8 → Fin 3 :=
  ![0, 0, 1, 0, 2, 0, 1, 0]
private def data : Fin 8 → BranchData 4 3 :=
  ![⟨118, 0, ⟨(![[], [3, 2], [1, 4, 3], [], [2, 3], [4, 3]] : Fin 6 → List (Fin 5)), (![[1, 2, 1, 2, 2, 5], [1, 1, 1, 4], [2, 2], [1, 2, 2], [1, 1, 2, 1, 2, 5]] : Fin 5 → List (Fin 6))⟩⟩, ⟨118, 0, ⟨(![[], [3, 2], [1, 4, 3], [], [2, 3], [4, 3]] : Fin 6 → List (Fin 5)), (![[1, 2, 1, 2, 2, 5], [1, 1, 1, 4], [2, 2], [1, 2, 2], [1, 1, 2, 1, 2, 5]] : Fin 5 → List (Fin 6))⟩⟩, ⟨69, 0, ⟨(![[1, 2], [], [3, 4, 5], [1], [2, 3, 4], [0, 5, 1]] : Fin 6 → List (Fin 6)), (![[0, 2, 2, 2, 5, 4], [3], [0, 3], [0, 2, 5, 4], [0, 5, 2], [2, 4]] : Fin 6 → List (Fin 6))⟩⟩, ⟨116, 0, ⟨(![[], [0, 3, 2], [4, 3], [], [0, 2, 3], [1, 4, 3]] : Fin 6 → List (Fin 5)), (![[1, 2, 1, 2, 2, 5], [1, 1, 1, 4], [2, 2], [1, 1, 2, 1, 2], [1, 2, 2, 5]] : Fin 5 → List (Fin 6))⟩⟩, ⟨63, 0, ⟨(![[1, 2], [4, 3], [], [1], [0, 1, 3, 4, 4, 4], [0, 3]] : Fin 6 → List (Fin 5)), (![[0, 1, 4], [3], [0, 3], [0, 1, 4, 5], [0, 1, 1, 5, 4]] : Fin 5 → List (Fin 6))⟩⟩, ⟨116, 864, ⟨(![[], [1, 3], [3, 2, 4], [], [3], [2, 3, 4]] : Fin 6 → List (Fin 5)), (![[1, 2, 1, 2, 2, 5], [1, 1, 1, 4], [2, 5], [4], [1, 1, 1, 2, 2, 5]] : Fin 5 → List (Fin 6))⟩⟩, ⟨69, 768, ⟨(![[0, 1], [], [4, 5, 3], [0, 1, 2], [1, 4], [1, 4, 5, 3]] : Fin 6 → List (Fin 6)), (![[0, 2, 2, 5, 2], [2, 2, 5, 2], [0, 3], [0, 5, 2], [2, 2, 2, 4, 5], [0, 2, 2, 2, 4]] : Fin 6 → List (Fin 6))⟩⟩, ⟨118, 864, ⟨(![[], [0, 3], [3, 2, 4], [], [3, 0], [2, 3, 4]] : Fin 6 → List (Fin 5)), (![[1, 2, 1, 2, 2, 5], [1, 1, 1, 4], [2, 5], [1, 1, 2, 1, 2, 2, 2], [2, 1, 2, 5]] : Fin 5 → List (Fin 6))⟩⟩]
set_option maxHeartbeats 1600000 in
public theorem step_4_23 : Step 4 23 := by
  apply step_of_checks 4 23
    (fun σ => pivot ⟨signatureIndex σ % 8, Nat.mod_lt _ (by decide)⟩)
    (fun σ => data ⟨signatureIndex σ % 8, Nat.mod_lt _ (by decide)⟩)
  unfold BranchData.Valid PointValid
  decide +kernel
end Tits.MinimumIndex.LargeTwoOvergroups.SeedCoverage
