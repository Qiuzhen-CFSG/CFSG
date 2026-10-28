module
public import Theory.SpecificGroups.Tits.MinimumIndex.LargeTwoOvergroups.SeedCoverage.Schreier
public import Mathlib.Data.Fintype.Pi

/-! Kernel-checked binary Schreier words for level 4, node 20.
Source: Parrott (1972), §5; witness discovery in `source/`.
The words certify both containments after conjugation in the marked Sylow group. -/
namespace Tits.MinimumIndex.LargeTwoOvergroups.SeedCoverage
set_option maxRecDepth 20000
private def pivot : Fin 16 → Fin 4 :=
  ![0, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0]
private def data : Fin 16 → BranchData 4 4 :=
  ![⟨115, 0, ⟨(![[], [0, 1], [0, 2, 3], [4, 2, 3], [], [0, 1], [0, 3, 2], [2, 4, 3]] : Fin 8 → List (Fin 5)), (![[1, 3, 7], [3, 7], [1, 2, 3, 2, 7], [2, 2, 3, 2, 3], [1, 2, 2, 3, 2]] : Fin 5 → List (Fin 8))⟩⟩, ⟨115, 0, ⟨(![[], [0, 1], [0, 2, 3], [4, 2, 3], [], [0, 1], [0, 3, 2], [2, 4, 3]] : Fin 8 → List (Fin 5)), (![[1, 3, 7], [3, 7], [1, 2, 3, 2, 7], [2, 2, 3, 2, 3], [1, 2, 2, 3, 2]] : Fin 5 → List (Fin 8))⟩⟩, ⟨99, 0, ⟨(![[0, 1], [], [0, 2, 3], [4, 3, 2], [0, 1], [], [0, 3, 2], [4, 3, 2]] : Fin 8 → List (Fin 5)), (![[3, 0, 3], [0, 3, 0, 3], [0, 2, 3, 6, 3], [2, 2, 3, 2, 3], [0, 2, 2, 3, 2]] : Fin 5 → List (Fin 8))⟩⟩, ⟨92, 0, ⟨(![[], [0], [2, 3], [1, 2, 4, 3], [], [0], [1, 2, 3], [2, 4, 3]] : Fin 8 → List (Fin 5)), (![[1], [3, 7], [2, 3, 2, 3], [2, 2, 3, 2, 3], [2, 2, 3, 6]] : Fin 5 → List (Fin 8))⟩⟩, ⟨70, 0, ⟨(![[1, 2], [0, 1, 2], [], [1, 3, 4, 5], [1], [0, 1], [0, 1, 3, 4], [0, 1, 3, 5]] : Fin 8 → List (Fin 6)), (![[0, 1], [4], [0, 4], [3, 0, 6, 7], [0, 1, 3, 7], [0, 1, 3, 6]] : Fin 6 → List (Fin 8))⟩⟩, ⟨120, 0, ⟨(![[], [0, 1], [2, 3], [2, 4, 3], [], [0, 1], [3, 2], [4, 2, 3]] : Fin 8 → List (Fin 5)), (![[1, 3, 7], [3, 7], [1, 2, 3, 2, 7], [1, 2, 2, 3, 2, 7], [2, 2, 3, 6]] : Fin 5 → List (Fin 8))⟩⟩, ⟨99, 1010, ⟨(![[0], [], [3], [3, 0, 4], [0], [], [1, 3], [3, 0, 4]] : Fin 8 → List (Fin 5)), (![[0], [0, 3, 0, 3], [0, 2, 3, 2, 3], [2], [0, 2, 2, 2, 3]] : Fin 5 → List (Fin 8))⟩⟩, ⟨92, 1010, ⟨(![[], [0], [0, 3], [3, 4], [], [0], [0, 1, 3], [1, 3, 4]] : Fin 8 → List (Fin 5)), (![[1], [3, 7], [2, 3, 2, 7], [1, 2], [1, 2, 2, 2, 3]] : Fin 5 → List (Fin 8))⟩⟩, ⟨63, 1, ⟨(![[1, 2], [0, 1, 2], [0, 4, 3], [], [1], [0, 1, 2], [1, 4, 4, 4], []] : Fin 8 → List (Fin 5)), (![[0, 1], [4], [0, 4], [2, 1, 6], [0, 2, 2, 6]] : Fin 5 → List (Fin 8))⟩⟩, ⟨114, 0, ⟨(![[], [0, 1], [0, 2, 3], [0, 4, 2, 3], [], [0, 1], [0, 3, 2], [0, 2, 4, 3]] : Fin 8 → List (Fin 5)), (![[1, 3, 3], [3, 3], [1, 2, 3, 2, 7], [2, 2, 3, 2, 3], [2, 2, 3, 6]] : Fin 5 → List (Fin 8))⟩⟩, ⟨99, 864, ⟨(![[0], [], [3], [3, 2, 4], [0], [], [1, 3], [3, 2, 4]] : Fin 8 → List (Fin 5)), (![[0], [0, 3, 0, 3], [0, 2, 3, 2, 3], [2], [0, 3, 2]] : Fin 5 → List (Fin 8))⟩⟩, ⟨92, 864, ⟨(![[], [0], [3], [2, 3, 4, 0], [], [0], [1, 3], [0, 2, 3, 4]] : Fin 8 → List (Fin 5)), (![[1], [3, 3], [2, 3, 2, 7], [2], [1, 3, 6]] : Fin 5 → List (Fin 8))⟩⟩, ⟨69, 768, ⟨(![[0, 1], [1], [], [4, 5, 0], [0, 1, 2], [1, 2], [4], [4, 5, 3]] : Fin 8 → List (Fin 6)), (![[0, 1], [1], [0, 4], [0, 1, 3, 3], [6], [0, 3, 1, 6]] : Fin 6 → List (Fin 8))⟩⟩, ⟨121, 0, ⟨(![[], [0, 1], [2, 3], [0, 2, 4, 3], [], [0, 1], [3, 2], [0, 4, 2, 3]] : Fin 8 → List (Fin 5)), (![[1, 3, 3], [3, 3], [1, 2, 3, 2, 7], [1, 2, 2, 3, 2, 7], [1, 2, 2, 3, 2]] : Fin 5 → List (Fin 8))⟩⟩, ⟨99, 2, ⟨(![[0, 1], [], [0, 2, 3], [4, 3, 0], [0, 1], [], [0, 3, 2], [4, 3, 0]] : Fin 8 → List (Fin 5)), (![[3, 0, 3], [0, 3, 0, 3], [0, 2, 3, 6, 3], [2, 2, 3, 2, 3], [0, 2, 3]] : Fin 5 → List (Fin 8))⟩⟩, ⟨92, 2, ⟨(![[], [0], [0, 2, 3], [0, 4, 3], [], [0], [0, 1, 2, 3], [4, 0, 3]] : Fin 8 → List (Fin 5)), (![[1], [3, 3], [2, 3, 2, 3], [1, 2, 2, 3, 2, 3], [2, 3]] : Fin 5 → List (Fin 8))⟩⟩]
set_option maxHeartbeats 1600000 in
public theorem step_4_20 : Step 4 20 := by
  apply step_of_checks 4 20
    (fun σ => pivot ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩)
    (fun σ => data ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩)
  unfold BranchData.Valid PointValid
  decide +kernel
end Tits.MinimumIndex.LargeTwoOvergroups.SeedCoverage
