module
public import Theory.SpecificGroups.Tits.MinimumIndex.LargeTwoOvergroups.SeedCoverage.Schreier
public import Mathlib.Data.Fintype.Pi

/-! Kernel-checked binary Schreier words for level 4, node 31.
Source: Parrott (1972), §5; witness discovery in `source/`.
The words certify both containments after conjugation in the marked Sylow group. -/
namespace Tits.MinimumIndex.LargeTwoOvergroups.SeedCoverage
set_option maxRecDepth 20000
private def pivot : Fin 16 → Fin 4 :=
  ![0, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0]
private def data : Fin 16 → BranchData 4 4 :=
  ![⟨33, 1024, ⟨(![[], [2, 4], [5], [1, 3], [], [0, 1, 2, 3, 4], [0, 1, 5], [0, 3]] : Fin 8 → List (Fin 6)), (![[2, 3, 2], [2, 3, 6], [1, 1], [1, 1, 2, 2], [1, 1, 1], [2]] : Fin 6 → List (Fin 8))⟩⟩, ⟨33, 1024, ⟨(![[], [2, 4], [5], [1, 3], [], [0, 1, 2, 3, 4], [0, 1, 5], [0, 3]] : Fin 8 → List (Fin 6)), (![[2, 3, 2], [2, 3, 6], [1, 1], [1, 1, 2, 2], [1, 1, 1], [2]] : Fin 6 → List (Fin 8))⟩⟩, ⟨17, 0, ⟨(![[0, 2, 3], [], [2, 5], [4, 5, 0], [1, 2, 3], [2], [2, 3, 5], [4, 5, 0]] : Fin 8 → List (Fin 6)), (![[0, 2, 2], [2, 0, 6], [5], [2, 2, 5], [0, 2, 3], [2, 5]] : Fin 6 → List (Fin 8))⟩⟩, ⟨9, 1792, ⟨(![[], [3, 4], [2, 5, 1], [2, 3], [], [1, 4], [3, 5], [3, 4, 4]] : Fin 8 → List (Fin 6)), (![[1, 3, 5], [1, 5, 3], [1, 1], [1, 1, 3], [1, 1, 1, 7], [1, 1, 3, 6]] : Fin 6 → List (Fin 8))⟩⟩, ⟨21, 12, ⟨(![[1, 2, 3], [1, 4], [], [2, 5], [0, 2], [1, 3, 4], [0, 1, 2, 3], [3, 5]] : Fin 8 → List (Fin 6)), (![[0, 6], [0, 3, 7], [0, 4, 6], [1, 1, 6], [1, 0, 6], [0, 3, 0, 6]] : Fin 6 → List (Fin 8))⟩⟩, ⟨51, 0, ⟨(![[], [2, 3], [0, 4], [0, 2, 2, 4, 3], [], [0, 2, 3], [1, 2, 2, 4], [3, 4]] : Fin 8 → List (Fin 5)), (![[1, 1, 1, 5], [1, 1], [2, 3, 5], [2, 7], [1, 1, 1, 5, 2]] : Fin 5 → List (Fin 8))⟩⟩, ⟨19, 780, ⟨(![[1, 3], [], [2, 5, 4], [2, 5], [0, 3], [2, 3], [5, 4], [2, 5]] : Fin 8 → List (Fin 6)), (![[2, 4, 2], [2, 0, 2], [2, 6], [2, 5, 6], [3, 2], [2, 6, 3]] : Fin 6 → List (Fin 8))⟩⟩, ⟨10, 1792, ⟨(![[], [3, 4], [3, 5, 4], [2, 3], [], [1, 4], [4, 5, 3], [3, 4, 4]] : Fin 8 → List (Fin 6)), (![[1, 3, 5], [1, 5, 3], [1, 1], [1, 1, 3], [1, 1, 1, 7], [5, 6]] : Fin 6 → List (Fin 8))⟩⟩, ⟨22, 0, ⟨(![[0, 2, 3], [4], [2, 5], [], [1, 2], [4], [0, 5, 0], []] : Fin 8 → List (Fin 6)), (![[0, 2, 2], [1, 1, 4], [1, 1], [0, 2, 0, 6], [1], [0, 4, 6]] : Fin 6 → List (Fin 8))⟩⟩, ⟨49, 0, ⟨(![[], [2, 3], [1, 4], [2, 2, 3, 4], [], [0, 2, 3], [0, 2, 2, 4], [0, 4, 3]] : Fin 8 → List (Fin 5)), (![[1, 1, 1, 5], [1, 1], [2, 1, 7], [2, 3], [1, 1, 2]] : Fin 5 → List (Fin 8))⟩⟩, ⟨20, 768, ⟨(![[1, 3], [], [0, 2, 5], [0, 4, 5, 1], [0, 3], [3, 4, 4], [2, 5, 1], [5, 4]] : Fin 8 → List (Fin 6)), (![[3, 4, 7], [3, 0, 7], [0, 2, 0, 6], [2, 2, 5], [0, 3, 2], [0, 2, 5]] : Fin 6 → List (Fin 8))⟩⟩, ⟨50, 12, ⟨(![[], [1, 3, 2], [2, 2, 3, 4], [4], [], [0, 1, 3, 2], [4, 3], [4, 4, 4]] : Fin 8 → List (Fin 5)), (![[1, 1, 1, 5], [1, 1], [1, 2, 7], [3, 2], [3]] : Fin 5 → List (Fin 8))⟩⟩, ⟨61, 1024, ⟨(![[0, 3, 4, 4], [0, 1, 2, 3], [], [0, 1, 4], [3, 4, 4], [1, 3, 2], [0, 2, 2], [0, 2, 2, 4]] : Fin 8 → List (Fin 5)), (![[0, 4], [1, 1], [0, 5, 6], [3, 3, 4], [6, 7]] : Fin 5 → List (Fin 8))⟩⟩, ⟨50, 1024, ⟨(![[], [1, 2, 3], [2, 3, 4, 2], [0, 3], [], [1, 3, 2], [2, 2, 4, 3], [3]] : Fin 8 → List (Fin 5)), (![[3, 3], [1, 1], [1, 1, 1, 3], [7], [1, 2, 5, 7]] : Fin 5 → List (Fin 8))⟩⟩, ⟨57, 1036, ⟨(![[2, 2, 3], [], [0, 2, 4], [0, 3, 2], [1, 3], [0, 1], [3, 4, 2, 3], [1, 3, 2]] : Fin 8 → List (Fin 5)), (![[0, 2, 4, 2], [0, 2, 6, 4], [4, 7], [0, 2, 6], [0, 3, 2]] : Fin 5 → List (Fin 8))⟩⟩, ⟨58, 12, ⟨(![[], [1, 3, 2], [1, 4, 3], [4], [], [0, 1, 3, 2], [0, 3, 4], [2, 4, 2]] : Fin 8 → List (Fin 5)), (![[1, 1, 1, 5], [1, 1], [1, 3, 2], [1, 1, 3, 6], [3]] : Fin 5 → List (Fin 8))⟩⟩]
set_option maxHeartbeats 1600000 in
public theorem step_4_31 : Step 4 31 := by
  apply step_of_checks 4 31
    (fun σ => pivot ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩)
    (fun σ => data ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩)
  unfold BranchData.Valid PointValid
  decide +kernel
end Tits.MinimumIndex.LargeTwoOvergroups.SeedCoverage
