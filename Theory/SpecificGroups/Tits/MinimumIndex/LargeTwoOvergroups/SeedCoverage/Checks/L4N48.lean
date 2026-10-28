module
public import Theory.SpecificGroups.Tits.MinimumIndex.LargeTwoOvergroups.SeedCoverage.Schreier
public import Mathlib.Data.Fintype.Pi

/-! Kernel-checked binary Schreier words for level 4, node 48.
Source: Parrott (1972), §5; witness discovery in `source/`.
The words certify both containments after conjugation in the marked Sylow group. -/
namespace Tits.MinimumIndex.LargeTwoOvergroups.SeedCoverage
set_option maxRecDepth 20000
private def pivot : Fin 4 → Fin 2 :=
  ![0, 0, 1, 0]
private def data : Fin 4 → BranchData 4 2 :=
  ![⟨68, 0, ⟨(![[], [1, 4, 3, 5], [1], [0, 4, 5]] : Fin 4 → List (Fin 6)), (![[1, 1, 1, 1, 2], [2], [1, 1, 2, 3, 3], [1, 1, 3, 1], [1, 1, 2], [1, 1, 3]] : Fin 6 → List (Fin 4))⟩⟩, ⟨68, 0, ⟨(![[], [1, 4, 3, 5], [1], [0, 4, 5]] : Fin 4 → List (Fin 6)), (![[1, 1, 1, 1, 2], [2], [1, 1, 2, 3, 3], [1, 1, 3, 1], [1, 1, 2], [1, 1, 3]] : Fin 6 → List (Fin 4))⟩⟩, ⟨54, 0, ⟨(![[2, 3], [], [0, 1, 2], [1, 4]] : Fin 4 → List (Fin 5)), (![[0, 0, 3, 3], [0, 0], [2, 3, 3], [0, 0, 0, 2, 3, 3], [0, 0, 3]] : Fin 5 → List (Fin 4))⟩⟩, ⟨68, 1024, ⟨(![[], [3, 4, 5], [1], [4, 5, 0]] : Fin 4 → List (Fin 6)), (![[1, 1, 1, 1, 2], [2], [1, 1, 3, 2, 3], [1, 1, 2, 3, 1], [1, 2, 1], [1, 1, 3]] : Fin 6 → List (Fin 4))⟩⟩]
set_option maxHeartbeats 1600000 in
public theorem step_4_48 : Step 4 48 := by
  apply step_of_checks 4 48
    (fun σ => pivot ⟨signatureIndex σ % 4, Nat.mod_lt _ (by decide)⟩)
    (fun σ => data ⟨signatureIndex σ % 4, Nat.mod_lt _ (by decide)⟩)
  unfold BranchData.Valid PointValid
  decide +kernel
end Tits.MinimumIndex.LargeTwoOvergroups.SeedCoverage
