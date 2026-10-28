module
public import Theory.SpecificGroups.Tits.MinimumIndex.LargeTwoOvergroups.SeedCoverage.Schreier
public import Mathlib.Data.Fintype.Pi

/-! Kernel-checked binary Schreier words for level 0, node 0.
Source: Parrott (1972), §5; witness discovery in `source/`.
The words certify both containments after conjugation in the marked Sylow group. -/
namespace Tits.MinimumIndex.LargeTwoOvergroups.SeedCoverage
set_option maxRecDepth 20000
private def pivot : Fin 4 → Fin 2 :=
  ![0, 0, 1, 0]
private def data : Fin 4 → BranchData 0 2 :=
  ![⟨0, 0, ⟨(![[], [2], [0, 2, 0, 2, 0, 2, 1, 2, 1], [1, 0, 2, 1, 1]] : Fin 4 → List (Fin 3)), (![[1, 3, 1, 3, 2, 3, 1, 2, 3, 1, 2], [2, 3, 2, 3, 1, 2, 3], [1]] : Fin 3 → List (Fin 4))⟩⟩, ⟨0, 0, ⟨(![[], [2], [0, 2, 0, 2, 0, 2, 1, 2, 1], [1, 0, 2, 1, 1]] : Fin 4 → List (Fin 3)), (![[1, 3, 1, 3, 2, 3, 1, 2, 3, 1, 2], [2, 3, 2, 3, 1, 2, 3], [1]] : Fin 3 → List (Fin 4))⟩⟩, ⟨2, 0, ⟨(![[0], [], [1, 1, 0, 0, 0, 1, 1, 1, 0], []] : Fin 4 → List (Fin 2)), (![[0], [0, 0, 0, 2, 0, 0, 2, 0, 2, 2, 0, 2, 0]] : Fin 2 → List (Fin 4))⟩⟩, ⟨1, 0, ⟨(![[], [0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1], [1, 1, 0, 1, 1, 1, 1, 1, 1], [1]] : Fin 4 → List (Fin 2)), (![[1, 1, 2, 1, 1, 1, 1, 1, 1], [3]] : Fin 2 → List (Fin 4))⟩⟩]
set_option maxHeartbeats 1600000 in
public theorem step_0_0 : Step 0 0 := by
  apply step_of_checks 0 0
    (fun σ => pivot ⟨signatureIndex σ % 4, Nat.mod_lt _ (by decide)⟩)
    (fun σ => data ⟨signatureIndex σ % 4, Nat.mod_lt _ (by decide)⟩)
  unfold BranchData.Valid PointValid
  decide +kernel
end Tits.MinimumIndex.LargeTwoOvergroups.SeedCoverage
