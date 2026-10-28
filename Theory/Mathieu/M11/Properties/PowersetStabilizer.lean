module

public import Mathlib.GroupTheory.GroupAction.SubMulAction.Combination
public import Theory.Mathieu.M11.Basic

set_option maxHeartbeats 800000
set_option maxRecDepth 100000

namespace Sporadic.Mathieu

open scoped Pointwise in
public theorem m11_mem_powersetCard_stabilizer_of_set_eq
    {n : Nat} (g : M11) (s : Set.powersetCard (Fin 11) n)
    (hset : g • (s : Set (Fin 11)) = (s : Set (Fin 11))) :
    g ∈ MulAction.stabilizer M11 s := by
  rw [MulAction.mem_stabilizer_iff]
  apply Subtype.ext
  apply Finset.ext
  intro x
  have hmemsmul :
      x ∈ g • (s : Finset (Fin 11)) ↔ x ∈ g • (s : Set (Fin 11)) := by
    rw [← Finset.mem_coe, Finset.coe_smul_finset]
    rw [Set.powersetCard.coe_coe]
  have hmemcoe :
      x ∈ ((g • s : Set.powersetCard (Fin 11) n) : Finset (Fin 11)) ↔
        x ∈ g • (s : Finset (Fin 11)) := by
    have hcoe := Set.powersetCard.coe_smul (G := M11) (g := g) (s := s)
    exact Iff.of_eq
      (congrArg (fun u : Finset (Fin 11) => x ∈ u) hcoe)
  exact hmemcoe.trans (hmemsmul.trans (Set.ext_iff.mp hset x))

end Sporadic.Mathieu
