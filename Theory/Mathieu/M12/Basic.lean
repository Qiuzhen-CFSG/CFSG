module

public import Mathlib.GroupTheory.OrderOfElement
public import Theory.Mathieu.M12.Block

open Theory.GroupTheory

namespace Sporadic.Mathieu

open scoped Pointwise

set_option maxRecDepth 100000

/-- The Mathieu group M12, defined as the full automorphism group of W12. -/
public noncomputable def M12 : Subgroup (Equiv.Perm (Fin 12)) :=
  m12WittDesign.aut

/-- Membership in M12 is exactly preservation of the explicit hexad set. -/
public theorem mem_M12_iff (g : Equiv.Perm (Fin 12)) :
    g ∈ M12 ↔ g • (m12Blocks : Set (Finset (Fin 12))) = m12Blocks := by
  rw [M12, SteinerSystem.mem_aut_iff]
  rfl

/-- M12 is finite as a subgroup of a finite permutation group. -/
public noncomputable instance : Fintype M12 := Fintype.ofFinite _

/-- Every block of W12 has size six. -/
public theorem m12Blocks_card (B : Finset (Fin 12)) (hB : B ∈ m12Blocks) : B.card = 6 :=
  m12Block_card B hB

/-- Every five-set lies in exactly one W12 block. -/
public theorem m12Blocks_unique_block (S : Finset (Fin 12)) (hS : S.card = 5) :
    (m12Blocks.filter (fun B => S ⊆ B)).card = 1 := by
  simpa only [m12WittDesign, SteinerSystem.ofPairwiseIntersection_blocks] using
    m12WittDesign.steiner S hS


/-- The first standard generator belongs to the W12 automorphism group. -/
public theorem m12GeneratorA_mem : m12GeneratorA ∈ M12 := by
  rw [M12, SteinerSystem.mem_aut_iff]
  have h := congrArg (fun s : Finset (Finset (Fin 12)) => (s : Set (Finset (Fin 12))))
    m12GeneratorA_blocks_smul
  simpa only [m12WittDesign, SteinerSystem.ofPairwiseIntersection_blocks,
    Finset.coe_smul_finset] using h

/-- The second standard generator belongs to the W12 automorphism group. -/
public theorem m12GeneratorB_mem : m12GeneratorB ∈ M12 := by
  rw [M12, SteinerSystem.mem_aut_iff]
  have h := congrArg (fun s : Finset (Finset (Fin 12)) => (s : Set (Finset (Fin 12))))
    m12GeneratorB_blocks_smul
  simpa only [m12WittDesign, SteinerSystem.ofPairwiseIntersection_blocks,
    Finset.coe_smul_finset] using h

end Sporadic.Mathieu
