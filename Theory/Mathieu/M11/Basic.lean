module

public import Mathlib.Algebra.Group.Subgroup.Actions
public import Mathlib.Data.Fin.Basic
public import Mathlib.Data.Fintype.Perm
public import Mathlib.GroupTheory.Perm.List
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Algebra.Group.End
public import Mathlib.Algebra.Group.Action.End
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Algebra.Group.Pointwise.Finset.Scalar
public import Theory.GroupTheory.SteinerSystem
public import Theory.Mathieu.M11.Generators
public import Theory.Mathieu.M11.Block


set_option maxRecDepth 100000
set_option maxHeartbeats 800000


/-!
# The Mathieu group `M₁₁` in its Atlas degree-11 model.

This file follows GLS, Number 3, Part I, Chapter A, Table 5.3a
(printed page 262, PDF page 279).  The table points to Aschbacher,
*Sporadic Groups* [A2, p. 89] for the degree-11 construction.  The
public ATLAS page for the same representation is
`http://brauer.maths.qmul.ac.uk/Atlas/v3/permrep/M11G1-p11B0` and its
GAP generator files are
`http://brauer.maths.qmul.ac.uk/Atlas/spor/M11/gap/M11G1-p11B0.g1` and
`...g2` (retrieved 2026-08-02).

The formal object below is the full automorphism group of the explicitly
verified `S(4, 5, 11)` Steiner system, as required by GLS 5.3a.  The ATLAS
standard generators are retained as concrete automorphisms and computational
witnesses.  The exact order `7920` remains a separate proof obligation.
-/
open Theory.GroupTheory

namespace Sporadic.Mathieu


/-- The 66 blocks of the ATLAS S(4,5,11) model, with points numbered 1--11. -/
private theorem m11DistinctBlocks_inter_card_lt_four
    (B₁ : Finset (Fin 11)) (hB₁ : B₁ ∈ m11Blocks)
    (B₂ : Finset (Fin 11)) (hB₂ : B₂ ∈ m11Blocks)
    (hne : B₁ ≠ B₂) : (B₁ ∩ B₂).card < 4 := by
  rw [m11Blocks] at hB₁ hB₂
  rcases Finset.mem_image.mp hB₁ with ⟨i, -, rfl⟩
  rcases Finset.mem_image.mp hB₂ with ⟨j, -, rfl⟩
  apply m11BlockAt_inter_card_lt_four i j
  intro hij
  apply hne
  simp [hij]
/-- The explicit Witt S(4,5,11) design used for the M11 identification. -/
public noncomputable def m11WittDesign : SteinerSystem (Fin 11) 4 5 :=
  SteinerSystem.ofPairwiseIntersection m11Blocks m11Block_card
    m11DistinctBlocks_inter_card_lt_four (by decide +kernel)

/-- The block field of the explicit Witt design is the listed 66-block system. -/
public theorem m11WittDesign_blocks : m11WittDesign.blocks = m11Blocks := by
  simp only [m11WittDesign, SteinerSystem.ofPairwiseIntersection_blocks]
/-- Every block in the explicit design has size five. -/
public theorem m11Blocks_card (B : Finset (Fin 11)) (hB : B ∈ m11Blocks) : B.card = 5 := by
  exact m11Block_card B hB

/-- Every four-subset of the eleven points lies in exactly one block. -/
public theorem m11Blocks_unique_block (S : Finset (Fin 11)) (hS : S.card = 4) :
    (m11Blocks.filter (fun B => S ⊆ B)).card = 1 := by
  simpa only [m11WittDesign, SteinerSystem.ofPairwiseIntersection_blocks] using
    m11WittDesign.steiner S hS

end Sporadic.Mathieu




namespace Sporadic.Mathieu


open scoped Pointwise

/-- The Mathieu group `M₁₁`, defined as the full automorphism group of W11. -/
@[expose]
public noncomputable def M11 : Subgroup (Equiv.Perm (Fin 11)) :=
  m11WittDesign.aut

open scoped Pointwise

/-- Membership in M11 is exactly preservation of the explicit Witt block set. -/
public theorem mem_M11_iff (g : Equiv.Perm (Fin 11)) :
    g ∈ M11 ↔ g • (m11Blocks : Set (Finset (Fin 11))) = m11Blocks := by
  rw [M11, SteinerSystem.mem_aut_iff]
  simp only [m11WittDesign_blocks]

/-- `M₁₁` is finite as a subgroup of a finite permutation group. -/
public noncomputable instance : Fintype M11 := Fintype.ofFinite _

/-- The first standard generator belongs to the W11 automorphism group. -/
public theorem m11GeneratorA_mem : m11GeneratorA ∈ M11 := by
  rw [M11, SteinerSystem.mem_aut_iff]
  have h := congrArg (fun s : Finset (Finset (Fin 11)) => (s : Set (Finset (Fin 11))))
    m11GeneratorA_blocks_smul
  simpa only [m11WittDesign, SteinerSystem.ofPairwiseIntersection_blocks,
    Finset.coe_smul_finset] using h

/-- The second standard generator belongs to the W11 automorphism group. -/
public theorem m11GeneratorB_mem : m11GeneratorB ∈ M11 := by
  rw [M11, SteinerSystem.mem_aut_iff]
  have h := congrArg (fun s : Finset (Finset (Fin 11)) => (s : Set (Finset (Fin 11))))
    m11GeneratorB_blocks_smul
  simpa only [m11WittDesign, SteinerSystem.ofPairwiseIntersection_blocks,
    Finset.coe_smul_finset] using h
end Sporadic.Mathieu
