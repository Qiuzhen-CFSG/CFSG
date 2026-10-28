module

public import Mathlib.Algebra.Group.Subgroup.Actions
public import Mathlib.Data.Fin.Basic
public import Mathlib.Data.Fintype.Perm
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.GroupTheory.Perm.List
public import Mathlib.Algebra.Group.End
public import Mathlib.Algebra.Group.Action.End
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Algebra.Group.Pointwise.Finset.Scalar
public import Theory.Mathieu.M24.Block
/-!
# The Mathieu group `M₂₄` as the automorphism group of the Witt design W24

This file follows GLS, Number 3, Part I, Chapter A, Table 5.3e
(printed page 266, PDF page 283), together with the cited Aschbacher/Atlas
construction.  The concrete `S(5, 8, 24)` block set is the 759-element orbit
of `{1,6,8,12,14,17,19,23}` under the ATLAS degree-24 standard generators
from `M24G1-p24B0.g1` and `M24G1-p24B0.g2`.

The group is defined as the full automorphism group of this verified design.
Order and simplicity are intentionally deferred to later phases.
-/
open Theory.GroupTheory

namespace Sporadic.Mathieu

set_option maxRecDepth 100000
set_option maxHeartbeats 800000

private theorem m24BlockCardCheck :
    ∀ B ∈ m24Blocks, B.card = 8 := by
  intro B hB
  rw [m24Blocks] at hB
  rcases Finset.mem_image.mp hB with ⟨i, _, rfl⟩
  exact m24BlockAt_card i

private theorem m24PairwiseIntersectionCheck :
    ∀ B₁ ∈ m24Blocks, ∀ B₂ ∈ m24Blocks,
      B₁ ≠ B₂ → (B₁ ∩ B₂).card < 5 := by
  intro B₁ hB₁ B₂ hB₂ hne
  rw [m24Blocks] at hB₁ hB₂
  rcases Finset.mem_image.mp hB₁ with ⟨i, _, rfl⟩
  rcases Finset.mem_image.mp hB₂ with ⟨j, _, rfl⟩
  apply m24BlockAt_inter i j
  intro hij
  apply hne
  rw [hij]

/-- The concrete Witt `S(5,8,24)` design. -/
public noncomputable def m24WittDesign : SteinerSystem (Fin 24) 5 8 :=
  SteinerSystem.ofPairwiseIntersection m24Blocks
    m24BlockCardCheck
    m24PairwiseIntersectionCheck
    (by
      rw [m24BlocksCardinalityCheck]
      decide +kernel)

/-- The block set of the concrete W24 design is the explicit octad set. -/
public theorem m24WittDesign_blocks : m24WittDesign.blocks = m24Blocks := by
  simp only [m24WittDesign, SteinerSystem.ofPairwiseIntersection_blocks]
/-- The Mathieu group `M₂₄`, defined as the full automorphism group of W24. -/
@[expose] public noncomputable def M24 : Subgroup (Equiv.Perm (Fin 24)) :=
  m24WittDesign.aut
open scoped Pointwise

/-- Membership in `M₂₄` is exactly preservation of the explicit octad set. -/
public theorem mem_M24_iff (g : Equiv.Perm (Fin 24)) :
    g ∈ M24 ↔ g • (m24Blocks : Set (Finset (Fin 24))) = m24Blocks := by
  rw [M24, SteinerSystem.mem_aut_iff]
  rfl

/-- `M₂₄` is finite as a subgroup of a finite permutation group. -/
public noncomputable instance : Fintype M24 := Fintype.ofFinite _


/-- W24 has exactly 759 blocks. -/
public theorem m24Blocks_cardinality : m24Blocks.card = 759 :=
  m24BlocksCardinalityCheck

/-- Every block of W24 has size eight. -/
public theorem m24Blocks_card (B : Finset (Fin 24)) (hB : B ∈ m24Blocks) : B.card = 8 :=
  m24WittDesign.block_card B hB

/-- Every five-set lies in exactly one W24 block. -/
public theorem m24Blocks_unique_block (S : Finset (Fin 24)) (hS : S.card = 5) :
    (m24Blocks.filter (fun B => S ⊆ B)).card = 1 :=
  m24WittDesign.steiner S hS

/-- Every weight-eight word in the certified Golay code is an octad of W24. -/
public theorem m24GolayWord_mem_blocks_of_card_eq_eight
    (u : Fin 4096) (hu : (m24GolayWord u).card = 8) :
    m24GolayWord u ∈ m24Blocks := by
  obtain ⟨S, hS, hScard⟩ :=
    Finset.exists_subset_card_eq (show 5 ≤ (m24GolayWord u).card by omega)
  have hUnique := m24Blocks_unique_block S hScard
  obtain ⟨B, hBsingle⟩ := Finset.card_eq_one.mp hUnique
  have hBfilter : B ∈ m24Blocks.filter (fun C => S ⊆ C) := by
    rw [hBsingle]
    simp
  have hBdata := Finset.mem_filter.mp hBfilter
  have hBmem : B ∈ m24Blocks := hBdata.1
  have hSB : S ⊆ B := hBdata.2
  rw [m24Blocks] at hBmem
  rcases Finset.mem_image.mp hBmem with ⟨i, -, rfl⟩
  have hEq : m24BlockAt i = m24GolayWord u := by
    by_contra hne
    have hmsg : m24BlockMessage i ≠ u := by
      intro h
      apply hne
      rw [m24BlockAt_eq_m24GolayWord i, h]
    have hInter := m24Golay_inter_lt_five (m24BlockMessage i) u
      (by
        rw [← m24BlockAt_eq_m24GolayWord i]
        exact m24BlockAt_card i)
      hu
      (m24Golay_minWeight _
        (m24GolayMessageXor_ne_zero hmsg))
    have hSInter :
        S ⊆ m24GolayWord (m24BlockMessage i) ∩ m24GolayWord u := by
      apply Finset.subset_inter
      · rwa [← m24BlockAt_eq_m24GolayWord i]
      · exact hS
    have hCard : 5 ≤
        (m24GolayWord (m24BlockMessage i) ∩ m24GolayWord u).card := by
      rw [← hScard]
      exact Finset.card_le_card hSInter
    omega
  rw [← hEq, m24Blocks]
  exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩

/-- The first standard generator belongs to the W24 automorphism group. -/
public theorem m24GeneratorA_mem : m24GeneratorA ∈ M24 := by
  rw [M24, SteinerSystem.mem_aut_iff]
  change m24GeneratorA • (m24Blocks : Set (Finset (Fin 24))) = m24Blocks
  have h := congrArg (fun s : Finset (Finset (Fin 24)) => (s : Set (Finset (Fin 24))))
    m24GeneratorA_blocks_smul
  simpa only [Finset.coe_smul_finset] using h

/-- The second standard generator belongs to the W24 automorphism group. -/
public theorem m24GeneratorB_mem : m24GeneratorB ∈ M24 := by
  rw [M24, SteinerSystem.mem_aut_iff]
  change m24GeneratorB • (m24Blocks : Set (Finset (Fin 24))) = m24Blocks
  have h := congrArg (fun s : Finset (Finset (Fin 24)) => (s : Set (Finset (Fin 24))))
    m24GeneratorB_blocks_smul
  simpa only [Finset.coe_smul_finset] using h

end Sporadic.Mathieu
