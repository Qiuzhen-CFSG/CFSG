module

public import Theory.Mathieu.M23.Basic
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.Tactic.FinCases

/-!
# A concrete involution of the derived Witt design

The restriction of the standard M24 2A representative is certified directly
against all 253 heptads of W23. The M23 element is presented explicitly as eight
transpositions, with fixed heptad `{1,2,3,4,5,11,17}`. Every element of its
centralizer preserves that heptad.

This is the representative used for the centralizer calculation in
Aschbacher--Smith, *The Classification of Quasithin Groups*, Lemma 5.2.21,
printed p.657 (PDF p.674). Membership uses a kernel-checked block-reindexing certificate in the actual
derived Witt design.
-/

@[expose] public section

namespace Sporadic.Mathieu.M23Geometry
open scoped Pointwise
set_option maxRecDepth 100000
set_option maxHeartbeats 800000

/-- The eight transpositions, in the established M23 point labels. -/
def involutionPerm : Equiv.Perm (Fin 23) :=
  Equiv.swap (6 : Fin 23) 7 * Equiv.swap 8 0 * Equiv.swap 9 12 *
    Equiv.swap 10 18 * Equiv.swap 13 22 * Equiv.swap 14 20 *
    Equiv.swap 15 19 * Equiv.swap 16 21

private def involutionBlockIndex : Fin 253 → Fin 253 :=
  ![0,2,1,4,3,6,5,8,7,9,10,11,12,16,15,14,13,19,20,17,18,21,22,23,24,26,25,28,27,32,31,30,29,36,35,34,33,38,37,40,39,44,43,42,41,46,45,48,47,51,52,49,50,56,55,54,53,59,58,57,66,67,64,65,62,63,60,61,70,69,68,71,76,75,74,73,72,78,77,80,79,82,81,84,83,85,87,86,88,90,89,91,92,94,93,96,95,97,99,98,100,104,102,103,101,108,107,106,105,111,112,109,110,114,113,124,123,122,121,120,119,118,117,116,115,126,125,130,129,128,127,132,131,134,133,136,135,140,139,138,137,143,144,141,142,145,147,146,148,149,152,151,150,154,153,160,162,161,163,164,155,157,156,158,159,172,171,170,169,168,167,166,165,173,175,174,176,179,178,177,180,182,181,188,192,191,190,189,183,187,186,185,184,198,197,199,200,194,193,195,196,202,201,211,212,208,210,209,205,207,206,203,204,214,213,219,220,218,217,215,216,224,223,222,221,233,234,238,237,235,236,240,239,225,226,229,230,228,227,232,231,247,251,252,250,249,248,241,246,245,244,242,243]

private theorem involutionBlockIndex_involutive :
    Function.Involutive involutionBlockIndex := by
  intro i
  revert i
  decide +kernel

private theorem involutionPerm_block_bits (i : Fin 253) (x : Fin 23) :
    (m23BlockMask i).testBit (involutionPerm.symm x).val =
      (m23BlockMask (involutionBlockIndex i)).testBit x.val := by
  revert i x
  decide +kernel

private theorem involutionPerm_blocks : involutionPerm • m23Blocks = m23Blocks :=
  m23Blocks_smul_of_reindex involutionPerm involutionBlockIndex
    involutionBlockIndex_involutive.surjective
    (fun i => m23Perm_smul_blockAt_of_bits _ _ _ (involutionPerm_block_bits i))

/-- The concrete permutation preserves every heptad of W23. -/
theorem involutionPerm_mem : involutionPerm ∈ M23 := by
  rw [mem_M23_iff]
  have h := congrArg (fun s : Finset (Finset (Fin 23)) => (s : Set (Finset (Fin 23))))
    involutionPerm_blocks
  simpa only [Finset.coe_smul_finset] using h

/-- The representative as an element of the actual design automorphism group. -/
def involutionRepresentative : M23 := ⟨involutionPerm, involutionPerm_mem⟩

theorem involutionRepresentative_coe :
    (involutionRepresentative : Equiv.Perm (Fin 23)) = involutionPerm := rfl

theorem involutionRepresentative_order : orderOf involutionRepresentative = 2 := by
  rw [← Subgroup.orderOf_coe, involutionRepresentative_coe]
  apply orderOf_eq_prime
  · decide +kernel
  · decide +kernel

/-- The seven fixed points of the representative. -/
def involutionHeptad : Finset (Fin 23) := {1, 2, 3, 4, 5, 11, 17}

theorem involutionRepresentative_fixed_iff (x : Fin 23) :
    (involutionRepresentative : Equiv.Perm (Fin 23)) x = x ↔ x ∈ involutionHeptad := by
  rw [involutionRepresentative_coe]
  fin_cases x <;> decide +kernel

theorem involutionHeptad_card : involutionHeptad.card = 7 := by decide +kernel

theorem involutionHeptad_mem : involutionHeptad ∈ m23Blocks := by
  have h : involutionHeptad = m23BlockAt 0 := by decide +kernel
  rw [h, m23Blocks]
  exact Finset.mem_image.mpr ⟨0, Finset.mem_univ _, rfl⟩

theorem centralizer_preserves_involutionHeptad (g : M23)
    (hg : g ∈ Subgroup.centralizer ({involutionRepresentative} : Set M23)) :
    g • involutionHeptad = involutionHeptad := by
  have hc := congrArg M23.subtype (Subgroup.mem_centralizer_singleton_iff.mp hg)
  simp only [map_mul, Subgroup.subtype_apply] at hc
  apply Finset.eq_of_subset_of_card_le
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_smul_finset.mp hx
    apply (involutionRepresentative_fixed_iff _).mp
    have he := congrArg (fun k : Equiv.Perm (Fin 23) => k y) hc
    simp only [Equiv.Perm.mul_apply] at he
    rw [(involutionRepresentative_fixed_iff y).mpr hy] at he
    exact he.symm
  · simp
end Sporadic.Mathieu.M23Geometry
