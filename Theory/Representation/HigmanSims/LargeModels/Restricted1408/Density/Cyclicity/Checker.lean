module

public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Density.Packed
public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Density.OrbitSpan
public import Mathlib.Algebra.BigOperators.Pi

/-!
# Soundness of packed cyclic-span certificates

An orbit recurrence with a smaller predecessor proves membership in every
invariant subspace containing the seed. Packed linear combinations of those
orbit vectors then recover the standard basis. The result supplies exactly
the invariant-subspace premises of the literal row and column cyclicity tests.
No kernel, irreducibility, density, or group-descent hypothesis is used.

The concrete data and ATLAS conventions are documented in `source/README.md`.
-/

public section

namespace Representation.HigmanSims.LargeModels.Restricted1408.Density.Cyclicity

lemma listProduct_mem (W : Submodule (ZMod 2) Vector) (x start : ℕ)
    (rows : List ℕ) (h : ∀ r ∈ rows, vectorOfBits r ∈ W) :
    vectorOfBits (PackedBinaryRows.listProduct x start rows) ∈ W := by
  induction rows generalizing start with
  | nil => simpa only [PackedBinaryRows.listProduct, vectorOfBits_zero] using W.zero_mem
  | cons r rs ih =>
    rw [PackedBinaryRows.listProduct, vectorOfBits_xor]
    refine W.add_mem ?_ (ih (start + 1) (fun y hy => h y (List.mem_cons_of_mem r hy)))
    split
    · exact h r (List.mem_cons_self)
    · simpa only [vectorOfBits_zero] using W.zero_mem

lemma eq_top_of_powers_mem (W : Submodule (ZMod 2) Vector)
    (h : ∀ i : Fin 1408, vectorOfBits (2 ^ i.val) ∈ W) : W = ⊤ := by
  have he (i : Fin 1408) : vectorOfBits (2 ^ i.val) =
      fun j : Fin 1408 => if i = j then (1 : ZMod 2) else 0 := by
    funext j
    simp [vectorOfBits, Thompson.BinaryMatrix.bit, Nat.testBit_two_pow, Fin.ext_iff]
  apply top_unique
  intro x _
  rw [pi_eq_sum_univ x]
  apply W.sum_mem
  intro i _
  exact W.smul_mem (x i) (he i ▸ h i)

/-- A checked packed right inverse is enough to prove a spanning claim. -/
theorem eq_top_of_listProducts (W : Submodule (ZMod 2) Vector) (rows : List ℕ)
    (hrows : ∀ r ∈ rows, vectorOfBits r ∈ W)
    (hspan : ∀ i : Fin 1408, ∃ c : ℕ,
      PackedBinaryRows.listProduct c 0 rows = 2 ^ i.val) : W = ⊤ := by
  apply eq_top_of_powers_mem W
  intro i
  obtain ⟨c, hc⟩ := hspan i
  rw [← hc]
  exact listProduct_mem W c 0 rows hrows

/-- Increasing predecessor indices make orbit membership a strong induction. -/
theorem orbit_mem (W : Submodule (ZMod 2) Vector) (seed : Vector)
    (a b : Vector → Vector) (ha : ∀ x ∈ W, a x ∈ W) (hb : ∀ x ∈ W, b x ∈ W)
    (hs : seed ∈ W) (rows : ℕ → ℕ) (parents : ℕ → ℕ) (choices : ℕ → Bool)
    (hzero : vectorOfBits (rows 0) = seed)
    (hparents : ∀ i, 0 < i → i < 1408 → parents i < i)
    (hstep : ∀ i, 0 < i → i < 1408 →
      vectorOfBits (rows i) =
        if choices i then b (vectorOfBits (rows (parents i)))
        else a (vectorOfBits (rows (parents i)))) :
    ∀ i, i < 1408 → vectorOfBits (rows i) ∈ W := by
  intro i
  induction i using Nat.strong_induction_on with
  | h i ih =>
    intro hi
    by_cases hz : i = 0
    · simpa only [hz, hzero] using hs
    · have hp := hparents i (Nat.pos_of_ne_zero hz) hi
      have hm := ih (parents i) hp (hp.trans hi)
      rw [hstep i (Nat.pos_of_ne_zero hz) hi]
      split
      · exact hb _ hm
      · exact ha _ hm

end Representation.HigmanSims.LargeModels.Restricted1408.Density.Cyclicity
