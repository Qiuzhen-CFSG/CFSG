module

public import Theory.GroupTheory.PCoreImage
public import Mathlib.GroupTheory.Commutator.Basic

/-!
# Displacements of a normalized two-by-three group

If B normalizes Y, its intersection with the embedded two-core of Y
is a normal two-subgroup of B, hence lies in the embedded two-core of B.
If Y/O₂(Y) is a three-group, every element of Y ∩ B consequently has
three-power order modulo O₂(B). Mutual normalization applies this to all
commutators of Y with B.

This is the ambient-group input to the Borel-action argument in
Aschbacher--Smith, proof of 15.3.37, printed p.1135. The argument uses
relative normality in B and makes no assertion about ambient normality.
-/

@[expose] public section

namespace Subgroup
open scoped commutatorElement
variable {G : Type*} [Group G] {Y B : Subgroup G}

/-- Relative normalization transfers the intersection of the embedded cores. -/
theorem pCoreIn_inf_le_of_normalizes (hBY : B ≤ normalizer (Y : Set G)) :
    Y.pCoreIn 2 ⊓ B ≤ B.pCoreIn 2 := by
  have hn : B ≤ normalizer (Y.pCoreIn 2 : Set G) :=
    hBY.trans (normalizer_le_normalizer_characteristic_image Y (pCore 2 Y))
  exact le_pCoreIn_of_normalizes
    ((isPGroup_pCoreIn 2 Y).to_le inf_le_left) inf_le_right
    (le_normalizer_iff.mpr (fun b hb x hx =>
      ⟨(mem_normalizer_iff.mp (hn hb) x).mp hx.1,
        B.mul_mem (B.mul_mem hb hx.2) (B.inv_mem hb)⟩))

/-- Every element of the intersection is three-primary modulo B's two-core. -/
theorem exists_three_pow_mem_pCoreIn_of_mem_inf
    (hY : IsPGroup 3 (Y ⧸ pCore 2 Y))
    (hBY : B ≤ normalizer (Y : Set G)) {x : G} (hx : x ∈ Y ⊓ B) :
    ∃ k : ℕ, x ^ (3 ^ k) ∈ B.pCoreIn 2 := by
  let y : Y := ⟨x, hx.1⟩
  obtain ⟨k, hk⟩ := hY (QuotientGroup.mk' (pCore 2 Y) y)
  have hy : y ^ (3 ^ k) ∈ pCore 2 Y := by
    apply (QuotientGroup.eq_one_iff _).mp
    change QuotientGroup.mk' (pCore 2 Y) (y ^ (3 ^ k)) = 1
    simpa only [map_pow] using hk
  exact ⟨k, pCoreIn_inf_le_of_normalizes hBY
    ⟨mem_map_of_mem Y.subtype hy, B.pow_mem hx.2 _⟩⟩

/-- Mutual normalization forces three-primary commutator displacements on B/O₂(B). -/
theorem exists_three_pow_commutator_mem_pCoreIn
    (hY : IsPGroup 3 (Y ⧸ pCore 2 Y))
    (hYB : Y ≤ normalizer (B : Set G))
    (hBY : B ≤ normalizer (Y : Set G)) {y b : G} (hy : y ∈ Y) (hb : b ∈ B) :
    ∃ k : ℕ, ⁅y, b⁆ ^ (3 ^ k) ∈ B.pCoreIn 2 := by
  apply exists_three_pow_mem_pCoreIn_of_mem_inf hY hBY
  exact le_inf (le_normalizer_iff_commutator_le_left.mp hBY)
    (le_normalizer_iff_commutator_le_right.mp hYB)
    (commutator_mem_commutator hy hb)

end Subgroup
