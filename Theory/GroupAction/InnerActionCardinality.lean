module

public import Mathlib.GroupTheory.Index
public import Mathlib.GroupTheory.Subgroup.Center
public import Mathlib.GroupTheory.Subgroup.Centralizer

/-!
# The order of an action realized by inner conjugators

If an action is realized by elements of Z in L, its image has order at
most |Z : Z ∩ Z(L)|. The proof compares the action image with the image of
the literal conjugation homomorphism on Z and identifies its kernel.
This is the inner-action order comparison in Aschbacher–Smith E.6.7, p.246.
-/

public section
namespace Theory.GroupAction
open Subgroup

/-- An inner witness for every actor bounds the image by the actual central quotient. -/
theorem card_range_le_inner_quotient {A L : Type*} [Group A] [Group L] [Finite L]
    (f : A →* MulAut L) (Z : Subgroup L)
    (hi : ∀ a, ∃ z : Z, f a = MulAut.conj (z : L)) :
    Nat.card f.range ≤ Nat.card (Z ⧸ (center L).subgroupOf Z) := by
  let g : Z →* MulAut L := (MulAut.conj : L →* MulAut L).comp Z.subtype
  have hfg : f.range ≤ g.range := by
    rintro _ ⟨a, rfl⟩
    obtain ⟨z, hz⟩ := hi a
    exact ⟨z, hz.symm⟩
  have hk : g.ker = (center L).subgroupOf Z := by
    ext z
    change MulAut.conj (z : L) = 1 ↔ (z : L) ∈ center L
    constructor
    · intro he
      apply mem_center_iff.mpr
      intro l
      have hh := MulEquiv.congr_fun he l
      change (z : L) * l * (z : L)⁻¹ = l at hh
      exact (mul_inv_eq_iff_eq_mul.mp hh).symm
    · intro hz
      apply MulEquiv.ext
      intro l
      change (z : L) * l * (z : L)⁻¹ = l
      rw [← mem_center_iff.mp hz l, mul_inv_cancel_right]
  calc
    Nat.card f.range ≤ Nat.card g.range :=
      Nat.card_le_card_of_injective (inclusion hfg) (inclusion_injective hfg)
    _ = Nat.card (Z ⧸ (center L).subgroupOf Z) := by
      rw [← index_ker, hk, index_eq_card]

end Theory.GroupAction
