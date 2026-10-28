module

public import Theory.GroupTheory.PrimeRankHom

/-!
# Abelian two-subgroups acting with a kernel of order at most two

The kernel/image rank inequality adds at most one to the target's two-rank.
If an abelian two-group of rank at least four acts with such a kernel, its
image has rank at least three. An order bound of sixteen for that image then
bounds the acting group by thirty-two, by the first isomorphism theorem.

This is the numerical transfer used in GLS4, Chapter 2, Section 13,
inequality (13C) and its equality case. The model-specific image bounds are
explicit premises; this module makes no assertion about unitary groups.
-/

public section
open Subgroup
open scoped IsMulCommutative
namespace Theory.GroupTheory

variable {G H : Type*} [Group G] [Group H] [Finite G] [Finite H]

private theorem twoRank_le_one_of_card_le_two (K : Type*) [Group K] [Finite K]
    (hK : Nat.card K ≤ 2) : primeRank 2 K ≤ 1 := by
  apply (primeRank_le_iff_elementary_card_le K).mpr
  intro E _
  simpa using E.card_le_card_group.trans hK

/-- A kernel of order at most two adds at most one to the target rank. -/
theorem primeRank_le_succ_of_kernel_card_le_two (f : G →* H) {n : ℕ}
    (hker : Nat.card f.ker ≤ 2) (hH : primeRank 2 H ≤ n) :
    primeRank 2 G ≤ n + 1 := by
  have hk := twoRank_le_one_of_card_le_two f.ker hker
  have hr := primeRank_le_ker_add (p := 2) f
  omega

/-- In rank at least four the image has rank at least three, so its order
bound of sixteen gives the order bound of thirty-two for the domain. -/
theorem card_le_thirty_two_of_abelian_image_bound (f : G →* H)
    (hG : IsPGroup 2 G) [IsMulCommutative G]
    (hker : Nat.card f.ker ≤ 2) (hrank : 4 ≤ primeRank 2 G)
    (himage : ∀ B : Subgroup H, IsPGroup 2 B → IsMulCommutative B →
      3 ≤ primeRank 2 B → Nat.card B ≤ 16) :
    Nat.card G ≤ 32 := by
  have hk := twoRank_le_one_of_card_le_two f.ker hker
  have hr := primeRank_le_ker_add (p := 2) f.rangeRestrict
  have heker : f.rangeRestrict.ker = f.ker := by
    ext x
    exact Subtype.ext_iff
  rw [heker] at hr
  have hrc : IsMulCommutative f.range := by
    apply IsMulCommutative.of_comm
    intro x y
    obtain ⟨a, rfl⟩ := f.rangeRestrict_surjective x
    obtain ⟨b, rfl⟩ := f.rangeRestrict_surjective y
    rw [← map_mul, ← map_mul, mul_comm a b]
  have hc := himage f.range
    (hG.of_surjective f.rangeRestrict f.rangeRestrict_surjective) hrc (by omega)
  calc
    Nat.card G = Nat.card f.ker * Nat.card f.range := by
      rw [← index_ker, card_mul_index]
    _ ≤ 2 * 16 := Nat.mul_le_mul hker hc
    _ = 32 := by decide

end Theory.GroupTheory
