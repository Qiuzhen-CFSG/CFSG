module
public import Theory.GroupTheory.AbelianIndexTwoCentralizers
public import Mathlib.GroupTheory.Index

/-!
# The centralizer of an abelian kernel with a small-index supplement

If an abelian subgroup is not central, an index-at-most-two commuting
supplement is its full centralizer. The commuting product inherits every
common power bound of its two factors. These are the intrinsic group
steps in the abelian-core branch of Aschbacher--Smith 2.5.21, p.565.
-/

public section
open scoped Pointwise
namespace Subgroup
variable {S : Type*} [Group S] [Finite S]

/-- The core centralizer is the indicated product when that product has index at most two. -/
theorem centralizer_eq_sup_of_index_le_two
    (C D : Subgroup S) [IsMulCommutative C]
    (hDC : D ≤ centralizer (C : Set S))
    (hi : (C ⊔ D).index ≤ 2) (hn : ¬ C ≤ center S) :
    centralizer (C : Set S) = C ⊔ D ∧ (C ⊔ D).index = 2 := by
  have hle : C ⊔ D ≤ centralizer (C : Set S) := sup_le C.le_centralizer hDC
  have hne : centralizer (C : Set S) ≠ ⊤ := by
    intro he
    apply hn
    intro c hc
    exact mem_center_iff.mpr fun s =>
      (show s ∈ centralizer (C : Set S) from he ▸ mem_top s) c hc |>.symm
  have hpos : 0 < (C ⊔ D).index := Nat.pos_of_ne_zero (index_ne_zero_of_finite (H := C ⊔ D))
  have higt : 1 < (C ⊔ D).index := one_lt_index_of_ne_top (by
    intro he
    exact hne (top_unique (he ▸ hle)))
  have hie : (C ⊔ D).index = 2 := by omega
  refine ⟨?_, hie⟩
  by_contra he
  have hlt : C ⊔ D < centralizer (C : Set S) := lt_of_le_of_ne hle (Ne.symm he)
  have hstrict := index_strictAnti hlt
  have hcent := one_lt_index_of_ne_top hne
  omega

omit [Finite S] in
/-- The indicated commuting product inherits a common power bound. -/
theorem sup_power_bound_of_commute
    (C D : Subgroup S) (hDC : D ≤ centralizer (C : Set S))
    (m : ℕ) (hC : ∀ c ∈ C, c ^ m = 1) (hD : ∀ d ∈ D, d ^ m = 1) :
    ∀ a ∈ C ⊔ D, a ^ m = 1 := by
  have hn : D ≤ normalizer (C : Set S) := hDC.trans (centralizer_le_normalizer _)
  intro a ha
  have he : a ∈ (C : Set S) * (D : Set S) := by
    rwa [← coe_mul_of_right_le_normalizer_left C D hn]
  obtain ⟨c, hc, d, hd, rfl⟩ := he
  rw [(show Commute c d from hDC hd c hc).mul_pow, hC c hc, hD d hd, one_mul]
end Subgroup
