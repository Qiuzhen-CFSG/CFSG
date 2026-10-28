module

public import Theory.GroupTheory.CentralizerIndexBound
public import Mathlib.Algebra.Group.Subgroup.Finite

/-!
# Excluding large abelian subgroups outside an abelian kernel

Suppose a quotient subgroup has order at most b, each nontrivial quotient
element fixes at most a elements of an abelian kernel, and the whole
quotient subgroup fixes fewer than a. Counting an abelian subgroup E
through its kernel intersection shows that |E| ≥ ab forces E into the
kernel: otherwise equality in the first bound makes its image the whole
quotient subgroup, where the strict second bound gives a contradiction.

Application: the E₁₆ octad kernel acting on the E₂¹¹ kernel of J₄ max1,
with a = 128 and b = 16; GLS3 Table 5.3i. This counting argument uses
neither a splitting nor an elementary-abelian quotient lift.
-/

public section

open Subgroup
open scoped IsMulCommutative
namespace Subgroup
variable {G H : Type*} [Group G] [Group H] [Finite G] [Finite H]

theorem abelian_le_kernel_of_centralizer_bounds
    (f : G →* H) [IsMulCommutative f.ker] (U : Subgroup H)
    (a b : ℕ) (ha : 0 < a)
    (hU : Nat.card U ≤ b)
    (hfixed : ∀ x ∈ U.comap f, x ∉ f.ker →
      Nat.card ((centralizer ({x} : Set G)).subgroupOf f.ker) ≤ a)
    (hall : Nat.card ((centralizer (U.comap f : Set G)).subgroupOf f.ker) < a)
    (E : Subgroup G) [IsMulCommutative E] (hEU : E ≤ U.comap f)
    (hE : a * b ≤ Nat.card E) : E ≤ f.ker := by
  by_contra hn
  obtain ⟨x, hxE, hxV⟩ := SetLike.not_le_iff_exists.mp hn
  have hEx : E ≤ centralizer ({x} : Set G) := by
    intro e he y hy
    have hyx : y = x := Set.mem_singleton_iff.mp hy
    subst y
    exact congrArg Subtype.val (mul_comm (⟨x, hxE⟩ : E) ⟨e, he⟩)
  have hsize := card_le_centralizer_card_mul_relIndex E f.ker ({x} : Set G) hEx
  rw [relIndex_ker] at hsize
  have himage : E.map f ≤ U := map_le_iff_le_comap.mpr hEU
  have hd : Nat.card (E.map f) ≤ b := (card_le_of_le himage).trans hU
  have hupper : Nat.card E ≤ a * Nat.card (E.map f) :=
    hsize.trans (Nat.mul_le_mul_right _ (hfixed x (hEU hxE) hxV))
  have hbeq : b ≤ Nat.card (E.map f) :=
    (Nat.le_of_mul_le_mul_left (hE.trans hupper) ha)
  have hmap : E.map f = U := eq_of_le_of_card_ge himage (hU.trans hbeq)
  have hsup : E ⊔ f.ker = U.comap f := by rw [← hmap, comap_map_eq]
  have hc : (centralizer (E : Set G)).subgroupOf f.ker ≤
      (centralizer (U.comap f : Set G)).subgroupOf f.ker := by
    intro v hv
    have hEcv : E ≤ centralizer ({(v : G)} : Set G) := by
      intro e he z hz
      obtain rfl := Set.mem_singleton_iff.mp hz
      exact (hv e he).symm
    have hVcv : f.ker ≤ centralizer ({(v : G)} : Set G) := by
      intro w hw z hz
      obtain rfl := Set.mem_singleton_iff.mp hz
      exact congrArg Subtype.val (mul_comm v (⟨w, hw⟩ : f.ker))
    have hQcv : U.comap f ≤ centralizer ({(v : G)} : Set G) :=
      hsup ▸ sup_le hEcv hVcv
    intro z hz
    exact (hQcv hz v rfl).symm
  have hsmall : Nat.card ((centralizer (E : Set G)).subgroupOf f.ker) < a :=
    (card_le_of_le hc).trans_lt hall
  have hsize' := card_le_centralizer_card_mul_relIndex E f.ker (E : Set G) E.le_centralizer
  rw [relIndex_ker] at hsize'
  have hb : 0 < b := (Nat.card_pos (α := E.map f)).trans_le hd
  have hlt : Nat.card E < a * b :=
    (hsize'.trans (Nat.mul_le_mul_left _ hd)).trans_lt (Nat.mul_lt_mul_of_pos_right hsmall hb)
  exact (not_lt_of_ge hE) hlt

end Subgroup
