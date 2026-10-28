module

public import Theory.GroupTheory.SubgroupProductCard
public import Mathlib.GroupTheory.DoubleCoset
public import Mathlib.Data.Set.Card
public import Mathlib.Tactic.Group

/-!
# Double-coset cardinality and an overgroup bound

Right translation identifies `X g Y` with the product of `X` and `g Y g⁻¹`.
The subgroup-product formula therefore computes its size from the conjugate
intersection. If `g ∉ X`, the sets `X` and `X g X` are disjoint. Every
subgroup containing `X` and `g` has at least their combined cardinality.

All products are set products and all conjugates use left conjugation. No
normality or closure of the double coset is assumed. This is the counting
step in Z. Janko, *A characterization of the Mathieu simple groups, I*,
J. Algebra 9 (1968), 1--19, proof of Lemma 17, p.17,
DOI 10.1016/0021-8693(68)90002-1.
-/

open scoped Pointwise
open DoubleCoset

namespace Subgroup

variable {G : Type*} [Group G] [Finite G]

/-- A double coset is counted by the intersection with the left conjugate
of its right-hand subgroup. -/
public theorem card_doubleCoset_mul_card_inf (X Y : Subgroup G) (g : G) :
    Nat.card (doubleCoset g X Y) *
        Nat.card (X ⊓ Y.map (MulAut.conj g).toMonoidHom : Subgroup G) =
      Nat.card X * Nat.card Y := by
  let f : ((X : Set G) * (Y.map (MulAut.conj g).toMonoidHom : Set G)) ≃
      doubleCoset g X Y :=
    { toFun := fun x => ⟨x * g, by
        obtain ⟨a, ha, b, hb, hab⟩ := x.property
        obtain ⟨y, hy, rfl⟩ := hb
        apply mem_doubleCoset.mpr
        refine ⟨a, ha, y, hy, ?_⟩
        rw [← hab]
        change a * (g * y * g⁻¹) * g = a * g * y
        group⟩
      invFun := fun x => ⟨x * g⁻¹, by
        obtain ⟨a, ha, b, hb, hab⟩ := mem_doubleCoset.mp x.property
        refine Set.mem_mul.mpr ⟨a, ha, (MulAut.conj g) b,
          mem_map_of_mem _ hb, ?_⟩
        rw [hab]
        change a * (g * b * g⁻¹) = a * g * b * g⁻¹
        group⟩
      left_inv := fun x => Subtype.ext (mul_inv_cancel_right (x : G) g)
      right_inv := fun x => Subtype.ext (inv_mul_cancel_right (x : G) g) }
  rw [← Nat.card_congr f, card_set_mul_mul_card_inf,
    ← Nat.card_congr (Y.equivMapOfInjective _ (MulAut.conj g).injective).toEquiv]

/-- An overgroup containing an element outside `X` contains both disjoint
sets `X` and `X g X`. -/
public theorem card_add_doubleCoset_le_card (X H : Subgroup G) (hX : X ≤ H)
    (g : G) (hgH : g ∈ H) (hgX : g ∉ X) :
    Nat.card X + Nat.card X * Nat.card X /
        Nat.card (X ⊓ X.map (MulAut.conj g).toMonoidHom : Subgroup G) ≤
      Nat.card H := by
  have hd : Disjoint (X : Set G) (doubleCoset g X X) := by
    rw [Set.disjoint_left]
    intro x hx hdx
    obtain ⟨a, ha, b, hb, rfl⟩ := mem_doubleCoset.mp hdx
    exact hgX ((X.mul_mem_cancel_left ha).mp ((X.mul_mem_cancel_right hb).mp hx))
  have hs : (X : Set G) ∪ doubleCoset g X X ⊆ H := by
    rintro x (hx | hx)
    · exact hX hx
    · obtain ⟨a, ha, b, hb, rfl⟩ := mem_doubleCoset.mp hx
      exact H.mul_mem (H.mul_mem (hX ha) hgH) (hX hb)
  have hc : Nat.card X + Nat.card (doubleCoset g X X) ≤ Nat.card H := by
    change (X : Set G).ncard + (doubleCoset g X X).ncard ≤ (H : Set G).ncard
    rw [← Set.ncard_union_eq hd]
    exact Set.ncard_le_ncard hs
  have hmul := card_doubleCoset_mul_card_inf X X g
  have hpos : 0 < Nat.card (X ⊓ X.map (MulAut.conj g).toMonoidHom : Subgroup G) :=
    Nat.card_pos
  rw [← hmul, Nat.mul_div_cancel _ hpos]
  exact hc

end Subgroup
