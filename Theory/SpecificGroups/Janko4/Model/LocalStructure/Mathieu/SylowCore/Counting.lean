module

public import Mathlib.GroupTheory.Index
public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Theory.ElementaryAbelian.Basic

/-!
# Counting elementary subgroups across an abelian kernel

For an abelian subgroup `A` and a normal subgroup `E`, the kernel of the map
`A → G/E` embeds in `C_E(A)`. Thus `|A| ≤ |AE/E| |C_E(A)|`. A strict bound
below `|E|` for normal elementary subgroups not contained in `E` makes an
elementary `E` characteristic: apply the bound to each automorphic image.

This is the group-theoretic deduction for the literal J₄ max1 kernel. The
finite action calculation needed to instantiate its hypothesis is separate.
Source context: Kleidman–Wilson, *The maximal subgroups of J₄* (1988),
pp.484–510, and GLS3 Table 5.3i. The counting argument itself is general.
-/

public section

namespace Janko4.LocalStructure.SylowCore
open Subgroup
open scoped IsMulCommutative

/-- The quotient kernel of an abelian subgroup embeds in its centralizer in `E`. -/
theorem card_le_image_mul_centralizer {G : Type*} [Group G] [Finite G]
    (E A : Subgroup G) [E.Normal] [IsMulCommutative A] :
    Nat.card A ≤ Nat.card (A.map (QuotientGroup.mk' E)) *
      Nat.card ((centralizer (A : Set G)).subgroupOf E) := by
  let f := (QuotientGroup.mk' E).comp A.subtype
  have hcard : Nat.card A = Nat.card f.ker * Nat.card f.range := by
    rw [← f.ker.card_mul_index, index_ker]
  have hrange : f.range = A.map (QuotientGroup.mk' E) := by
    rw [MonoidHom.range_comp, range_subtype]
  let j : f.ker → (centralizer (A : Set G)).subgroupOf E := fun x =>
    ⟨⟨x.val.val, (QuotientGroup.eq_one_iff _).mp x.property⟩, by
      apply mem_centralizer_iff.mpr
      intro a ha
      exact congrArg Subtype.val (mul_comm (⟨a, ha⟩ : A) x.val)⟩
  have hj : Function.Injective j := by
    intro x y h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : (centralizer (A : Set G)).subgroupOf E => z.val.val) h
  calc
    Nat.card A = Nat.card f.ker * Nat.card f.range := hcard
    _ ≤ Nat.card ((centralizer (A : Set G)).subgroupOf E) * Nat.card f.range :=
      Nat.mul_le_mul_right _ (Nat.card_le_card_of_injective j hj)
    _ = _ := by rw [hrange, Nat.mul_comm]

/-- A subgroup at least as large as `E` must equal `E` under the strict bound. -/
theorem eq_of_card_le_of_image_centralizer_bound {G : Type*} [Group G] [Finite G]
    (E A : Subgroup G) [E.Normal] [IsMulCommutative A]
    (hbound : ¬ A ≤ E → Nat.card (A.map (QuotientGroup.mk' E)) *
      Nat.card ((centralizer (A : Set G)).subgroupOf E) < Nat.card E)
    (hcard : Nat.card E ≤ Nat.card A) : A = E := by
  have hle : A ≤ E := by
    by_contra hn
    exact (not_lt_of_ge hcard)
      (lt_of_le_of_lt (card_le_image_mul_centralizer E A) (hbound hn))
  exact eq_of_le_of_card_ge hle hcard

/-- Automorphisms preserve normality, elementary structure and cardinality. -/
theorem characteristic_of_image_centralizer_bound {G : Type*} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] (E : Subgroup G) [E.Normal] [IsElementaryAbelian p E]
    (hbound : ∀ (A : Subgroup G), A.Normal → IsElementaryAbelian p A → ¬ A ≤ E →
      Nat.card (A.map (QuotientGroup.mk' E)) *
        Nat.card ((centralizer (A : Set G)).subgroupOf E) < Nat.card E) :
    E.Characteristic := by
  apply characteristic_iff_map_eq.mpr
  intro e
  let A := E.map e.toMonoidHom
  have hA : A.Normal := (inferInstance : E.Normal).map _ e.surjective
  have : IsElementaryAbelian p A := IsElementaryAbelian.map _
  have hcard : Nat.card A = Nat.card E := card_map_of_injective e.injective
  exact eq_of_card_le_of_image_centralizer_bound E A
    (hbound A hA inferInstance) hcard.ge

end Janko4.LocalStructure.SylowCore
