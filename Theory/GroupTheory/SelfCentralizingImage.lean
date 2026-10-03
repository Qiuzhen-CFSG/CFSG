module
public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.GroupTheory.Index

/-!
# Centralizer orders from self-centralizing images

If a homomorphism is injective on an abelian subgroup T and its image
is self-centralizing, then C(T) has order |T| times the order of the
intersection of C(T) with the kernel. In particular, when the kernel
centralizes T, the full kernel order contributes. The image of C(T) equals
the image of T; apply the kernel–image cardinality formula.

This elementary counting argument is used in Alperin–Brauer–Gorenstein,
III.8 Proposition 5, article p.117.
-/

namespace Subgroup

/-- With a self-centralizing abelian image, only the part of the kernel
centralizing the subgroup contributes to the centralizer order. -/
public theorem card_centralizer_of_selfCentralizing_image_intersection
    {G H : Type*} [Group G] [Finite G] [Group H]
    (f : G →* H) (T : Subgroup G) [IsMulCommutative T]
    (hinj : Function.Injective (f.comp T.subtype))
    (hself : centralizer (T.map f : Set H) = T.map f) :
    Nat.card (centralizer (T : Set G)) =
      Nat.card T * Nat.card (f.ker.subgroupOf (centralizer (T : Set G))) := by
  let C := centralizer (T : Set G)
  have hmap : C.map f = T.map f := by
    apply le_antisymm
    · exact (map_centralizer_le_centralizer_image _ f).trans hself.le
    · exact map_mono T.le_centralizer
  have hcard : Nat.card (T.map f) = Nat.card T := by
    apply Nat.card_image_of_injOn
    intro a ha b hb hab
    exact congrArg Subtype.val (hinj (show f.comp T.subtype ⟨a, ha⟩ =
      f.comp T.subtype ⟨b, hb⟩ from hab))
  have h := (f.ker.subgroupOf C).index_mul_card
  rw [show (f.ker.subgroupOf C).index = f.ker.relIndex C from rfl,
    relIndex_ker, hmap, hcard] at h
  exact h.symm

/-- Count a centralizer using an injective, self-centralizing image. -/
public theorem card_centralizer_of_selfCentralizing_image
    {G H : Type*} [Group G] [Finite G] [Group H]
    (f : G →* H) (T : Subgroup G) [IsMulCommutative T]
    (hinj : Function.Injective (f.comp T.subtype))
    (hker : f.ker ≤ centralizer (T : Set G))
    (hself : centralizer (T.map f : Set H) = T.map f) :
    Nat.card (centralizer (T : Set G)) = Nat.card T * Nat.card f.ker := by
  rw [card_centralizer_of_selfCentralizing_image_intersection f T hinj hself,
    Nat.card_congr (subgroupOfEquivOfLe hker).toEquiv]

end Subgroup
