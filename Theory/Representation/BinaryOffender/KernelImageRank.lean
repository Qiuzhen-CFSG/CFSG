module
public import Theory.Representation.BinaryOffender.Basic
public import Theory.ElementaryAbelian.Injective
public import Theory.ElementaryAbelian.Quotient
/-!
# Rank budget for an image and the kernel of a second action

For two homomorphisms on a finite elementary two-group, the first image's
rank is bounded by the second image's rank plus the first image of its
kernel. The index of a subgroup cannot increase under a surjection; applying
this to the second kernel and taking binary logarithms proves the bound.

The original tensor-module application combines it with the additive
fixed-codimension budget to retain the whole pointwise seed kernel.
Source: the group-order identity underlying Aschbacher--Smith D.2.2,
printed p.178, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace Representation.BinaryOffender
private theorem card_two_pow_log (H : Type*) [Group H] [Finite H] [IsElementaryAbelian 2 H] :
    Nat.card H = 2 ^ Nat.log 2 (Nat.card H) := by
  obtain ⟨k,hk⟩ := (IsElementaryAbelian.isPGroup 2 H).exists_card_eq
  rw [hk,Nat.log_pow (by decide : 1 < 2)]

variable {A B C : Type*} [Group A] [Group B] [Group C] [Finite A]
  [IsElementaryAbelian 2 A]
/-- The image on the original carrier is bounded by the image on a section
and the remaining kernel image, without a faithfulness hypothesis. -/
theorem rank_range_le_range_add_kernel_image (f : A →* B) (g : A →* C) :
    rank g.range ≤ rank f.range + rank (f.ker.map g) := by
  let : IsElementaryAbelian 2 f.ker := IsElementaryAbelian.of_injective f.ker.subtype f.ker.subtype_injective
  let : Finite f.range := Finite.of_surjective _ f.rangeRestrict_surjective
  let : Finite g.range := Finite.of_surjective _ g.rangeRestrict_surjective
  let : Finite (f.ker.map g) := Finite.of_surjective _ (g.subgroupMap_surjective f.ker)
  let K := f.ker.map g.rangeRestrict
  have hi : K.index ≤ Nat.card f.range := by
    rw [←Subgroup.index_ker]
    exact Nat.le_of_dvd (Nat.pos_of_ne_zero f.ker.index_ne_zero_of_finite) (f.ker.index_map_dvd g.rangeRestrict_surjective)
  have hc : Nat.card g.range ≤ Nat.card f.range * Nat.card K := by
    rw [←K.index_mul_card]
    exact Nat.mul_le_mul_right _ hi
  have hk : Nat.card K = Nat.card (f.ker.map g) := by
    have he : K.map g.range.subtype = f.ker.map g := by
      rw [map_map]
      rfl
    rw [←he]
    exact (Nat.card_congr (K.equivMapOfInjective g.range.subtype g.range.subtype_injective).toEquiv)
  rw [hk] at hc
  let : IsElementaryAbelian 2 f.range := IsElementaryAbelian.of_surjective _ f.rangeRestrict_surjective
  let : IsElementaryAbelian 2 g.range := IsElementaryAbelian.of_surjective _ g.rangeRestrict_surjective
  let : IsElementaryAbelian 2 (f.ker.map g) := IsElementaryAbelian.map _
  have hlog := Nat.log_mono_right (b := 2) hc
  rw [card_two_pow_log f.range,card_two_pow_log (f.ker.map g),←pow_add,Nat.log_pow (by decide : 1 < 2)] at hlog
  exact hlog
end Representation.BinaryOffender
