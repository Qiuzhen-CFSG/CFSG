module

public import Mathlib.Algebra.Group.Subgroup.Order
public import Mathlib.Algebra.Group.Subgroup.Finite
public import Mathlib.GroupTheory.Subgroup.Centralizer

/-!
# Centralizer maximality and double centralizers under equivalences

An actual group equivalence carries a set centralizer onto the centralizer
of its image. Applying this twice preserves the cardinality of the ambient
double centralizer; the subgroup order isomorphism preserves maximality.
These transport lemmas retain the ambient group at both centralizer levels.
Their concrete consumer is the marked degree-28 Rudvalis representation.
-/

public section

open Subgroup
namespace Subgroup
variable {G H : Type*} [Group G] [Group H]

private theorem centralizer_equiv_image (e : G ≃* H) (s : Set G) :
    (centralizer s).map e.toMonoidHom = centralizer (e '' s) := by
  apply le_antisymm (map_centralizer_le_centralizer_image _ _)
  intro x hx
  refine ⟨e.symm x, ?_, e.apply_symm_apply x⟩
  intro y hy
  apply e.injective
  simpa only [map_mul, e.apply_symm_apply] using hx (e y) ⟨y, hy, rfl⟩

theorem isCoatom_centralizer_equiv_iff (e : G ≃* H) (t : G) :
    IsCoatom (centralizer ({e t} : Set H)) ↔ IsCoatom (centralizer ({t} : Set G)) := by
  rw [← Set.image_singleton, ← centralizer_equiv_image]
  exact OrderIso.isCoatom_iff e.mapSubgroup _

theorem card_doubleCentralizer_equiv (e : G ≃* H) (t : G) :
    Nat.card (centralizer (centralizer ({e t} : Set H) : Set H)) =
      Nat.card (centralizer (centralizer ({t} : Set G) : Set G)) := by
  have hinner : centralizer ({e t} : Set H) =
      (centralizer ({t} : Set G)).map e.toMonoidHom := by
    rw [centralizer_equiv_image, Set.image_singleton]
  rw [hinner, coe_map]
  change Nat.card (centralizer (e '' (centralizer ({t} : Set G) : Set G))) = _
  rw [← centralizer_equiv_image e, card_map_of_injective e.injective]
end Subgroup
