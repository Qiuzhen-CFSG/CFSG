module
public import Theory.GroupAction.RankTwoCosetCover
public import Mathlib.GroupTheory.Index
/-!
# Valences of rank-two coset graphs

The neighbors of the standard vertex of type `i` are the cosets of the
intersection in its endpoint subgroup. Representatives in that subgroup give
both surjectivity and injectivity. Thus the valence is the actual intrinsic
subgroup index, even when the ambient completion is infinite.

Source: Aschbacher--Smith, F.3.3 and F.4.4--5, printed pp.270 and 274--275.
-/

@[expose] public section
noncomputable section
namespace Subgroup.CosetGeometry.RankTwo
variable {G : Type*} [Group G] (F : Bool → Subgroup G)
def neighborQuotientMap (i : Bool) :
    (F i ⧸ (F (!i)).subgroupOf (F i)) → (graph F).neighborSet (base F i) :=
  Quotient.lift (fun a : F i =>
    ⟨mkVertex F (!i) a, by
      refine ⟨by change i ≠ !i; cases i <;> decide, ?_⟩
      apply (incident_base_iff F i _).mpr
      exact ⟨a, a.property, rfl⟩⟩) (by
    intro a b hab
    apply Subtype.ext
    apply (mkVertex_eq F (!i) a b).mpr
    have hh : a⁻¹ * b ∈ (F (!i)).subgroupOf (F i) := QuotientGroup.leftRel_apply.mp hab
    exact hh)

theorem neighborQuotientMap_bijective (i : Bool) : Function.Bijective (neighborQuotientMap F i) := by
  constructor
  · intro x y hxy
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective y
    apply QuotientGroup.eq.mpr
    exact (mkVertex_eq F (!i) a b).mp (congrArg Subtype.val hxy)
  · intro v
    obtain ⟨a, ha, he⟩ := neighbor_base_rep F i v.property
    exact ⟨((⟨a, ha⟩ : F i) : F i ⧸ (F (!i)).subgroupOf (F i)), Subtype.ext he⟩

/-- The neighbors at a standard vertex are its intrinsic cosets modulo the
intersection of the two endpoint groups. -/
def neighborEquivQuotient (i : Bool) :
    (graph F).neighborSet (base F i) ≃ (F i ⧸ (F (!i)).subgroupOf (F i)) :=
  (Equiv.ofBijective (neighborQuotientMap F i) (neighborQuotientMap_bijective F i)).symm

theorem card_neighbor_base (i : Bool) :
    Nat.card ((graph F).neighborSet (base F i)) =
      ((F (!i)).subgroupOf (F i)).index := by
  rw [Nat.card_congr (neighborEquivQuotient F i), Subgroup.index_eq_card]
end Subgroup.CosetGeometry.RankTwo
