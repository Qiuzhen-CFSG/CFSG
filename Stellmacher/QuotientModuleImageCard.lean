module
public import Stellmacher.LaterDefs

/-!
# Cardinality of a faithful actor image

For a centralizer quotient-module witness and a subgroup Y of its source,
the image order times the order of C_Y(V) is exactly the order of Y.
Restrict the projection to Y, identify its range with the projected subgroup
and its kernel with the ambient centralizer intersection, then apply the
kernel-index cardinal formula.

This shared first-isomorphism calculation is used in both directions of the
module measure argument in Stellmacher (8.1), journal p.37: the lower index
bound and the upper bound defining an offender. It requires no finiteness
beyond the cardinal formula already provided by the group library.
-/

namespace Stellmacher.Later

universe u

/-- The faithful image order times the actor's centralizer order is its order. -/
public theorem QuotientModuleWitness.image_card_mul_centralizer_card
    {G : Type u} [Group G] {A V : Subgroup G}
    (w : QuotientModuleWitness A (A ⊓ Subgroup.centralizer (V : Set G)) V)
    (Y : Subgroup G) (hYA : Y ≤ A) :
    let _ := w.groupX
    Nat.card ((Y.subgroupOf A).map w.projection) *
      Nat.card (Y ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) = Nat.card Y := by
  let := w.groupX
  let Yb : Subgroup w.X := (Y.subgroupOf A).map w.projection
  let f : Y →* w.X := w.projection.comp (Subgroup.inclusion hYA)
  have hfrange : f.range = Yb := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨⟨y, hYA y.property⟩, y.property, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨⟨y, hy⟩, rfl⟩
  let K : Subgroup G := Y ⊓ Subgroup.centralizer (V : Set G)
  have hker : f.ker = K.subgroupOf Y := by
    ext y
    change w.projection (Subgroup.inclusion hYA y) = 1 ↔ (y : G) ∈ K
    change Subgroup.inclusion hYA y ∈ w.projection.ker ↔ (y : G) ∈ K
    rw [w.kernel_eq]
    exact ⟨fun hy ↦ ⟨y.property, hy.2⟩, fun hy ↦ ⟨hYA y.property, hy.2⟩⟩
  have hcardK : Nat.card f.ker = Nat.card K := by
    rw [hker]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  have hcard := f.ker.card_mul_index
  rw [Subgroup.index_ker, hfrange, hcardK] at hcard
  change Nat.card Yb * Nat.card K = Nat.card Y
  simpa [Nat.mul_comm] using hcard

end Stellmacher.Later

