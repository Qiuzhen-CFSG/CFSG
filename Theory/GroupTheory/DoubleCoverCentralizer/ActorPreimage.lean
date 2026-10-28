module
public import Theory.GroupTheory.DoubleCoverCentralizer.Action

/-!
# The preimage of the actual inner actors

For an action α on H, take the preimage of its image under inner conjugation.
Its kernel is Z(H), and its image is precisely the inner part of the acting
group. This gives its order without any equality with a full centralizer.
If the actors and the center are p-groups, the preimage is a p-group as well.

This is the actor-image variant of the cover argument in Aschbacher–Smith,
16.3.6, printed p.1179 / PDF p.1196 (1 March 2004 manuscript).
-/

@[expose] public section
namespace Theory.GroupTheory.DoubleCoverCentralizer
open Subgroup
variable {H A : Type*} [Group H] [Group A]

/-- The elements implementing actual actors by inner conjugation. -/
def actorPreimage (α : A →* MulAut H) : Subgroup H :=
  α.range.comap (MulAut.conj : H →* MulAut H)

theorem center_le_actorPreimage (α : A →* MulAut H) : center H ≤ actorPreimage α := by
  intro z hz
  have hc : MulAut.conj z = 1 := by
    change z ∈ (MulAut.conj : H →* MulAut H).ker
    rwa [conj_kernel]
  change MulAut.conj z ∈ α.range
  rw [hc]
  exact α.range.one_mem

/-- Every inner representative of an actor fixing J centralizes J. -/
theorem actorPreimage_le_centralizer (J : Subgroup H) (α : A →* MulAut H)
    (hfix : ∀ a : A, ∀ j : J, α a j = j) :
    actorPreimage α ≤ centralizer (J : Set H) := by
  rintro f ⟨a, ha⟩ j hj
  have h := hfix a ⟨j, hj⟩
  rw [ha] at h
  change f * j * f⁻¹ = j at h
  exact ((mul_inv_eq_iff_eq_mul).mp h).symm

/-- The preimage maps onto precisely the image of the inner actors. -/
theorem actorPreimage_conj_range (α : A →* MulAut H) :
    ((MulAut.conj : H →* MulAut H).comp (actorPreimage α).subtype).range =
      (innerActors α).map α := by
  ext a
  constructor
  · rintro ⟨f, rfl⟩
    obtain ⟨e, he⟩ := f.property
    exact ⟨e, (show α e ∈ (MulAut.conj : H →* MulAut H).range from
      he.symm ▸ ⟨f, rfl⟩), he⟩
  · rintro ⟨e, he, rfl⟩
    obtain ⟨f, hf⟩ := he
    exact ⟨⟨f, (show MulAut.conj f ∈ α.range from hf ▸ ⟨e, rfl⟩)⟩, hf⟩

/-- The center-kernel formula for the actual actor preimage. -/
theorem actorPreimage_card (α : A →* MulAut H) (hinj : Function.Injective α) :
    Nat.card (actorPreimage α) = Nat.card (center H) * Nat.card (innerActors α) := by
  let D := actorPreimage α
  let f := (MulAut.conj : H →* MulAut H).comp D.subtype
  have hk : f.ker = (center H).subgroupOf D := by
    ext d
    change MulAut.conj (d : H) = 1 ↔ (d : H) ∈ center H
    rw [← conj_kernel]
    rfl
  have hkcard : Nat.card f.ker = Nat.card (center H) := by
    rw [hk]
    exact Nat.card_congr (subgroupOfEquivOfLe (center_le_actorPreimage α)).toEquiv
  have hr : Nat.card f.range = Nat.card (innerActors α) := by
    rw [actorPreimage_conj_range]
    exact card_map_of_injective hinj
  calc
    Nat.card D = Nat.card f.ker * f.ker.index := f.ker.card_mul_index.symm
    _ = Nat.card (center H) * Nat.card (innerActors α) := by
      rw [index_ker, hkcard, hr]

/-- The actor preimage is a p-group when both its image and center-kernel are. -/
theorem actorPreimage_isPGroup (α : A →* MulAut H) {p : ℕ}
    (hA : IsPGroup p A) (hZ : IsPGroup p (center H)) :
    IsPGroup p (actorPreimage α) := by
  have hr : IsPGroup p α.range :=
    hA.of_surjective α.rangeRestrict α.rangeRestrict_surjective
  exact hr.comap_of_ker_isPGroup MulAut.conj (by rwa [conj_kernel])

end Theory.GroupTheory.DoubleCoverCentralizer
