module

public import Theory.GroupAction.PermutationLiftSubgroup

/-!
# Restricting a permutation action to an injectively named family

If every actor induces a permutation in H on an injectively named family,
that induced permutation is unique. Choosing it therefore gives a homomorphism
to H, with the original intertwining equation. The Lyons pair-orbit construction
uses this for eleven distinct sets of matrices.
-/

@[expose] public section

namespace Theory.GroupAction

variable {G X Y : Type*} [Group G]
  (ρ : G →* Equiv.Perm Y) (point : X → Y)
  (hp : Function.Injective point) (H : Subgroup (Equiv.Perm X))
  (h : ∀ g, ∃ p : H, ∀ x, ρ g (point x) = point (p.val x))

/-- The unique induced permutation on an injectively named invariant family. -/
noncomputable def permutationLiftHom : G →* H where
  toFun g := (h g).choose
  map_one' := by
    apply Subtype.ext
    ext x
    apply hp
    exact ((h 1).choose_spec x).symm.trans (by simp)
  map_mul' g k := by
    apply Subtype.ext
    ext x
    apply hp
    rw [← (h (g * k)).choose_spec x, map_mul, Equiv.Perm.mul_apply,
      (h k).choose_spec x, (h g).choose_spec]
    rfl

theorem permutationLiftHom_spec (g : G) (x : X) :
    ρ g (point x) = point ((permutationLiftHom ρ point hp H h g).val x) :=
  (h g).choose_spec x

/-- A specified intertwiner identifies the induced permutation exactly. -/
theorem permutationLiftHom_eq (g : G) (p : H)
    (he : ∀ x, ρ g (point x) = point (p.val x)) :
    permutationLiftHom ρ point hp H h g = p := by
  apply Subtype.ext
  ext x
  apply hp
  exact (permutationLiftHom_spec ρ point hp H h g x).symm.trans (he x)

end Theory.GroupAction
