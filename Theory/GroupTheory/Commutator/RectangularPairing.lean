module
public import Mathlib.Algebra.Group.Subgroup.Basic
public import Mathlib.Algebra.Group.Hom.Instances

/-!
# Descent of rectangular pairings

A pairing of two groups into a commutative group descends through a pair of
surjective homomorphisms when it kills the two kernels. The resulting pairing
is evaluated through the literal quotient maps, which may have different
sources and targets.
-/

namespace MonoidHom

/-- Descend a multiplicative pairing independently in its two variables. -/
public theorem exists_descended_rectangular_pairing
    {S T X Y V : Type*} [Group S] [Group T] [Group X] [Group Y] [CommGroup V]
    (f : S →* X) (g : T →* Y) (hf : Function.Surjective f)
    (hg : Function.Surjective g) (b : S →* (T →* V))
    (hl : ∀ x ∈ f.ker, b x = 1) (hr : ∀ x, g.ker ≤ (b x).ker) :
    ∃ c : X →* (Y →* V), ∀ x y, c (f x) (g y) = b x y := by
  let row (x : S) : Y →* V := g.liftOfSurjective hg ⟨b x, hr x⟩
  have hrow (x : S) (y : T) : row x (g y) = b x y :=
    g.liftOfRightInverse_comp_apply _ _ _ y
  let rows : S →* (Y →* V) := {
    toFun := row
    map_one' := by
      ext t
      obtain ⟨y, rfl⟩ := hg t
      rw [hrow, map_one]
      rfl
    map_mul' := by
      intro x y
      ext t
      obtain ⟨z, rfl⟩ := hg t
      change row (x * y) (g z) = row x (g z) * row y (g z)
      rw [hrow, hrow, hrow, map_mul]
      rfl }
  have hker : f.ker ≤ rows.ker := by
    intro x hx
    apply MonoidHom.ext
    intro t
    obtain ⟨y, rfl⟩ := hg t
    change row x (g y) = 1
    rw [hrow, hl x hx]
    rfl
  refine ⟨f.liftOfSurjective hf ⟨rows, hker⟩, ?_⟩
  intro x y
  rw [f.liftOfRightInverse_comp_apply _ _ _ x]
  exact hrow x y

end MonoidHom
