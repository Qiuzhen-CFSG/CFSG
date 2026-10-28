/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/LinearAlgebra/AffinePermutation.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Mathlib.LinearAlgebra.AffineSpace.AffineEquiv
public import Mathlib.Tactic.Ring

/-!
# Affine permutations from coordinate functions

Coordinatewise affine scalar formulas construct an affine map with
the original underlying function. Bijectivity upgrades it to an affine
equivalence without changing the permutation.

Source: Gerald Höhn, ATLAS, `Atlas/LinearAlgebra/AffinePermutation.lean`,
revision `8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adaptation: Lean 4.33.0 module boundaries and rewritten project imports.
Import the ring tactic explicitly for the coordinate calculations.
Definitions remain exposed for the source computational interfaces.
-/

@[expose] public section

namespace Atlas.LinearAlgebra

variable {F I : Type*} [Field F]

/-- Coordinatewise affine scalar functions determine an actual affine map. -/
def affineMapOfCoordinateAffine (p : (I → F) → (I → F))
    (hp : ∀ i, ∃ a : F, ∃ l : (I → F) →ₗ[F] F, ∀ v, p v i = a + l v) :
    (I → F) →ᵃ[F] (I → F) where
  toFun := p
  linear := {
    toFun := fun v => p v - p 0
    map_add' := by
      intro v w
      funext i
      obtain ⟨a,l,hl⟩ := hp i
      change p (v+w) i - p 0 i = (p v i-p 0 i)+(p w i-p 0 i)
      rw [hl,hl,hl,hl,map_add,map_zero]
      ring
    map_smul' := by
      intro r v
      funext i
      obtain ⟨a,l,hl⟩ := hp i
      change p (r • v) i-p 0 i = r*(p v i-p 0 i)
      rw [hl,hl,hl,map_smul,map_zero]
      change a+r*l v-(a+0)=r*(a+l v-(a+0))
      ring }
  map_vadd' := by
    intro v w
    funext i
    obtain ⟨a,l,hl⟩ := hp i
    change p (w+v) i = (p w i-p 0 i)+p v i
    rw [hl,hl,hl,hl,map_add,map_zero]
    ring

/-- This equivalence has exactly the original underlying permutation, without
changing its carrier or assuming an affine-group target. -/
noncomputable def affineEquivOfCoordinateAffine (p : Equiv.Perm (I → F))
    (hp : ∀ i, ∃ a : F, ∃ l : (I → F) →ₗ[F] F, ∀ v, p v i = a + l v) :
    (I → F) ≃ᵃ[F] (I → F) :=
  AffineEquiv.ofBijective (φ := affineMapOfCoordinateAffine p hp) p.bijective

@[simp] theorem affineEquivOfCoordinateAffine_apply (p : Equiv.Perm (I → F))
    (hp : ∀ i, ∃ a : F, ∃ l : (I → F) →ₗ[F] F, ∀ v, p v i = a+l v)
    (v : I → F) : affineEquivOfCoordinateAffine p hp v = p v := rfl

end Atlas.LinearAlgebra
