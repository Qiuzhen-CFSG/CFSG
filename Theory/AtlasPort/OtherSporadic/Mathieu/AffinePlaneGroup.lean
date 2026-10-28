/-
Copyright (c) 2026 ATLAS contributors. All rights reserved.
Released under the ATLAS Research and Attribution License 1.0; see LICENSES/ATLAS.txt.
Authors: Gerald Höhn, ATLAS contributors
-/
module

public import Theory.AtlasPort.OtherSporadic.Mathieu.AffineRows
public import Mathlib.Algebra.Group.Equiv.TypeTags

/-!
# AffinePlaneGroup

The affine group of the two-dimensional binary plane is multiplicatively equivalent to
all permutations of its four points. Every point permutation has a unique translation
and linear part, giving an explicit bijective action homomorphism.

Source: `Atlas/Mathieu/AffinePlaneGroup.lean`, Gerald Höhn (ATLAS), revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0 with public module imports and exposed definitions
so that the original downstream coordinate reductions remain available.
Proof syntax and simplifier arguments are adapted without changing public statements.
-/

@[expose] public section

namespace Atlas.Codes

def planeLinearAction : KIsometry →* MulAut (Multiplicative K) where
  toFun L := L.toAddEquiv.toMultiplicative
  map_one' := by apply MulEquiv.ext; intro z; rfl
  map_mul' _ _ := by apply MulEquiv.ext; intro z; rfl

abbrev AffinePlaneGroup := Multiplicative K ⋊[planeLinearAction] KIsometry

def affinePlaneHom : AffinePlaneGroup →* Equiv.Perm K where
  toFun x := x.right.toEquiv.trans (Equiv.addRight x.left.toAdd)
  map_one' := by apply Equiv.ext; intro z; change z+0=z; exact add_zero z
  map_mul' x y := by
    apply Equiv.ext
    intro z
    change (x.right * y.right) z + (x.left.toAdd + x.right y.left.toAdd) =
      x.right (y.right z + y.left.toAdd) + x.left.toAdd
    rw [map_add]
    simp only [LinearEquiv.mul_apply]
    abel

theorem affinePlaneHom_apply (x : AffinePlaneGroup) (z : K) :
    affinePlaneHom x z = x.right z + x.left.toAdd := rfl

theorem affinePlaneHom_bijective : Function.Bijective affinePlaneHom := by
  constructor
  · intro x y he
    have ht := Equiv.congr_fun he 0
    simp only [affinePlaneHom_apply,map_zero,zero_add] at ht
    have hL : x.right = y.right := by
      apply LinearEquiv.ext
      intro z
      have h := Equiv.congr_fun he z
      simp only [affinePlaneHom_apply,ht] at h
      exact add_right_cancel h
    exact SemidirectProduct.ext ht hL
  · intro e
    refine ⟨⟨Multiplicative.ofAdd (e 0),rowLinearPart e⟩,?_⟩
    apply Equiv.ext
    intro z
    exact row_affine_formula e z

noncomputable def affinePlaneEquiv : AffinePlaneGroup ≃* Equiv.Perm K :=
  MulEquiv.ofBijective affinePlaneHom affinePlaneHom_bijective

end Atlas.Codes
