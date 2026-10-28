/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Conway/SextetReflection.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.OtherSporadic.Lattices.LeechRationalExtension
/-!
Explicit sextet and tetrad isometries of the integral Leech lattice.
Coordinate identities and the retained lattice generators certify the isometry operations.

Source: Gerald Höhn, `Atlas/Conway/SextetReflection.lean`, ATLAS revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted to CFSG Lean 4.33.0 with public imports and exposed definition bodies,
preserving the source namespaces and cross-module coordinate reductions.
-/

@[expose] public section

noncomputable section
namespace Atlas.Conway
open Atlas.Codes Atlas.Lattices
open scoped BigOperators

def sextetBlockSign (i : HexIndex) : ℚ := if i = (2,1) then -1 else 1

theorem sextetBlockSign_sq (i : HexIndex) : sextetBlockSign i * sextetBlockSign i = 1 := by
  unfold sextetBlockSign
  split_ifs <;> norm_num

/-- The prescribed R on five tetrads and -R on the retained last tetrad. -/
def sextetReflection : RationalCoordinates →ₗ[ℚ] RationalCoordinates where
  toFun x := fun p => sextetBlockSign p.1 * (x p - (∑ k : Tetrad, x (p.1,k)) / 2)
  map_add' x y := by
    ext p
    simp only [Pi.add_apply,Finset.sum_add_distrib]
    ring
  map_smul' r x := by
    ext p
    simp only [Pi.smul_apply,smul_eq_mul,← Finset.mul_sum,RingHom.id_apply]
    ring

theorem sextetReflection_apply (x : RationalCoordinates) (i : HexIndex) (k : Tetrad) :
    sextetReflection x (i,k) = sextetBlockSign i * (x (i,k) - (∑ j : Tetrad, x (i,j)) / 2) := rfl

theorem sextetReflection_blockSum (x : RationalCoordinates) (i : HexIndex) :
    (∑ k : Tetrad, sextetReflection x (i,k)) = -sextetBlockSign i * ∑ k : Tetrad, x (i,k) := by
  simp only [sextetReflection_apply,← Finset.mul_sum,Finset.sum_sub_distrib]
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  ring

theorem sextetReflection_involutive : Function.Involutive sextetReflection := by
  intro x
  ext ⟨i,k⟩
  rw [sextetReflection_apply,sextetReflection_apply,sextetReflection_blockSum]
  unfold sextetBlockSign
  split_ifs <;> ring

theorem sextetReflection_blockDot (x y : RationalCoordinates) (i : HexIndex) :
    (∑ k : Tetrad, sextetReflection x (i,k) * sextetReflection y (i,k)) =
      ∑ k : Tetrad, x (i,k) * y (i,k) := by
  have he (k : Tetrad) : sextetReflection x (i,k) * sextetReflection y (i,k) =
      x (i,k) * y (i,k) - x (i,k) * (∑ j : Tetrad, y (i,j)) / 2 -
      y (i,k) * (∑ j : Tetrad, x (i,j)) / 2 +
      (∑ j : Tetrad, x (i,j)) * (∑ j : Tetrad, y (i,j)) / 4 := by
    rw [sextetReflection_apply,sextetReflection_apply]
    calc
      _ = (sextetBlockSign i * sextetBlockSign i) *
          ((x (i,k) - (∑ j : Tetrad, x (i,j)) / 2) *
           (y (i,k) - (∑ j : Tetrad, y (i,j)) / 2)) := by ring
      _ = _ := by rw [sextetBlockSign_sq]; ring
  simp only [he,Finset.sum_add_distrib,Finset.sum_sub_distrib,
    ← Finset.sum_div,← Finset.sum_mul,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  ring

theorem sextetReflection_form (x y : RationalCoordinates) :
    rationalForm (sextetReflection x) (sextetReflection y) = rationalForm x y := by
  change (1/8 : ℚ) * (∑ p : Omega, sextetReflection x p * sextetReflection y p) =
    (1/8 : ℚ) * (∑ p : Omega, x p * y p)
  simp only [Fintype.sum_prod_type,sextetReflection_blockDot]

def sextetReflectionEquiv : RationalCoordinates ≃ₗ[ℚ] RationalCoordinates :=
  { sextetReflection with
    invFun := sextetReflection
    left_inv := sextetReflection_involutive
    right_inv := sextetReflection_involutive }

end Atlas.Conway
