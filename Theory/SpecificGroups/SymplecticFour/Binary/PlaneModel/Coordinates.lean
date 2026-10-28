module

public import Theory.SpecificGroups.SymplecticFour.Binary.FieldTransport
public import Mathlib.Data.Fintype.Perm

/-!
# Binary plane-parabolic matrix coordinates

Label the four actual vectors of F₂² by the binary digits of `Fin 4`.
Every permutation `p` of these vectors is affine: its translation is `p(0)`
and its linear part has columns `p(1) + p(0)` and `p(2) + p(0)`.
For a binary scalar `t`, put
`U = [[a, a+c+t], [a+c+t, c]]`, where `(a,c) = p(0)`.
The associated symplectic matrix is `[[A, U A⁻ᵀ], [0, A⁻ᵀ]]`.
Here `t` is the image of zero under a permutation of `Fin 2`.

The finite proofs below are kernel reductions against these explicit formulas.
They establish the symplectic equation, multiplication, faithfulness, and
coverage of all upper-block symplectic matrices. Coverage uses the exact
block equations, rather than an order comparison. No exceptional isomorphism
with a degree-six permutation group is needed.

Source: the binary plane local group in Aschbacher--Smith F.1.12(I)(2),
printed pp.262–264. The bridge from this stabilizer to `LᵢS` is external.
-/

@[expose] public section
open Matrix
namespace Theory.SpecificGroups.SymplecticFour.Binary.PlaneModel
/-- A binary two-by-two block. -/
abbrev BMat := Matrix (Fin 2) (Fin 2) (ZMod 2)
/-- Binary digits, in the ordered basis of the isotropic plane. -/
def vec (i : Fin 4) : Fin 2 → ZMod 2 := ![(i.val % 2 : ℕ), (i.val / 2 : ℕ)]
/-- Linear part of the affine permutation of the four actual vectors. -/
def lin (p : Equiv.Perm (Fin 4)) : BMat :=
  Matrix.of ![![(vec (p 1) 0 + vec (p 0) 0), (vec (p 2) 0 + vec (p 0) 0)],
    ![(vec (p 1) 1 + vec (p 0) 1), (vec (p 2) 1 + vec (p 0) 1)]]
/-- Inverse transpose for a binary invertible two-by-two matrix. -/
def dual (A : BMat) : BMat := !![A 1 1, A 1 0; A 0 1, A 0 0]
/-- The equivariant binary splitting of the symmetric matrices. -/
def symmPart (s : Equiv.Perm (Fin 2)) (p : Equiv.Perm (Fin 4)) : BMat :=
  let v := vec (p 0)
  let t : ZMod 2 := (s 0).val
  !![v 0, v 0 + v 1 + t; v 0 + v 1 + t, v 1]
/-- The actual four-by-four matrix associated to the product coordinates. -/
def modelMatrix (s : Equiv.Perm (Fin 2)) (p : Equiv.Perm (Fin 4)) :
    Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod 2) :=
  fromBlocks (lin p) (symmPart s p * dual (lin p)) 0 (dual (lin p))
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem modelMatrix_symplectic : ∀ s p, (modelMatrix s p) ∈ Matrix.symplecticGroup (Fin 2) (ZMod 2) := by
  intro s p
  rw [modelMatrix, SymplecticGroup.fromBlocks_mem_iff]
  revert s p
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem modelMatrix_mul : ∀ s p t q, modelMatrix (s * t) (p * q) = modelMatrix s p * modelMatrix t q := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem modelMatrix_injective : ∀ s p t q, modelMatrix s p = modelMatrix t q → s = t ∧ p = q := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem modelMatrix_surjective : ∀ A B D : BMat, Bᵀ * D = Dᵀ * B → Aᵀ * D = 1 →
    ∃ s p, modelMatrix s p = fromBlocks A B 0 D := by
  decide +kernel
end Theory.SpecificGroups.SymplecticFour.Binary.PlaneModel
