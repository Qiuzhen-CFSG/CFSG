module

public import Theory.SpecificGroups.Triality.SimplyConnectedModel.GraphField
public import Theory.SpecificGroups.Triality.Model.QTKEParameters
public import Mathlib.FieldTheory.IsAlgClosed.Basic

/-!
# Finite-field descent of the concrete Spin triality matrices

Choose an embedding of the actual cubic coefficient field GF(2^(3*n)) into
an algebraically closed field of characteristic two. Its image is exactly
the roots of X^(2^(3*n)) - X. The cube formula for the literal Spin graph-field
action therefore puts every natural matrix entry of a fixed point in this
image, including n = 1. Entrywise descent gives a faithful matrix representation
of the full fixed group over that exact finite field.

This is coordinate descent, not a claim that every descended matrix is a
word in rational root elements. That generation result and the comparison
with the Geck matrices remain separate obligations.

Sources: GLS3, Remarks 2.2.5 and Theorem 2.2.6, and the even orthogonal
matrix realization in §2.7 (`refs/KGroup/GLS3/chapter2.tex`).
-/

@[expose] public section

open Triality.Standard Triality.SimplyConnected
open Theory.AlgebraicGroup

noncomputable section
namespace Triality.BinaryDegree.CarrierTransport
variable (k : Type*) [Field k] [IsAlgClosed k] [CharP k 2]

/-- Embed the genuine cubic coefficient field into the algebraic closure. -/
def coefficientEmbedding (n : ℕ) (hn : 0 < n) :
    ExtensionField (binaryParameters n hn) →+* k := by
  letI : Algebra (ZMod 2) (ExtensionField (binaryParameters n hn)) := ZMod.algebra _ 2
  letI : Algebra (ZMod 2) k := ZMod.algebra _ 2
  exact (IsAlgClosed.lift (R := ZMod 2)
    (S := ExtensionField (binaryParameters n hn)) (M := k)).toRingHom

variable {k}

omit [IsAlgClosed k] [CharP k 2] in
/-- The finite-field image is exactly the fixed field of the cubic Frobenius. -/
theorem coefficient_mem_range_iff {n : ℕ} {hn : 0 < n}
    (f : ExtensionField (binaryParameters n hn) →+* k) (t : k) :
    t ∈ f.range ↔ t ^ (2 ^ (3 * n)) = t := by
  let K := ExtensionField (binaryParameters n hn)
  let : Fintype K := Fintype.ofFinite K
  have hcard : Fintype.card K = 2 ^ (3 * n) := by
    rw [← Nat.card_eq_fintype_card]
    exact GaloisField.card 2 (3 * n) (by omega)
  constructor
  · rintro ⟨s, rfl⟩
    rw [← map_pow, ← hcard, FiniteField.pow_card]
  · intro ht
    let p : Polynomial K := Polynomial.X ^ (2 ^ (3 * n)) - Polynomial.X
    have hp : p ≠ 0 := FiniteField.X_pow_card_pow_sub_X_ne_zero _ (by omega) (by decide)
    have hs : p.Splits := by
      rw [show p = Polynomial.X ^ Fintype.card K - Polynomial.X by rw [hcard]]
      apply Polynomial.splits_iff_card_roots.mpr
      rw [FiniteField.roots_X_pow_card_sub_X, Finset.card_val, Finset.card_univ,
        FiniteField.X_pow_card_sub_X_natDegree_eq _ Fintype.one_lt_card]
    apply hs.mem_range_of_isRoot hp
    simp [p, Polynomial.IsRoot, ht]

/-- Ordinary Frobenius fixation is equivalent to rationality of all natural entries. -/
theorem frobenius_fixed_iff_coordinates {n : ℕ} {hn : 0 < n}
    (f : ExtensionField (binaryParameters n hn) →+* k) (g : Points k) :
    frobeniusPointAut k (3 * n) g = g ↔
      ∀ i j, naturalMatrix k g i j ∈ f.range := by
  constructor
  · intro hg i j
    apply (coefficient_mem_range_iff f _).mpr
    rw [← naturalMatrix_frobenius, hg]
  · intro hg
    apply naturalMatrix_injective k
    funext i j
    rw [naturalMatrix_frobenius]
    exact (coefficient_mem_range_iff f _).mp (hg i j)

/-- The actual graph-field cube forces all fixed-point matrix entries into GF(q³). -/
theorem fixed_coordinates_mem_range {n : ℕ} {hn : 0 < n}
    (f : ExtensionField (binaryParameters n hn) →+* k)
    (g : GraphField.FixedGroup k n) (i j : Fin 4 ⊕ Fin 4) :
    naturalMatrix k g.val i j ∈ f.range := by
  apply (frobenius_fixed_iff_coordinates f g.val).mp
    (GraphField.fixedSubgroup_le_frobeniusFixedSubgroup k n g.property)

/-- The faithful natural matrix, with matrix rather than pointwise multiplication. -/
abbrev spinMatrix (g : Points k) : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) k :=
  naturalMatrix k g

omit [CharP k 2] in
/-- Identification with the standard basis-to-matrix construction. -/
theorem spinMatrix_eq_toMatrix (g : Points k) :
    spinMatrix g = LinearMap.toMatrix (hyperbolicBasis k) (hyperbolicBasis k)
      (naturalAction k g).val.toLinearMap := by
  ext i j
  exact (LinearMap.toMatrix_apply _ _ _ _ _).symm

omit [CharP k 2] in
/-- The natural matrix of the identity. -/
theorem spinMatrix_one : spinMatrix (1 : Points k) = 1 := by
  rw [spinMatrix_eq_toMatrix]
  rw [map_one]
  exact LinearMap.toMatrix_one (hyperbolicBasis k)

omit [CharP k 2] in
/-- The natural action uses ordinary matrix multiplication. -/
theorem spinMatrix_mul (g h : Points k) :
    spinMatrix (g * h) = spinMatrix g * spinMatrix h := by
  simp only [spinMatrix_eq_toMatrix]
  rw [map_mul]
  exact LinearMap.toMatrix_mul (hyperbolicBasis k)
    (naturalAction k g).val.toLinearMap (naturalAction k h).val.toLinearMap

/-- Descend each entry of a graph-field fixed point to the specified finite field. -/
def finiteMatrix {n : ℕ} {hn : 0 < n}
    (f : ExtensionField (binaryParameters n hn) →+* k)
    (g : GraphField.FixedGroup k n) :
    Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) (ExtensionField (binaryParameters n hn)) :=
  fun i j => (fixed_coordinates_mem_range f g i j).choose

/-- Extension of scalars recovers the literal natural Spin matrix. -/
theorem map_finiteMatrix {n : ℕ} {hn : 0 < n}
    (f : ExtensionField (binaryParameters n hn) →+* k)
    (g : GraphField.FixedGroup k n) : (finiteMatrix f g).map f = spinMatrix g.val := by
  ext i j
  exact (fixed_coordinates_mem_range f g i j).choose_spec

/-- No Spin point is lost in coordinate descent. -/
theorem finiteMatrix_injective {n : ℕ} {hn : 0 < n}
    (f : ExtensionField (binaryParameters n hn) →+* k) :
    Function.Injective (finiteMatrix f) := by
  intro g h he
  apply Subtype.ext
  apply naturalMatrix_injective k
  change spinMatrix g.val = spinMatrix h.val
  rw [← map_finiteMatrix f g, ← map_finiteMatrix f h, he]

/-- Coordinate descent preserves the identity matrix. -/
theorem finiteMatrix_one {n : ℕ} {hn : 0 < n}
    (f : ExtensionField (binaryParameters n hn) →+* k) : finiteMatrix f 1 = 1 := by
  apply Matrix.map_injective f.injective
  dsimp only
  rw [map_finiteMatrix, Matrix.map_one, Subgroup.coe_one, spinMatrix_one]
  all_goals simp

/-- Coordinate descent preserves matrix multiplication. -/
theorem finiteMatrix_mul {n : ℕ} {hn : 0 < n}
    (f : ExtensionField (binaryParameters n hn) →+* k)
    (g h : GraphField.FixedGroup k n) :
    finiteMatrix f (g * h) = finiteMatrix f g * finiteMatrix f h := by
  apply Matrix.map_injective f.injective
  dsimp only
  rw [map_finiteMatrix, Matrix.map_mul, map_finiteMatrix, map_finiteMatrix,
    Subgroup.coe_mul, spinMatrix_mul]

/-- A faithful representation of the full Spin fixed group over the cubic field. -/
def finiteNaturalRepresentation {n : ℕ} {hn : 0 < n}
    (f : ExtensionField (binaryParameters n hn) →+* k) :
    GraphField.FixedGroup k n →*
      (Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4)
        (ExtensionField (binaryParameters n hn)))ˣ where
  toFun g :=
    { val := finiteMatrix f g
      inv := finiteMatrix f g⁻¹
      val_inv := by rw [← finiteMatrix_mul, mul_inv_cancel, finiteMatrix_one]
      inv_val := by rw [← finiteMatrix_mul, inv_mul_cancel, finiteMatrix_one] }
  map_one' := Units.ext (finiteMatrix_one f)
  map_mul' g h := Units.ext (finiteMatrix_mul f g h)

/-- Faithfulness follows from the actual characteristic-two Spin natural action. -/
theorem finiteNaturalRepresentation_injective {n : ℕ} {hn : 0 < n}
    (f : ExtensionField (binaryParameters n hn) →+* k) :
    Function.Injective (finiteNaturalRepresentation f) := by
  intro g h he
  exact finiteMatrix_injective f (congrArg Units.val he)

end Triality.BinaryDegree.CarrierTransport
