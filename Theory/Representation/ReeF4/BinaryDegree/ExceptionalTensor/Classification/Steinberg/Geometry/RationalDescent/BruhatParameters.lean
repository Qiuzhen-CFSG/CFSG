module

public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.RationalDescent.BruhatParameters.MatrixCoordinates
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.RationalDescent.BruhatParameters.TriangularMatrices
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.RationalDescent.BruhatParameters.RestrictedCells
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.RationalDescent.BruhatParameters.UnipotentRecovery

/-!
# Rational parameters in actual F4 Bruhat cells

The ordered root, coroot and prime-field Weyl words are literal elements of
F4Chevalley.Carrier. Removing the Weyl word preserves rational matrix entries.
The triangular extraction theorem recovers the entries of the two unipotent
factors and the nonzero torus diagonal; the explicit inverse Cartan monomials
then recover the four direct coroot units. Word transport supplies a finite
split-group word with exactly the same mapped parameters.

In characteristic two, the literal Bruhat coverage and root-matrix recovery
theorems discharge all geometric premises. Every carrier point whose presented
coordinates lie in the coefficient field image has such a cell expression
with root parameters and coroot units from that field. The two positive root
orderings may be prescribed. The exported coefficient-field parameters and
`splitEmbedding_cell` give the explicit word needed by the parent membership
assembly.

Source: Steinberg, *Lectures on Chevalley Groups*, Theorem 7(b) and its third
corollary, pp. 64–67 (`refs/KGroup/GLS3/Chapter2St1.tex`, lines 1017–1064).
-/

public section

open scoped BigOperators
open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
open RootPairing.IntegralGeckConstruction
namespace ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.RationalDescent.BruhatParameters
variable {F : Type*} [Field F] [IsAlgClosed F]

/-- The literal cell's parameters descend once its two actual root products
have their triangular matrices and the Cartan-column recovery property. -/
theorem cell_parameters_mem_range_of_triangular {m n n' N : ℕ}
    (f : CoefficientField m →+* F)
    (p : Fin n → F4Chevalley.Root) (q : Fin n' → F4Chevalley.Root)
    (a : Fin n → F) (t : Fin 4 → Fˣ) (b : Fin n' → F) (l : List (Fin 4))
    (e : Fin N ≃ F4Chevalley.BasisIndex)
    (hL : ∀ i j, i < j → (pointMatrix (rootProduct p a)).val (e i) (e j) = 0)
    (hU : ∀ i j, j < i → (pointMatrix (rootProduct q b)).val (e i) (e j) = 0)
    (hLd : ∀ i, (pointMatrix (rootProduct p a)).val (e i) (e i) = 1)
    (hUd : ∀ i, (pointMatrix (rootProduct q b)).val (e i) (e i) = 1)
    (hp : (∀ i j, (pointMatrix (rootProduct p a)).val i j ∈ f.range) →
      ∀ i, a i ∈ f.range)
    (hq : (∀ i j, (pointMatrix (rootProduct q b)).val i j ∈ f.range) →
      ∀ i, b i ∈ f.range)
    (hx : ∀ c, (cell p q a t b l).val c ∈ f.range) :
    (∀ i, a i ∈ f.range) ∧ (∀ i, t i ∈ Set.range (Units.map f.toMonoidHom)) ∧
      (∀ i, b i ∈ f.range) := by
  classical
  let L := (pointMatrix (rootProduct p a)).val.submatrix e e
  let U := (pointMatrix (rootProduct q b)).val.submatrix e e
  let d (i : Fin N) : F := F4Chevalley.basisTorusUnit t⁻¹ (e i)
  have heq : L * Matrix.diagonal d * U =
      (pointMatrix (rootProduct p a * corootProduct t * rootProduct q b)).val.submatrix e e := by
    rw [map_mul, map_mul, Units.val_mul, Units.val_mul, pointMatrix_corootProduct]
    change L * Matrix.diagonal d * U =
      ((pointMatrix (rootProduct p a)).val *
        Matrix.diagonal (fun i => (F4Chevalley.basisTorusUnit t⁻¹ i : F)) *
        (pointMatrix (rootProduct q b)).val).submatrix e e
    rw [← Matrix.submatrix_mul_equiv _ _ e e e,
      ← Matrix.submatrix_mul_equiv _ _ e e e, Matrix.submatrix_diagonal_equiv]
    rfl
  have hA : ∀ i j, (L * Matrix.diagonal d * U) i j ∈ f.fieldRange := by
    have h := right_weyl_inv_entries_mem_range f (cell p q a t b l) l hx
    simp only [cell, mul_inv_cancel_right] at h
    intro i j
    rw [heq]
    exact h (e i) (e j)
  obtain ⟨hLrat, hdrat, hUrat⟩ := entries_mem_of_triangular_factorization f.fieldRange L U d
    hL hU hLd hUd (fun i => Units.ne_zero _) hA
  have hL' : ∀ i j, (pointMatrix (rootProduct p a)).val i j ∈ f.range := by
    intro i j
    simpa only [L, Matrix.submatrix_apply, Equiv.apply_symm_apply, RingHom.mem_fieldRange, RingHom.mem_range] using
      hLrat (e.symm i) (e.symm j)
  have hU' : ∀ i j, (pointMatrix (rootProduct q b)).val i j ∈ f.range := by
    intro i j
    simpa only [U, Matrix.submatrix_apply, Equiv.apply_symm_apply, RingHom.mem_fieldRange, RingHom.mem_range] using
      hUrat (e.symm i) (e.symm j)
  refine ⟨hp hL', ?_, hq hU'⟩
  intro i
  apply unit_mem_range_of_value f
  rw [corootProduct_recover]
  apply f.range.prod_mem
  intro j _
  apply f.range.pow_mem
  rw [corootProduct_diagonal]
  simpa only [d, Equiv.apply_symm_apply, RingHom.mem_fieldRange, RingHom.mem_range] using
    hdrat (e.symm (Sum.inr (typeF4SimpleRootIndex j)))

variable [CharP F 2]
noncomputable local instance : InvolutiveNeg F4Chevalley.Root := typeF4RootPairing.indexNeg

/-- Every parameter of a literal opposite-root cell descends from its presented
coordinates. Both unipotent triangularity and parameter recovery are proved
for the actual root matrices, with no additional normal-form premise. -/
theorem cell_parameters_mem_range {m : ℕ} (f : CoefficientField m →+* F)
    (o o' : PositiveOrdering) (a b : Fin 24 → F) (t : Fin 4 → Fˣ) (l : List (Fin 4))
    (hx : ∀ c, (cell (fun i => (o i).val) (fun i => -(o' i).val) a t b l).val c ∈ f.range) :
    (∀ i, a i ∈ f.range) ∧ (∀ i, t i ∈ Set.range (Units.map f.toMonoidHom)) ∧
      (∀ i, b i ∈ f.range) :=
  cell_parameters_mem_range_of_triangular f _ _ a t b l unipotentBasisOrder
    (positive_rootProduct_lower o a) (negative_rootProduct_upper o' b)
    (positive_rootProduct_diagonal o a) (negative_rootProduct_diagonal o' b)
    (positive_parameters_mem_range f o a) (negative_parameters_mem_range f o' b) hx

/-- Bruhat coverage and rational recovery on every point of the actual closed
root-generated carrier. The Weyl factor remains a literal finite product of
simple normalizer words at parameter one. -/
theorem exists_cell_parameters_mem_range {m : ℕ} (f : CoefficientField m →+* F)
    (o o' : PositiveOrdering) (x : Variety.Point (F4Chevalley.Carrier (k := F)))
    (hx : ∀ c, x.val c ∈ f.range) :
    ∃ (a b : Fin 24 → F) (t : Fin 4 → Fˣ) (l : List (Fin 4)),
      x = cell (fun i => (o i).val) (fun i => -(o' i).val) a t b l ∧
      (∀ i, a i ∈ f.range) ∧ (∀ i, t i ∈ Set.range (Units.map f.toMonoidHom)) ∧
        (∀ i, b i ∈ f.range) := by
  obtain ⟨a, b, t, l, hcell⟩ := exists_cell_of_positiveOrderings o o' x
  exact ⟨a, b, t, l, hcell, cell_parameters_mem_range f o o' a b t l (hcell ▸ hx)⟩

/-- A rational carrier point has explicit coefficient-field root parameters
and unit parameters. Together with `splitEmbedding_cell`, this equation lets
the parent construct its finite split-group preimage as the same literal word. -/
theorem exists_cell_over_coefficientField {m : ℕ} (f : CoefficientField m →+* F)
    (o o' : PositiveOrdering) (x : Variety.Point (F4Chevalley.Carrier (k := F)))
    (hx : ∀ c, x.val c ∈ f.range) :
    ∃ (a b : Fin 24 → CoefficientField m) (t : Fin 4 → (CoefficientField m)ˣ)
      (l : List (Fin 4)),
      x = cell (fun i => (o i).val) (fun i => -(o' i).val)
        (f ∘ a) (fun i => Units.map f.toMonoidHom (t i)) (f ∘ b) l := by
  obtain ⟨a, b, t, l, hcell, ha, ht, hb⟩ := exists_cell_parameters_mem_range f o o' x hx
  choose a' ha' using ha
  choose t' ht' using ht
  choose b' hb' using hb
  refine ⟨a', b', t', l, ?_⟩
  have ea : f ∘ a' = a := funext ha'
  have et : (fun i => Units.map f.toMonoidHom (t' i)) = t := funext ht'
  have eb : f ∘ b' = b := funext hb'
  rw [ea, et, eb]
  exact hcell

/-- Two genuine positive orderings cover all rational carrier points by cells
with coefficient-field parameters. This supplies the orderings as well as the
parameters, without assuming finite split-group membership. -/
theorem exists_positiveOrderings_rational_cell_cover {m : ℕ}
    (f : CoefficientField m →+* F) :
    ∃ o o' : PositiveOrdering,
      ∀ x : Variety.Point (F4Chevalley.Carrier (k := F)),
        (∀ c, x.val c ∈ f.range) →
        ∃ (a b : Fin 24 → CoefficientField m) (t : Fin 4 → (CoefficientField m)ˣ)
          (l : List (Fin 4)),
          x = cell (fun i => (o i).val) (fun i => -(o' i).val)
            (f ∘ a) (fun i => Units.map f.toMonoidHom (t i)) (f ∘ b) l := by
  obtain ⟨o, o', _⟩ := exists_positiveOrderings_cell_cover (F := F)
  exact ⟨o, o', exists_cell_over_coefficientField f o o'⟩

end ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.RationalDescent.BruhatParameters
