module

public import Theory.AlgebraicGroup.RootSystems.SplitQuadraticConjugationGeneration
public import Mathlib.LinearAlgebra.CliffordAlgebra.SpinGroup

/-!
# Split orthogonal transformations are generated in the Lipschitz group

For a finite-dimensional split quadratic space over an algebraically closed
field, every linear isometry is a product of the characteristic-free
conjugation symmetries supplied by `split_conjugation_factorization`.  Each
anisotropic symmetry is represented by the corresponding invertible Clifford
vector, and Mathlib's generated `lipschitzGroup` contains these vectors by
construction.  Multiplying the units therefore gives one Lipschitz element
whose ordinary Clifford conjugation realizes the original isometry on all
embedded vectors.

The proof is deliberately phrased with `lipschitzGroup`, rather than with a
separately defined normalizer.  It only uses the inverse of the anisotropic
quadratic value supplied by the subtype witness; in particular it never
introduces `Invertible (2 : k)`.  Thus the packaging remains valid in
characteristic two, where the preceding split factorization also applies.
The list-fold orientation follows the source theorem: the rightmost
conjugation symmetry acts first, and Clifford multiplication is arranged in
the same order.
-/

universe u

open CliffordAlgebra

namespace Theory.AlgebraicGroup

variable {k V : Type u} [Field k] [IsAlgClosed k]
variable [AddCommGroup V] [Module k V] [FiniteDimensional k V]
variable {Q : QuadraticForm k V}

private noncomputable def cliffordVectorUnit
    (a : {v : V // Q v ≠ 0}) : (CliffordAlgebra Q)ˣ := by
  letI : Invertible (Q a.1) := invertibleOfNonzero a.2
  letI : Invertible (CliffordAlgebra.ι Q a.1) :=
    CliffordAlgebra.invertibleιOfInvertible Q a.1
  exact unitOfInvertible (CliffordAlgebra.ι Q a.1)

omit [IsAlgClosed k] [FiniteDimensional k V] in
private lemma cliffordVectorUnit_coe
    (a : {v : V // Q v ≠ 0}) :
    (cliffordVectorUnit a : CliffordAlgebra Q) = CliffordAlgebra.ι Q a.1 := by
  simp [cliffordVectorUnit]

omit [IsAlgClosed k] [FiniteDimensional k V] in
private lemma cliffordVectorUnit_mem_lipschitzGroup
    (a : {v : V // Q v ≠ 0}) :
    cliffordVectorUnit a ∈ lipschitzGroup Q := by
  apply Subgroup.subset_closure
  exact ⟨a.1, cliffordVectorUnit_coe a⟩

omit [IsAlgClosed k] [FiniteDimensional k V] in
private lemma cliffordVectorUnit_conjugation
    (a : {v : V // Q v ≠ 0}) (x : V) :
    (cliffordVectorUnit a : CliffordAlgebra Q) * CliffordAlgebra.ι Q x *
        (↑((cliffordVectorUnit a)⁻¹) : CliffordAlgebra Q) =
      CliffordAlgebra.ι Q (conjugationSymmetry Q a.1 a.2 x) := by
  let _ : Invertible (Q a.1) := invertibleOfNonzero a.2
  let _ : Invertible (CliffordAlgebra.ι Q a.1) :=
    CliffordAlgebra.invertibleιOfInvertible Q a.1
  rw [cliffordVectorUnit_coe]
  change CliffordAlgebra.ι Q a.1 * CliffordAlgebra.ι Q x *
      ⅟(CliffordAlgebra.ι Q a.1) = _
  rw [CliffordAlgebra.ι_mul_ι_mul_invOf_ι]
  simp only [conjugationSymmetry_apply, invOf_eq_inv]

omit [IsAlgClosed k] [FiniteDimensional k V] in
private lemma cliffordVectorUnits_prod_mem_lipschitzGroup
    (as : List {v : V // Q v ≠ 0}) :
    (as.map cliffordVectorUnit).prod ∈ lipschitzGroup Q := by
  induction as with
  | nil => simp
  | cons a as ih =>
      simpa using (lipschitzGroup Q).mul_mem
        (cliffordVectorUnit_mem_lipschitzGroup a) ih

omit [IsAlgClosed k] [FiniteDimensional k V] in
private lemma cliffordVectorUnits_prod_conjugation
    (as : List {v : V // Q v ≠ 0}) (x : V) :
    CliffordAlgebra.ι Q
        (as.foldr (fun a w => conjugationSymmetry Q a.1 a.2 w) x) =
      ((as.map cliffordVectorUnit).prod : CliffordAlgebra Q) *
        CliffordAlgebra.ι Q x *
        (↑((as.map cliffordVectorUnit).prod⁻¹) : CliffordAlgebra Q) := by
  induction as with
  | nil => simp
  | cons a as ih =>
      rw [List.foldr_cons, List.map_cons, List.prod_cons]
      rw [← cliffordVectorUnit_conjugation, ih]
      simp only [Units.val_mul, mul_inv_rev]
      simp only [mul_assoc]

/-- Every split quadratic isometry is realized by ordinary Clifford
conjugation with a unit in Mathlib's generated Lipschitz subgroup. -/
public theorem split_orthogonal_lipschitz_generation
    (s : SplitQuadraticForm Q) (f : V ≃ₗ[k] V)
    (hf : ∀ v, Q (f v) = Q v) :
    ∃ y : (CliffordAlgebra Q)ˣ,
      y ∈ lipschitzGroup Q ∧
        ∀ v, CliffordAlgebra.ι Q (f v) =
          (y : CliffordAlgebra Q) * CliffordAlgebra.ι Q v *
            (↑(y⁻¹) : CliffordAlgebra Q) := by
  obtain ⟨as, has⟩ := split_conjugation_factorization s f hf
  have has' : ∀ v, f v =
      as.foldr (fun a w => conjugationSymmetry Q a.1 a.2 w) v := by
    intro v
    simpa only [conjugationSymmetry_apply] using has v
  refine ⟨(as.map cliffordVectorUnit).prod,
    cliffordVectorUnits_prod_mem_lipschitzGroup as, ?_⟩
  intro v
  rw [has']
  exact cliffordVectorUnits_prod_conjugation as v

end Theory.AlgebraicGroup
