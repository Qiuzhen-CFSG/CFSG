module

public import Theory.AlgebraicGroup.RootSystems.SplitCliffordDicksonParity
public import Theory.AlgebraicGroup.RootSystems.SplitOrthogonalLipschitzGeneration

/-!
# Split even Clifford normalizer factorization

This module factors an even Clifford unit whose ordinary conjugation preserves
the embedded vector space.  For a positive-rank split quadratic form over an
algebraically closed field, the induced linear automorphism of the vector
space preserves the quadratic form.  The characteristic-free split
orthogonal generation theorem therefore realizes it by a unit in Mathlib's
exact `lipschitzGroup`.

The split Dickson-parity theorem then shows that the quotient of the original
even unit by this Lipschitz implementer is still even.  Evaluating both
implementers on the inverse image of a vector proves directly that this
quotient commutes with every `CliffordAlgebra.ι Q v`.  The argument uses the
split exterior-algebra model only to prove injectivity of the Clifford vector
embedding and faithfulness of the scalar map.  It does not assume
`Invertible (2 : k)`, so the result includes characteristic two.

This is the lower factorization input for the split-even reverse inclusion in
the Lipschitz normalizer.  The centralizer-to-scalar step is deliberately left
to its separate lower module.
-/

universe u

open CliffordAlgebra MulAction
open scoped Pointwise

namespace Theory.AlgebraicGroup

variable {k V : Type u} [Field k] [IsAlgClosed k]
variable [AddCommGroup V] [Module k V] [FiniteDimensional k V]
variable {Q : QuadraticForm k V}

omit [IsAlgClosed k] in
private theorem iota_injective_of_split (s : SplitQuadraticForm Q) :
    Function.Injective (CliffordAlgebra.ι Q) := by
  intro v w hvw
  apply (ExteriorAlgebra.ι_leftInverse (R := k) (M := V)).injective
  let e : CliffordAlgebra Q ≃ₗ[k] ExteriorAlgebra k V :=
    CliffordAlgebra.changeFormEquiv s.bilinear_toQuadraticMap
  have hvw' := congrArg e hvw
  simpa [e, CliffordAlgebra.changeFormEquiv,
    CliffordAlgebra.changeForm_ι] using hvw'

private noncomputable def iotaEquivRange (s : SplitQuadraticForm Q) :
    V ≃ₗ[k] LinearMap.range (CliffordAlgebra.ι Q) :=
  LinearEquiv.ofInjective (CliffordAlgebra.ι Q) (iota_injective_of_split s)

private noncomputable def unitConjLinearEquiv (x : (CliffordAlgebra Q)ˣ) :
    CliffordAlgebra Q ≃ₗ[k] CliffordAlgebra Q :=
  DistribMulAction.toLinearEquiv k (CliffordAlgebra Q) (ConjAct.toConjAct x)

private noncomputable def unitConjRangeEquiv
    (x : (CliffordAlgebra Q)ˣ)
    (hx : ConjAct.toConjAct x • LinearMap.range (CliffordAlgebra.ι Q) =
      LinearMap.range (CliffordAlgebra.ι Q)) :
    LinearMap.range (CliffordAlgebra.ι Q) ≃ₗ[k]
      LinearMap.range (CliffordAlgebra.ι Q) :=
  (unitConjLinearEquiv x).submoduleMap
      (LinearMap.range (CliffordAlgebra.ι Q)) |>.trans
    (LinearEquiv.ofEq _ _ hx)

private noncomputable def inducedLinearEquiv
    (s : SplitQuadraticForm Q) (x : (CliffordAlgebra Q)ˣ)
    (hx : ConjAct.toConjAct x • LinearMap.range (CliffordAlgebra.ι Q) =
      LinearMap.range (CliffordAlgebra.ι Q)) :
    V ≃ₗ[k] V :=
  (iotaEquivRange s).trans <|
    (unitConjRangeEquiv x hx).trans (iotaEquivRange s).symm

omit [IsAlgClosed k] in
private lemma inducedLinearEquiv_spec
    (s : SplitQuadraticForm Q) (x : (CliffordAlgebra Q)ˣ)
    (hx : ConjAct.toConjAct x • LinearMap.range (CliffordAlgebra.ι Q) =
      LinearMap.range (CliffordAlgebra.ι Q)) (v : V) :
    CliffordAlgebra.ι Q (inducedLinearEquiv s x hx v) =
      (x : CliffordAlgebra Q) * CliffordAlgebra.ι Q v *
        (↑(x⁻¹) : CliffordAlgebra Q) := by
  change CliffordAlgebra.ι Q
      ((iotaEquivRange s).symm
        (unitConjRangeEquiv x hx (iotaEquivRange s v))) = _
  have hrange := congrArg Subtype.val
    ((iotaEquivRange s).apply_symm_apply
      (unitConjRangeEquiv x hx (iotaEquivRange s v)))
  change ((iotaEquivRange s)
    ((iotaEquivRange s).symm
      (unitConjRangeEquiv x hx (iotaEquivRange s v)))).val = _
  rw [hrange]
  rfl

omit [IsAlgClosed k] in
private lemma inducedLinearEquiv_preserves
    (s : SplitQuadraticForm Q) (x : (CliffordAlgebra Q)ˣ)
    (hx : ConjAct.toConjAct x • LinearMap.range (CliffordAlgebra.ι Q) =
      LinearMap.range (CliffordAlgebra.ι Q)) (v : V) :
    Q (inducedLinearEquiv s x hx v) = Q v := by
  have hs := congrArg (fun z : CliffordAlgebra Q => z * z)
    (inducedLinearEquiv_spec s x hx v)
  rw [CliffordAlgebra.ι_sq_scalar] at hs
  have hconj :
      ((x : CliffordAlgebra Q) * CliffordAlgebra.ι Q v * ↑(x⁻¹)) *
          ((x : CliffordAlgebra Q) * CliffordAlgebra.ι Q v * ↑(x⁻¹)) =
        algebraMap k (CliffordAlgebra Q) (Q v) := by
    calc
      ((x : CliffordAlgebra Q) * CliffordAlgebra.ι Q v * ↑(x⁻¹)) *
            ((x : CliffordAlgebra Q) * CliffordAlgebra.ι Q v * ↑(x⁻¹)) =
          (x : CliffordAlgebra Q) * CliffordAlgebra.ι Q v *
            (↑(x⁻¹) * (x : CliffordAlgebra Q)) *
            CliffordAlgebra.ι Q v * ↑(x⁻¹) := by noncomm_ring
      _ = (x : CliffordAlgebra Q) *
          (CliffordAlgebra.ι Q v * CliffordAlgebra.ι Q v) * ↑(x⁻¹) := by
        rw [Units.inv_mul]
        simp [mul_assoc]
      _ = (x : CliffordAlgebra Q) *
          algebraMap k (CliffordAlgebra Q) (Q v) * ↑(x⁻¹) := by
        rw [CliffordAlgebra.ι_sq_scalar]
      _ = algebraMap k (CliffordAlgebra Q) (Q v) *
          (x : CliffordAlgebra Q) * ↑(x⁻¹) := by
        rw [Algebra.commutes]
      _ = algebraMap k (CliffordAlgebra Q) (Q v) := by
        rw [mul_assoc, Units.mul_inv, mul_one]
  change algebraMap k (CliffordAlgebra Q) (Q (inducedLinearEquiv s x hx v)) =
    ((x : CliffordAlgebra Q) * CliffordAlgebra.ι Q v * ↑(x⁻¹)) *
      ((x : CliffordAlgebra Q) * CliffordAlgebra.ι Q v * ↑(x⁻¹)) at hs
  rw [hconj] at hs
  let _ : Nontrivial (CliffordAlgebra Q) :=
    s.cliffordToExterior.symm.injective.nontrivial
  exact (FaithfulSMul.algebraMap_injective k (CliffordAlgebra Q)) hs

/-- An even unit normalizing the vectors of a positive-rank split Clifford
algebra differs from a Lipschitz unit by an even element commuting with every
embedded vector. -/
public theorem split_even_clifford_normalizer_factorization
    (s : SplitQuadraticForm Q) (hs : 0 < s.rank)
    {x : (CliffordAlgebra Q)ˣ}
    (hxEven : (↑x : CliffordAlgebra Q) ∈ CliffordAlgebra.even Q)
    (hxNormalizer :
      ConjAct.toConjAct x • LinearMap.range (CliffordAlgebra.ι Q) =
        LinearMap.range (CliffordAlgebra.ι Q)) :
    ∃ y : (CliffordAlgebra Q)ˣ,
      y ∈ lipschitzGroup Q ∧
      (↑(x * y⁻¹) : CliffordAlgebra Q) ∈ CliffordAlgebra.even Q ∧
      ∀ v : V, Commute (↑(x * y⁻¹) : CliffordAlgebra Q)
        (CliffordAlgebra.ι Q v) := by
  let f := inducedLinearEquiv s x hxNormalizer
  obtain ⟨y, hyLip, hySpec⟩ := split_orthogonal_lipschitz_generation s f
    (inducedLinearEquiv_preserves s x hxNormalizer)
  have hactions (v : V) :
      (x : CliffordAlgebra Q) * CliffordAlgebra.ι Q v * ↑(x⁻¹) =
        (y : CliffordAlgebra Q) * CliffordAlgebra.ι Q v * ↑(y⁻¹) := by
    rw [← inducedLinearEquiv_spec s x hxNormalizer, ← hySpec]
  refine ⟨y, hyLip,
    CliffordAlgebra.mul_inv_mem_even_of_mem_even_of_lipschitzGroup
      s hs hxEven hyLip hactions, ?_⟩
  intro v
  have hxs := inducedLinearEquiv_spec s x hxNormalizer (f.symm v)
  have hys := hySpec (f.symm v)
  rw [f.apply_symm_apply] at hxs hys
  show (↑(x * y⁻¹) : CliffordAlgebra Q) * CliffordAlgebra.ι Q v =
    CliffordAlgebra.ι Q v * (↑(x * y⁻¹) : CliffordAlgebra Q)
  calc
    (↑(x * y⁻¹) : CliffordAlgebra Q) * CliffordAlgebra.ι Q v =
        (x : CliffordAlgebra Q) * ↑(y⁻¹) *
          ((y : CliffordAlgebra Q) * CliffordAlgebra.ι Q (f.symm v) * ↑(y⁻¹)) := by
      rw [hys]
      simp [mul_assoc]
    _ = (x : CliffordAlgebra Q) * CliffordAlgebra.ι Q (f.symm v) * ↑(y⁻¹) := by
      simp [mul_assoc]
    _ = ((x : CliffordAlgebra Q) * CliffordAlgebra.ι Q (f.symm v) * ↑(x⁻¹)) *
        (x : CliffordAlgebra Q) * ↑(y⁻¹) := by
      symm
      calc
        ((x : CliffordAlgebra Q) * CliffordAlgebra.ι Q (f.symm v) * ↑(x⁻¹)) *
              (x : CliffordAlgebra Q) * ↑(y⁻¹) =
            (x : CliffordAlgebra Q) * CliffordAlgebra.ι Q (f.symm v) *
              (↑(x⁻¹) * (x : CliffordAlgebra Q)) * ↑(y⁻¹) := by noncomm_ring
        _ = (x : CliffordAlgebra Q) * CliffordAlgebra.ι Q (f.symm v) * ↑(y⁻¹) := by
          rw [Units.inv_mul]
          simp
    _ = CliffordAlgebra.ι Q v * (↑(x * y⁻¹) : CliffordAlgebra Q) := by
      rw [← hxs]
      exact mul_assoc _ _ _

end Theory.AlgebraicGroup
