module

public import Theory.AlgebraicGroup.RootSystems.CliffordSplitCentralizer
public import Theory.AlgebraicGroup.RootSystems.SplitOrthogonalCliffordFactorization

/-!
# The split even Clifford normalizer is the Lipschitz group

This module proves the reverse normalizer statement needed to recognize the
exact Spin carrier for a finite-dimensional split quadratic space of positive
hyperbolic rank.  Over an algebraically closed field of arbitrary
characteristic, an even Clifford unit whose ordinary conjugation stabilizes
the embedded vector range belongs to Mathlib's generated `lipschitzGroup`.
No inverse of `2` is used, so the result includes characteristic two.

The proof combines the characteristic-free split orthogonal factorization and
Dickson-parity theorem from `SplitOrthogonalCliffordFactorization` with the
split Clifford centralizer calculation from `CliffordSplitCentralizer`.  The
former produces a Lipschitz unit `y` such that `x * y⁻¹` is even and
centralizes every Clifford vector; the latter identifies this quotient with a
scalar.  Positive split rank supplies a vector of norm one.  A nonzero scalar
`a` is then the product `ι (a • v) * ι v`, so scalar units also lie in the
generated Lipschitz group.  Multiplying back by `y` proves the theorem.

This is the split, even-dimensional counterpart to the positive odd-dimensional
reverse theorem in `Theory.LinearAlgebra.CliffordAlgebra.LipschitzNormalizer`.
The even hypothesis is essential: without it, central units of mixed parity
can normalize the vector range without lying in the generated subgroup.
-/

universe u

open CliffordAlgebra MulAction
open scoped Pointwise

namespace Theory.AlgebraicGroup

variable {k V : Type u} [Field k] [IsAlgClosed k]
variable [AddCommGroup V] [Module k V] [FiniteDimensional k V]
variable {Q : QuadraticForm k V}

omit [IsAlgClosed k] in
private lemma exists_anisotropic_of_split
    (s : SplitQuadraticForm Q) (hs : 0 < s.rank) :
    ∃ v : V, Q v = 1 := by
  classical
  let i : Fin s.rank := ⟨0, hs⟩
  let e : Fin s.rank → k := fun j => if j = i then 1 else 0
  let w : HyperbolicSpace k s.rank := (e, e)
  let v : V := s.isometry.symm w
  refine ⟨v, ?_⟩
  have hmap := s.isometry.map_app v
  rw [s.isometry.apply_symm_apply] at hmap
  rw [← hmap]
  simp [w, e]

omit [IsAlgClosed k] in
private lemma scalar_unit_mem_lipschitzGroup
    (s : SplitQuadraticForm Q) (hs : 0 < s.rank)
    (z : (CliffordAlgebra Q)ˣ) (a : k)
    (hz : (↑z : CliffordAlgebra Q) = algebraMap k (CliffordAlgebra Q) a) :
    z ∈ lipschitzGroup Q := by
  obtain ⟨v, hv⟩ := exists_anisotropic_of_split s hs
  let : Nontrivial (CliffordAlgebra Q) :=
    s.cliffordToExterior.symm.injective.nontrivial
  have ha : a ≠ 0 := by
    intro ha
    have hz0 : (↑z : CliffordAlgebra Q) = 0 := by simp [hz, ha]
    exact z.ne_zero hz0
  have hvUnit : IsUnit (CliffordAlgebra.ι Q v) := by
    apply CliffordAlgebra.isUnit_ι_of_isUnit
    rw [hv]
    exact isUnit_one
  have havUnit : IsUnit (CliffordAlgebra.ι Q (a • v)) := by
    apply CliffordAlgebra.isUnit_ι_of_isUnit
    apply isUnit_iff_ne_zero.mpr
    simp [QuadraticMap.map_smul, hv, ha]
  obtain ⟨uv, huv⟩ := hvUnit
  obtain ⟨uav, huav⟩ := havUnit
  have huvLip : uv ∈ lipschitzGroup Q := by
    apply Subgroup.subset_closure
    change (↑uv : CliffordAlgebra Q) ∈ Set.range (CliffordAlgebra.ι Q)
    exact ⟨v, huv.symm⟩
  have huavLip : uav ∈ lipschitzGroup Q := by
    apply Subgroup.subset_closure
    change (↑uav : CliffordAlgebra Q) ∈ Set.range (CliffordAlgebra.ι Q)
    exact ⟨a • v, huav.symm⟩
  have hprod : (↑(uav * uv) : CliffordAlgebra Q) =
      algebraMap k (CliffordAlgebra Q) a := by
    simp only [Units.val_mul, huav, huv, map_smul, Algebra.smul_def]
    rw [mul_assoc, CliffordAlgebra.ι_sq_scalar, hv, map_one, mul_one]
  have hzu : z = uav * uv := by
    apply Units.ext
    rw [hz, hprod]
  rw [hzu]
  exact (lipschitzGroup Q).mul_mem huavLip huvLip

/-- In positive split rank, an even Clifford unit whose ordinary conjugation
stabilizes the embedded vector range lies in Mathlib's generated Lipschitz
group.  The result is valid in arbitrary characteristic. -/
public theorem mem_lipschitzGroup_of_mem_even_of_conjAct_smul_range_ι_eq_of_split
    (s : SplitQuadraticForm Q) (hs : 0 < s.rank)
    {x : (CliffordAlgebra Q)ˣ}
    (hxEven : (↑x : CliffordAlgebra Q) ∈ CliffordAlgebra.even Q)
    (hxNormalizer :
      ConjAct.toConjAct x • LinearMap.range (CliffordAlgebra.ι Q) =
        LinearMap.range (CliffordAlgebra.ι Q)) :
    x ∈ lipschitzGroup Q := by
  obtain ⟨y, hyLip, hxyEven, hxyCommute⟩ :=
    split_even_clifford_normalizer_factorization
      s hs hxEven hxNormalizer
  obtain ⟨a, hxyScalar⟩ :=
    CliffordAlgebra.eq_algebraMap_of_mem_even_of_commute_ι
      s (↑(x * y⁻¹) : CliffordAlgebra Q) hxyEven hxyCommute
  have hxyLip : x * y⁻¹ ∈ lipschitzGroup Q :=
    scalar_unit_mem_lipschitzGroup s hs (x * y⁻¹) a hxyScalar
  have := (lipschitzGroup Q).mul_mem hxyLip hyLip
  simpa using this

end Theory.AlgebraicGroup
