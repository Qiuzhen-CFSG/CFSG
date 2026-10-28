module

public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.BasicMinimum.HighestWeight
public import Theory.AlgebraicGroup.Bor1.CommonEigenspaces
public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Coroot weight spaces for the concrete F4 action

Integer four-tuples specify simultaneous eigenspaces of the four actual simple
coroot curves. Distinct tuples give distinct eigenvalue functions over an
algebraically closed field. The general common-eigenspace independence theorem
therefore bounds any finite sum of their dimensions by the representation's
dimension. No maximal-torus realization or highest-weight uniqueness is assumed.

These spaces retain the positive-coroot convention of `BasicWeights`. In
particular the zero space consists of vectors fixed by all four coroot curves.
The highest-vector bridge uses exactly the existing public highest-weight
hypothesis, without adding any representation classification premise.

Source: GLS3, Section 1.14, especially the weight and multiplicity conventions
of Definition 1.14.5. This is the linear-algebra step in the end-node minimum.
-/

public section

open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
open scoped DirectSum
namespace ReeF4.BinaryDegree.ExceptionalTensor.EndNode
universe u
variable {F : Type u} [Field F] [IsAlgClosed F]
/-- Simple-coroot coefficients, numbered long, long, short, short. -/
abbrev Weight := Fin 4 → ℤ

/-- Evaluation of the integral coefficient tuple on a simple coroot. -/
@[expose] def corootEigenvalue (μ : Weight) (p : Fin 4 × Fˣ) : F := (p.2 : F) ^ μ p.1

theorem corootEigenvalue_injective : Function.Injective (corootEigenvalue (F := F)) := by
  intro μ ν h
  funext i
  by_contra hi
  obtain ⟨t, ht⟩ := exists_unit_zpow_ne_one (k := F) (sub_ne_zero.mpr hi)
  apply ht
  rw [zpow_sub, mul_inv_eq_one]
  apply Units.ext
  simpa [corootEigenvalue] using congrFun h (i, t)

/-- The simultaneous eigenspace for the specified integral coroot coefficients. -/
@[expose] noncomputable def corootWeightSpace (B : AlgebraicFactor F) (μ : Weight) :
    Submodule F B.Space :=
  ⨅ p : Fin 4 × Fˣ, Module.End.eigenspace
    (B.action.action (algebraicCorootElement (typeF4SimpleRootIndex p.1) p.2) :
      Module.End F B.Space) (corootEigenvalue μ p)

theorem mem_corootWeightSpace (B : AlgebraicFactor F) (μ : Weight) (v : B.Space) :
    v ∈ corootWeightSpace B μ ↔ ∀ (i : Fin 4) (t : Fˣ),
      (B.action.action (algebraicCorootElement (typeF4SimpleRootIndex i) t) :
        Module.End F B.Space) v = ((t : F) ^ μ i) • v := by
  simp only [corootWeightSpace, Submodule.mem_iInf, Module.End.mem_eigenspace_iff,
    corootEigenvalue, Prod.forall]

theorem corootWeightSpace_iSupIndep (B : AlgebraicFactor F) :
    iSupIndep (corootWeightSpace B) :=
  (Bor1.iSupIndep_commonEigenspaces (fun p : Fin 4 × Fˣ =>
    (B.action.action (algebraicCorootElement (typeF4SimpleRootIndex p.1) p.2) :
      Module.End F B.Space))).comp corootEigenvalue_injective

/-- Count dimensions of finitely many distinct actual coroot weight spaces. -/
theorem sum_corootWeightSpace_finrank_le (B : AlgebraicFactor F)
    {ι : Type*} [Fintype ι] (μ : ι → Weight) (hμ : Function.Injective μ) :
    ∑ i, Module.finrank F (corootWeightSpace B (μ i)) ≤ Module.finrank F B.Space := by
  classical
  let A := fun i => corootWeightSpace B (μ i)
  have hi : Function.Injective (DirectSum.coeLinearMap A) :=
    ((corootWeightSpace_iSupIndep B).comp hμ).dfinsupp_lsum_injective
  have h := LinearMap.finrank_le_finrank_of_injective hi
  simpa only [Module.finrank_directSum] using h

theorem basicHighestWeightVector_mem_corootWeightSpace
    {B : AlgebraicFactor F} {weight : Fin 2 × Fin 2} {v : B.Space}
    (hv : B.IsBasicHighestWeightVector weight v) :
    v ∈ corootWeightSpace B (fun i => (basicCoefficient weight i : ℤ)) := by
  apply (mem_corootWeightSpace B _ v).mpr
  intro i t
  simpa only [zpow_natCast] using hv.2.2 i t

theorem mem_zero_corootWeightSpace (B : AlgebraicFactor F) (v : B.Space) :
    v ∈ corootWeightSpace B 0 ↔ ∀ (i : Fin 4) (t : Fˣ),
      (B.action.action (algebraicCorootElement (typeF4SimpleRootIndex i) t) :
        Module.End F B.Space) v = v := by
  simp only [mem_corootWeightSpace, Pi.zero_apply, zpow_zero, one_smul]

end ReeF4.BinaryDegree.ExceptionalTensor.EndNode
