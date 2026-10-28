module

public import Theory.Representation.SL3.BinaryDefiningFactors
public import Mathlib.RepresentationTheory.Invariants

/-!
# Fixed equations for trace-zero adjoint operators

Transpose fixes precisely the symmetric matrices. The three off-diagonal
antisymmetry equations are independent even in characteristic two. Commuting
with the nonidentity transvection `1 + E₀₁` imposes four independent equations.
Explicit trace-zero matrices prove surjectivity of both equation maps.

If one actor has either form in genuine linear coordinates, every common
fixed vector satisfies its equations. Rank-nullity therefore bounds the
codimension of the common fixed space by three or four, respectively. No
assumption about cubicity, offenders, or the remaining actors is needed.

These calculations support the adjoint case of Guralnick--Malle,
Classification of 2F-modules II, Proposition 4.11, internal pp.31--32.
-/

public noncomputable section

open Representation.SL3.BinaryDefiningFactors
namespace Representation.SU3.CubicDegree.SchurOuter.AdjointBounds
variable {K : Type*} [Field K]

/-- Coordinate matrix of the actual trace-zero endomorphism. -/
def adjointMatrix : AdjointSpace K →ₗ[K] Matrix (Fin 3) (Fin 3) K :=
  LinearMap.toMatrix'.toLinearMap.comp (LinearMap.ker (LinearMap.trace K (Fin 3 → K))).subtype

/-- The coordinates use the standard basis of the natural three-space. -/
theorem adjointMatrix_apply (X : AdjointSpace K) :
    adjointMatrix X = LinearMap.toMatrix' X.val := by rfl

private noncomputable def fromMatrix (M : Matrix (Fin 3) (Fin 3) K) (h : M.trace = 0) :
    AdjointSpace K := ⟨M.toLin', by simpa using h⟩

private theorem adjointMatrix_fromMatrix (M : Matrix (Fin 3) (Fin 3) K) (h : M.trace = 0) :
    adjointMatrix (fromMatrix M h) = M := LinearMap.toMatrix'_toLin' M

private noncomputable def transposeEquations : AdjointSpace K →ₗ[K] (Fin 3 → K) where
  toFun X := ![adjointMatrix X 0 1 - adjointMatrix X 1 0,
    adjointMatrix X 0 2 - adjointMatrix X 2 0,
    adjointMatrix X 1 2 - adjointMatrix X 2 1]
  map_add' X Y := by
    ext i
    fin_cases i <;> simp [map_add]
    all_goals ring
  map_smul' c X := by
    ext i
    fin_cases i <;> simp [map_smul, mul_sub]

private theorem transposeEquations_surjective :
    Function.Surjective (transposeEquations (K := K)) := by
  intro v
  let M : Matrix (Fin 3) (Fin 3) K := !![0, v 0, v 1; 0, 0, v 2; 0, 0, 0]
  have hM : M.trace = 0 := by simp [M, Matrix.trace, Fin.sum_univ_three]
  refine ⟨fromMatrix M hM, ?_⟩
  change ![adjointMatrix (fromMatrix M hM) 0 1 - adjointMatrix (fromMatrix M hM) 1 0,
    adjointMatrix (fromMatrix M hM) 0 2 - adjointMatrix (fromMatrix M hM) 2 0,
    adjointMatrix (fromMatrix M hM) 1 2 - adjointMatrix (fromMatrix M hM) 2 1] = v
  rw [adjointMatrix_fromMatrix]
  ext i
  fin_cases i <;> simp [M]

private theorem transposeEquations_eq_zero (X : AdjointSpace K)
    (h : (adjointMatrix X).transpose = adjointMatrix X) :
    transposeEquations X = 0 := by
  have h01 := congrArg (fun M : Matrix (Fin 3) (Fin 3) K => M 1 0) h
  have h02 := congrArg (fun M : Matrix (Fin 3) (Fin 3) K => M 2 0) h
  have h12 := congrArg (fun M : Matrix (Fin 3) (Fin 3) K => M 2 1) h
  ext i
  fin_cases i <;> simp_all [transposeEquations, Matrix.transpose_apply]

/-- The nonidentity elementary transvection `1 + E₀₁`. -/
@[expose] def transvectionMatrix : Matrix (Fin 3) (Fin 3) K :=
  !![1, 1, 0; 0, 1, 0; 0, 0, 1]

private noncomputable def transvectionEquations : AdjointSpace K →ₗ[K] (Fin 4 → K) where
  toFun X := ![adjointMatrix X 1 0, adjointMatrix X 0 0 - adjointMatrix X 1 1,
    adjointMatrix X 1 2, adjointMatrix X 2 0]
  map_add' X Y := by
    ext i
    fin_cases i <;> simp [map_add]
    all_goals ring
  map_smul' c X := by
    ext i
    fin_cases i <;> simp [map_smul, mul_sub]

private theorem transvectionEquations_surjective :
    Function.Surjective (transvectionEquations (K := K)) := by
  intro v
  let M : Matrix (Fin 3) (Fin 3) K := !![v 1, 0, 0; v 0, 0, v 2; v 3, 0, -v 1]
  have hM : M.trace = 0 := by simp [M, Matrix.trace, Fin.sum_univ_three]
  refine ⟨fromMatrix M hM, ?_⟩
  change ![adjointMatrix (fromMatrix M hM) 1 0,
    adjointMatrix (fromMatrix M hM) 0 0 - adjointMatrix (fromMatrix M hM) 1 1,
    adjointMatrix (fromMatrix M hM) 1 2, adjointMatrix (fromMatrix M hM) 2 0] = v
  rw [adjointMatrix_fromMatrix]
  ext i
  fin_cases i <;> simp [M]

private theorem transvectionEquations_eq_zero (X : AdjointSpace K)
    (h : adjointMatrix X * transvectionMatrix = transvectionMatrix * adjointMatrix X) :
    transvectionEquations X = 0 := by
  have h00 := congrArg (fun M : Matrix (Fin 3) (Fin 3) K => M 0 0) h
  have h01 := congrArg (fun M : Matrix (Fin 3) (Fin 3) K => M 0 1) h
  have h02 := congrArg (fun M : Matrix (Fin 3) (Fin 3) K => M 0 2) h
  have h21 := congrArg (fun M : Matrix (Fin 3) (Fin 3) K => M 2 1) h
  simp [Matrix.mul_apply, Fin.sum_univ_three, transvectionMatrix] at h00 h01 h02 h21
  ext i
  fin_cases i
  · change adjointMatrix X 1 0 = 0
    exact h00
  · change adjointMatrix X 0 0 - adjointMatrix X 1 1 = 0
    change adjointMatrix X 0 0 + adjointMatrix X 0 1 =
      adjointMatrix X 0 1 + adjointMatrix X 1 1 at h01
    linear_combination h01
  · change adjointMatrix X 1 2 = 0
    exact h02
  · change adjointMatrix X 2 0 = 0
    exact h21



variable {W : Type*} [AddCommGroup W] [Module K W]

/-- A literal linear operator is transpose in trace-zero matrix coordinates. -/
@[expose] def IsTransposeOperator (f : Module.End K W) : Prop :=
  ∃ e : W ≃ₗ[K] AdjointSpace K, ∀ w,
    adjointMatrix (e (f w)) = (adjointMatrix (e w)).transpose

/-- A literal linear operator is conjugation by the nonidentity transvection
`1 + E₀₁`. The equation avoids making any choice of inverse. -/
@[expose] def IsTransvectionOperator (f : Module.End K W) : Prop :=
  ∃ e : W ≃ₗ[K] AdjointSpace K, ∀ w,
    adjointMatrix (e (f w)) * transvectionMatrix =
      transvectionMatrix * adjointMatrix (e w)

private theorem quotient_finrank_ge [FiniteDimensional K W] {n : ℕ}
    (U : Submodule K W) (e : W ≃ₗ[K] AdjointSpace K)
    (p : AdjointSpace K →ₗ[K] (Fin n → K)) (hp : Function.Surjective p)
    (hU : ∀ w ∈ U, p (e w) = 0) : n ≤ Module.finrank K (W ⧸ U) := by
  let f := p.comp e.toLinearMap
  have hf : Function.Surjective f := hp.comp e.surjective
  have hd := f.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hf, finrank_top, Module.finrank_pi,
    Fintype.card_fin] at hd
  have hle : U ≤ f.ker := fun w hw => hU w hw
  have hm := Submodule.finrank_mono hle
  have hq := U.finrank_quotient_add_finrank
  omega

variable {H : Type*} [Group H] [FiniteDimensional K W]

/-- An actor conjugate to transpose gives three independent common fixed equations. -/
theorem three_le_fixedCodim_of_transpose (τ : Representation K H W) (a : H)
    (ha : IsTransposeOperator (τ a)) :
    3 ≤ Module.finrank K (W ⧸ τ.invariants) := by
  obtain ⟨e, he⟩ := ha
  apply quotient_finrank_ge τ.invariants e transposeEquations transposeEquations_surjective
  intro w hw
  apply transposeEquations_eq_zero
  have h := he w
  rw [hw a] at h
  exact h.symm

/-- A transvection actor gives four independent common fixed equations. -/
theorem four_le_fixedCodim_of_transvection (τ : Representation K H W) (a : H)
    (ha : IsTransvectionOperator (τ a)) :
    4 ≤ Module.finrank K (W ⧸ τ.invariants) := by
  obtain ⟨e, he⟩ := ha
  apply quotient_finrank_ge τ.invariants e transvectionEquations transvectionEquations_surjective
  intro w hw
  apply transvectionEquations_eq_zero
  have h := he w
  rwa [hw a] at h

end Representation.SU3.CubicDegree.SchurOuter.AdjointBounds
