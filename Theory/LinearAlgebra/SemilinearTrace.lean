module
public import Mathlib.LinearAlgebra.Trace

/-!
# Trace under semilinear conjugation

For finite-dimensional spaces over a field and a semilinear equivalence
with respect to a field automorphism σ, conjugating an endomorphism applies
σ to its trace. The theorem uses the existing LinearEquiv.conj construction,
with the inverse field automorphism specified explicitly.

Write the endomorphism as a sum of rank-one maps using an existing basis.
A rank-one map v times l conjugates to e(v) times the linear functional
w ↦ σ(l(e⁻¹(w))). The rank-one trace formula therefore transforms its trace
by σ. Additivity proves the result for the full endomorphism. No new basis
construction, scalar-restriction convention, or representation-theoretic
classification is needed.

This supplies the elementary trace calculation for coefficient twists in
Frobenius descent of the SL2 representations used in Fong--Wong (1.15).
-/

namespace LinearMap

variable {F V W : Type*} [Field F] [AddCommGroup V] [Module F V]
  [AddCommGroup W] [Module F W]

variable (σ : F ≃+* F)
attribute [local instance] RingHomInvPair.of_ringEquiv RingHomInvPair.of_ringEquiv_symm

private theorem trace_conj_smulRight [FiniteDimensional F V] [FiniteDimensional F W]
    (e : LinearEquiv (σ' := (σ.symm : F →+* F)) (σ : F →+* F) V W)
    (l : V →ₗ[F] F) (v : V) :
    trace F W (e.conj (l.smulRight v)) = σ (trace F V (l.smulRight v)) := by
  let l' : W →ₗ[F] F :=
    { toFun := fun w => σ (l (e.symm w))
      map_add' := by intros; simp
      map_smul' := by intros; simp [map_smulₛₗ] }
  have h : e.conj (l.smulRight v) = l'.smulRight (e v) := by
    ext w
    simp [l', LinearEquiv.conj_apply_apply, map_smulₛₗ]
  rw [h, trace_smulRight, trace_smulRight]
  simp [l']

/-- Semilinear conjugation transforms the trace by the field automorphism. -/
public theorem trace_conj_semilinear [FiniteDimensional F V] [FiniteDimensional F W]
    (f : V →ₗ[F] V)
    (e : LinearEquiv (σ' := (σ.symm : F →+* F)) (σ : F →+* F) V W) :
    trace F W (e.conj f) = σ (trace F V f) := by
  classical
  let b := Module.Free.chooseBasis F V
  have hf : f = ∑ i, (b.coord i).smulRight (f (b i)) := by
    ext v
    simp only [sum_apply, smulRight_apply, Module.Basis.coord_apply]
    simp only [← map_smul]
    rw [← map_sum]
    exact congrArg f (b.sum_repr v).symm
  rw [hf, map_sum, map_sum, map_sum, map_sum]
  exact Finset.sum_congr rfl (fun i _ => trace_conj_smulRight σ e (b.coord i) (f (b i)))

end LinearMap

