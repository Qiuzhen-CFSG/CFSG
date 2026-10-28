module

public import Mathlib.LinearAlgebra.Eigenspace.Minpoly
public import Mathlib.LinearAlgebra.Eigenspace.Semisimple

universe u v w

/-! A finite eigenvector-spanning criterion for semisimplicity on an invariant
subspace. -/

namespace Theory.AlgebraicGroup

variable {k : Type u} [Field k]

/-- A semisimple endomorphism over an algebraically closed field admits a
finite eigenbasis. -/
public lemma Module.End.IsSemisimple.exists_fin_eigenbasis
    {V : Type v} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    [IsAlgClosed k]
    (T : Module.End k V) (hT : T.IsSemisimple) :
    ∃ (b : Module.Basis (Fin (Module.finrank k V)) k V)
      (μ : Fin (Module.finrank k V) → k),
      ∀ i, T (b i) = μ i • b i := by
  classical
  let hInternal := DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    T.eigenspaces_iSupIndep hT.iSup_eigenspace_eq_top
  let I := (μ : k) × Fin (Module.finrank k (T.eigenspace μ))
  let v : Module.Basis I k V :=
    hInternal.collectedBasis fun μ => Module.finBasis k (T.eigenspace μ)
  let : Fintype I := FiniteDimensional.fintypeBasisIndex v
  have hcard : Fintype.card I = Module.finrank k V :=
    (Module.finrank_eq_card_basis v).symm
  let e : I ≃ Fin (Module.finrank k V) :=
    Fintype.equivFinOfCardEq hcard
  let b : Module.Basis (Fin (Module.finrank k V)) k V := v.reindex e
  let μ : Fin (Module.finrank k V) → k := fun i => (e.symm i).1
  refine ⟨b, μ, ?_⟩
  intro i
  have hmem : v (e.symm i) ∈ T.eigenspace ((e.symm i).1) :=
    hInternal.collectedBasis_mem
      (fun μ => Module.finBasis k (T.eigenspace μ)) (e.symm i)
  have heig := Module.End.mem_eigenspace_iff.mp hmem
  simpa [b, μ, Module.Basis.reindex_apply] using heig

/-- If an invariant subspace is contained in the span of finitely many
eigenvectors, then the restricted endomorphism is semisimple. -/
public lemma Module.End.isSemisimple_restrict_of_le_span_eigenvectors
    {M : Type v} [AddCommGroup M] [Module k M]
    (T : Module.End k M) (P : Submodule k M)
    (hP : P ∈ T.invtSubmodule)
    {ι : Type w} [Finite ι] (v : ι → M) (μ : ι → k)
    (hv : ∀ i, T (v i) = μ i • v i)
    (hspan : P ≤ Submodule.span k (Set.range v)) :
    Module.End.IsSemisimple (T.restrict hP) := by
  classical
  let := Fintype.ofFinite ι
  let eigenvalues : Finset k := Finset.univ.image μ
  let q : Polynomial k :=
    ∏ a ∈ eigenvalues, (Polynomial.X - Polynomial.C a)
  have hsep : q.Separable := by
    apply Polynomial.separable_prod_X_sub_C_iff'.2
    intro x _hx y _hy hxy
    exact hxy
  have hqzero : Submodule.span k (Set.range v) ≤
      LinearMap.ker (Polynomial.aeval T q) := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    change Polynomial.aeval T q (v i) = 0
    rw [Module.End.aeval_apply_of_mem_apply_eq_smul (hv i)]
    have hmem : μ i ∈ eigenvalues := by
      simp [eigenvalues]
    have heval : q.eval (μ i) = 0 := by
      dsimp [q]
      rw [Polynomial.eval_prod]
      exact Finset.prod_eq_zero hmem (by simp)
    rw [heval, zero_smul]
  have hrestrict (r : Polynomial k) (x : P) :
      ((Polynomial.aeval (T.restrict hP) r) x : M) =
        Polynomial.aeval T r x := by
    induction r using Polynomial.induction_on' with
    | add p q hp hq =>
        simp only [map_add, LinearMap.add_apply]
        change
          (↑(Polynomial.aeval (T.restrict hP) p x) : M) +
              ↑(Polynomial.aeval (T.restrict hP) q x) =
            Polynomial.aeval T p x + Polynomial.aeval T q x
        rw [hp, hq]
    | monomial n a =>
        simp only [Polynomial.aeval_monomial, Module.End.mul_apply,
          Module.algebraMap_end_apply]
        rw [Module.End.pow_restrict n hP]
        rfl
  apply Module.End.isSemisimple_of_squarefree_aeval_eq_zero hsep.squarefree
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  rw [hrestrict]
  exact hqzero (hspan x.property)

end Theory.AlgebraicGroup
