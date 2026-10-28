module

public import Theory.Representation.FactorDegreeFiltration
public import Theory.Representation.JacobsonDensity
public import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Matrix-algebra criteria for the binary G₂ cycle factors

A rank-one matrix in an algebra, together with spanning column and row orbits,
produces every matrix unit by bilinearity. Thus the algebra is the whole matrix
algebra. Coordinates then transfer this density to any actual representation
whose action contains the checked matrices, proving irreducibility. No
assertion that the chosen actors generate the whole group is needed for that
irreducibility implication.

The final helper builds the literal zero-subspace quotient step of a finite
factor-degree filtration. These are the algebraic parts of the certificate
argument for Aschbacher–Smith G.7.2(3), printed p.348 / PDF p.359.
-/

@[expose] public section

open Matrix Representation

namespace G2DerivedPermutationFiltration.CycleMatrixCriterion

/-- A rank-one operator with spanning row and column orbits generates all matrix units. -/
theorem algebra_eq_top_of_rank_one
    {k n I J : Type*} [Field k] [Fintype n] [DecidableEq n]
    (Q : Subalgebra k (Matrix n n k)) (u v : n → k)
    (L : I → Matrix n n k) (R : J → Matrix n n k)
    (hL : ∀ i, L i ∈ Q) (hR : ∀ j, R j ∈ Q)
    (huv : vecMulVec u v ∈ Q)
    (hcol : Submodule.span k (Set.range (fun i => (L i).mulVec u)) = ⊤)
    (hrow : Submodule.span k (Set.range (fun j => vecMul v (R j))) = ⊤) : Q = ⊤ := by
  have hbase (i : I) (j : J) :
      vecMulVec ((L i).mulVec u) (vecMul v (R j)) ∈ Q := by
    rw [← mul_vecMulVec, ← vecMulVec_mul]
    exact Q.mul_mem (hL i) (Q.mul_mem huv (hR j))
  have hxy (x y : n → k) : vecMulVec x y ∈ Q := by
    have hx : x ∈ Submodule.span k (Set.range (fun i => (L i).mulVec u)) := by
      rw [hcol]; trivial
    have hy : y ∈ Submodule.span k (Set.range (fun j => vecMul v (R j))) := by
      rw [hrow]; trivial
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      induction hy using Submodule.span_induction with
      | mem y hy => obtain ⟨j, rfl⟩ := hy; exact hbase i j
      | zero => simpa only [vecMulVec_zero] using Q.zero_mem
      | add x y _ _ hx hy => simpa only [vecMulVec_add] using Q.add_mem hx hy
      | smul c x _ hx => simpa only [vecMulVec_smul] using Q.smul_mem hx c
    | zero => simpa only [zero_vecMulVec] using Q.zero_mem
    | add x y _ _ hx hy => simpa only [add_vecMulVec] using Q.add_mem hx hy
    | smul c x _ hx => simpa only [smul_vecMulVec] using Q.smul_mem hx c
  have hu (i j : n) : Matrix.single i j (1 : k) ∈ Q := by
    have he : vecMulVec (Pi.single i (1 : k)) (Pi.single j (1 : k)) =
        Matrix.single i j 1 := by
      ext a b
      by_cases ha : a = i <;> by_cases hb : b = j <;>
        simp_all [vecMulVec_apply, Matrix.single_apply] <;> grind
    rw [← he]
    exact hxy _ _
  apply top_unique
  intro M _
  have hM : M = ∑ i : n, ∑ j : n, M i j • Matrix.single i j 1 := by
    simpa using Matrix.matrix_eq_sum_single M
  rw [hM]
  exact Q.sum_mem fun i _ => Q.sum_mem fun j _ => Q.smul_mem (hu i j) (M i j)

/-- Two checked action matrices suffice; they need not generate the acting group. -/
theorem irreducible_of_coordinate_matrices
    {k G V n : Type*} [Field k] [_root_.Group G] [AddCommGroup V] [Module k V]
    [Fintype n] [DecidableEq n] [Nonempty n]
    (ρ : Representation k G V) (e : V ≃ₗ[k] (n → k))
    (a b : G) (A B : Matrix n n k)
    (ha : LinearMap.toMatrix' (e.conj (ρ a)) = A)
    (hb : LinearMap.toMatrix' (e.conj (ρ b)) = B)
    (hd : ∀ Q : Subalgebra k (Matrix n n k), A ∈ Q → B ∈ Q → Q = ⊤) :
    IsIrreducible ρ := by
  let : Nontrivial V := e.toEquiv.nontrivial
  let : FiniteDimensional k V := FiniteDimensional.of_injective e.toLinearMap e.injective
  apply irreducible_of_jacobson_density_surjective
  let E : Module.End k V ≃ₐ[k] Matrix n n k :=
    (e.conjAlgEquiv k).trans LinearMap.toMatrixAlgEquiv'
  let P := Algebra.adjoin k (Set.range ρ)
  let Q := P.map E.toAlgHom
  have hA : A ∈ Q := by
    rw [← ha]
    exact ⟨ρ a, Algebra.subset_adjoin (Set.mem_range_self a), rfl⟩
  have hB : B ∈ Q := by
    rw [← hb]
    exact ⟨ρ b, Algebra.subset_adjoin (Set.mem_range_self b), rfl⟩
  have hQ := hd Q hA hB
  apply top_unique
  intro f _
  have hf : E f ∈ Q := by rw [hQ]; trivial
  obtain ⟨f', hf', he⟩ := hf
  exact E.injective he ▸ hf'

end G2DerivedPermutationFiltration.CycleMatrixCriterion


namespace G2DerivedPermutationFiltration.CycleMatrixCriterion

/-- An irreducible action gives a filtration step using its actual quotient by zero. -/
theorem simple_filtration {k G V : Type*} [Field k] [_root_.Group G]
    [AddCommGroup V] [Module k V] (D : Set ℕ) (ρ : Representation k G V)
    (hρ : IsIrreducible ρ) (hd : Module.finrank k V ∈ D) :
    FactorDegreeFiltration D ρ := by
  let S : Subrepresentation ρ := ⊥
  let e : (V ⧸ S.toSubmodule) ≃ₗ[k] V := S.toSubmodule.quotEquivOfEqBot rfl
  let E : Representation.RepEquiv S.quotientRepresentation ρ := {
    toLinearEquiv := e
    isIntertwining' := by
      intro g
      apply LinearMap.ext
      intro x
      induction x using Submodule.Quotient.induction_on with
      | H x => rfl }
  refine FactorDegreeFiltration.step S ?_ (E.irreducible_of_euqiv hρ) ?_
  · let : Subsingleton S := by
      refine ⟨fun x y => Subtype.ext ?_⟩
      exact x.property.trans y.property.symm
    exact FactorDegreeFiltration.zero S.toRepresentation
  · rw [e.finrank_eq]
    exact hd

/-- Keep the ambient module abstract when checking a nested subspace action. -/
theorem subspace_irreducible_of_coordinate_matrices
    {k G V n : Type*} [Field k] [_root_.Group G] [AddCommGroup V] [Module k V]
    [Fintype n] [DecidableEq n] [Nonempty n]
    (ρ : Representation k G V) (S : Subrepresentation ρ)
    (e : S.toSubmodule ≃ₗ[k] (n → k))
    (a b : G) (A B : Matrix n n k)
    (ha : LinearMap.toMatrix' (e.conj (S.toRepresentation a)) = A)
    (hb : LinearMap.toMatrix' (e.conj (S.toRepresentation b)) = B)
    (hd : ∀ Q : Subalgebra k (Matrix n n k), A ∈ Q → B ∈ Q → Q = ⊤) :
    IsIrreducible S.toRepresentation :=
  irreducible_of_coordinate_matrices S.toRepresentation e a b A B ha hb hd

end G2DerivedPermutationFiltration.CycleMatrixCriterion
