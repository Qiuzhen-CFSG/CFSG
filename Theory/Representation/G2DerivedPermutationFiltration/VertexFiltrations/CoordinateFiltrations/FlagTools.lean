module

public import Theory.Representation.G2DerivedPermutationFiltration.VertexFiltrations.Transport
public import Theory.Representation.JacobsonDensity
public import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Finite flags and matrix certificates on their literal quotients

A nested invariant flag can be assembled into a `FactorDegreeFiltration` by
transporting each preceding stage into the next stage. Separately, matrices
which span the full endomorphism algebra prove irreducibility of an actual
quotient through an explicit equivariant coordinate isomorphism. These two
constructions separate the adapted-basis identities from the density checks.

The intended application is the binary vertex modules in Aschbacher–Smith
G.7.2(3), printed p.348. Neither construction assumes a factor catalogue.
-/

@[expose] public section

namespace G2DerivedPermutationFiltration.VertexCoordinates.CoordinateFiltrations

open Representation

variable {k G V : Type*} [Field k] [Group G] [AddCommGroup V] [Module k V]
  {ρ : Representation k G V}

/-- View an invariant subspace inside another one by taking its inverse image
under the latter's inclusion. -/
def within (S T : Subrepresentation ρ) : Subrepresentation T.toRepresentation where
  toSubmodule := S.toSubmodule.comap T.toSubmodule.subtype
  apply_mem_toSubmodule g _v hv := S.apply_mem_toSubmodule g hv

/-- For nested subspaces, that inverse image is the original smaller space. -/
def withinEquiv (S T : Subrepresentation ρ) (h : S ≤ T) :
    S.toSubmodule ≃ₗ[k] (within S T).toSubmodule where
  toFun x := ⟨⟨x.val, h x.property⟩, x.property⟩
  invFun x := ⟨x.val.val, x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Assemble a finite flag using its actual successive quotient actions. -/
theorem filtration_of_flag (D : Set ℕ) (n : ℕ) (S : ℕ → Subrepresentation ρ)
    (hzero : S 0 = ⊥) (hlast : S n = ⊤)
    (hmono : ∀ m, m < n → S m ≤ S (m + 1))
    (hsimple : ∀ m, m < n → IsIrreducible (within (S m) (S (m + 1))).quotientRepresentation)
    (hdegree : ∀ m, m < n →
      Module.finrank k ((S (m + 1)).toSubmodule ⧸ (within (S m) (S (m + 1))).toSubmodule) ∈ D) :
    FactorDegreeFiltration D ρ := by
  have aux : ∀ m, m ≤ n → FactorDegreeFiltration D (S m).toRepresentation := by
    intro m
    induction m with
    | zero =>
      intro _
      have : Subsingleton (S 0).toSubmodule := by
        rw [hzero]
        exact inferInstanceAs (Subsingleton (⊥ : Submodule k V))
      exact .zero _
    | succ m ih =>
      intro hm
      have hmn : m < n := by omega
      let U := within (S m) (S (m + 1))
      have hp : FactorDegreeFiltration D U.toRepresentation := by
        apply (ih (by omega)).transport (MonoidHom.id G) (fun x => ⟨x, rfl⟩)
          U.toRepresentation (withinEquiv (S m) (S (m + 1)) (hmono m hmn))
        intro g v
        rfl
      exact .step U hp (hsimple m hmn) (hdegree m hmn)
  let e : (S n).toSubmodule ≃ₗ[k] V := {
    toFun := Subtype.val
    invFun := fun x => ⟨x, by rw [hlast]; trivial⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }
  apply (aux n le_rfl).transport (MonoidHom.id G) (fun x => ⟨x, rfl⟩) ρ e
  intro g v
  rfl

/-- Matrices of specified group elements which generate the whole matrix
algebra certify irreducibility under an actual coordinate isomorphism. -/
theorem irreducible_of_coordinate_matrices
    {J : Type*} {d : ℕ} (hd : 0 < d) (g : J → G)
    (A : J → Matrix (Fin d) (Fin d) k) (e : V ≃ₗ[k] (Fin d → k))
    (he : ∀ j v, e (ρ (g j) v) = (A j).mulVec (e v))
    (hspan : ∀ Q : Subalgebra k (Matrix (Fin d) (Fin d) k),
      (∀ j, A j ∈ Q) → Q = ⊤) : IsIrreducible ρ := by
  let : NeZero d := ⟨by omega⟩
  let : Nontrivial V := e.symm.injective.nontrivial
  let : FiniteDimensional k V := e.symm.finiteDimensional
  let E : Module.End k V ≃ₐ[k] Matrix (Fin d) (Fin d) k :=
    (e.conjAlgEquiv k).trans LinearMap.toMatrixAlgEquiv'
  have hE (j : J) : E (ρ (g j)) = A j := by
    have hlin : e.conj (ρ (g j)) = (A j).toLin' := by
      apply LinearMap.ext
      intro v
      change e (ρ (g j) (e.symm v)) = (A j).mulVec v
      rw [he, e.apply_symm_apply]
    change LinearMap.toMatrix' (e.conj (ρ (g j))) = A j
    rw [hlin, LinearMap.toMatrix'_toLin']
  apply irreducible_of_jacobson_density_surjective
  let P := Algebra.adjoin k (Set.range ρ)
  let Q := P.map E.toAlgHom
  have hQ : Q = ⊤ := hspan Q fun j => by
    rw [← hE j]
    exact ⟨ρ (g j), Algebra.subset_adjoin (Set.mem_range_self (g j)), rfl⟩
  apply top_unique
  intro f _
  have hf : E f ∈ Q := by rw [hQ]; trivial
  obtain ⟨f', hf', heq⟩ := hf
  exact E.injective heq ▸ hf'

end G2DerivedPermutationFiltration.VertexCoordinates.CoordinateFiltrations
