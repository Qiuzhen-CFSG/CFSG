module

public import Theory.Representation.JacobsonDensity
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# Commuting compressions of irreducible representations

An idempotent endomorphism of a finite-dimensional complex irreducible monoid
representation has image of dimension at most one if the compressed monoid
operators commute. Neither finiteness of the monoid nor orthogonality or
nonvanishing of the projector is required.

Jacobson density identifies the span of the representation image with the full
endomorphism algebra: the image is already a submonoid, so its algebraic adjoin
equals its linear span. Two span inductions extend the commuting hypothesis to
all compressed endomorphisms. Given a nonzero image vector, choose a dual
functional taking value one there. Applying commutation to the associated
rank-one operators shows that every image vector is a scalar multiple of it.

This is the density/rank-one argument for the projector dimension bound used in
the twisted Gelfand weight-multiplicity criterion. The density input is the
general Jacobson density theorem formalized in `Theory.Representation.JacobsonDensity`;
the remaining argument is elementary linear algebra, independent of character
averaging or the particular group producing the projector.
-/

namespace Representation

variable {G V : Type*} [Monoid G] [AddCommGroup V] [Module ℂ V]
  [FiniteDimensional ℂ V]

public theorem finrank_range_le_one_of_commuting_compressions
    (rho : Representation ℂ G V) (hirred : IsIrreducible rho)
    (proj : Module.End ℂ V) (hproj : proj * proj = proj)
    (hcomm : ∀ left right : G,
      (proj * rho left * proj) * (proj * rho right * proj) =
        (proj * rho right * proj) * (proj * rho left * proj)) :
    Module.finrank ℂ (LinearMap.range proj) ≤ 1 := by
  classical
  let : IsIrreducible rho := hirred
  have hspan : Submodule.span ℂ (Set.range rho) = ⊤ := by
    have hdensity := jacobson_density_surjective_isAlgClosed_rep rho
    have heq := Algebra.adjoin_eq_span ℂ (Set.range rho)
    rw [← MonoidHom.coe_mrange rho, Submonoid.closure_eq] at heq
    rw [MonoidHom.coe_mrange, hdensity] at heq
    exact heq.symm
  have hcompress : ∀ left right : Module.End ℂ V,
      (proj * left * proj) * (proj * right * proj) =
        (proj * right * proj) * (proj * left * proj) := by
    intro left right
    have hleft : left ∈ Submodule.span ℂ (Set.range rho) := by rw [hspan]; trivial
    have hright : right ∈ Submodule.span ℂ (Set.range rho) := by rw [hspan]; trivial
    induction hleft using Submodule.span_induction with
    | mem left hleft =>
      obtain ⟨element, rfl⟩ := hleft
      induction hright using Submodule.span_induction with
      | mem right hright =>
        obtain ⟨other, rfl⟩ := hright
        exact hcomm element other
      | zero => simp
      | add left right _ _ hleft hright =>
        simpa only [mul_add, add_mul] using congrArg₂ (· + ·) hleft hright
      | smul scalar right _ hright =>
        simpa only [Algebra.mul_smul_comm, Algebra.smul_mul_assoc] using
          congrArg (scalar • ·) hright
    | zero => simp
    | add left right _ _ hleft hright =>
      simpa only [mul_add, add_mul] using congrArg₂ (· + ·) hleft hright
    | smul scalar left _ hleft =>
      simpa only [Algebra.mul_smul_comm, Algebra.smul_mul_assoc] using
        congrArg (scalar • ·) hleft
  have hfix (vector : LinearMap.range proj) : proj vector = vector := by
    obtain ⟨vector, ⟨preimage, rfl⟩⟩ := vector
    exact LinearMap.congr_fun hproj preimage
  by_cases hzero : ∀ vector : LinearMap.range proj, vector = 0
  · exact finrank_le_one (0 : LinearMap.range proj) (fun vector =>
      ⟨0, by simpa using (hzero vector).symm⟩)
  · push Not at hzero
    obtain ⟨vector, hvector⟩ := hzero
    have hnonzero : (vector : V) ≠ 0 := by simpa using hvector
    obtain ⟨dual, hdual⟩ := Module.Projective.exists_dual_eq_one ℂ hnonzero
    apply finrank_le_one vector
    intro other
    refine ⟨dual other, ?_⟩
    apply Subtype.ext
    have heq := LinearMap.congr_fun
      (hcompress (dual.smulRight (vector : V)) (dual.smulRight (other : V)))
      (vector : V)
    simpa [Module.End.mul_apply, hfix, LinearMap.smulRight_apply, hdual] using heq

end Representation
