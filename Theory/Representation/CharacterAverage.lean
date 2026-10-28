module

public import Mathlib.RepresentationTheory.Basic
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Data.Complex.Basic
public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Mathlib.LinearAlgebra.Projection

/-!
# Finite additive-character averaging

`Representation.characterAverage` is the normalized inverse-character average
of a complex representation along an additive character from a finite abelian
group. `Representation.characterAverage_spec` identifies it as a projection
onto the intersection of the actual character eigenspaces and proves its left
and right intertwining identities. The definition is intentionally exposed so
operator arguments can expand precisely this finite sum.

Translation of the summation index proves left intertwining, and commutativity
of the parameter group gives right intertwining. Left intertwining places the
image in the weight space. Every summand fixes a weight vector after its
character factors cancel; division by the nonzero cardinal then gives the
identity on that space. The representation need not be finite-dimensional or
faithful, and the character need not factor through the parameter map: an
incompatible character simply has zero weight space and zero projection.

This is the standard finite character-averaging argument, in the explicit
operator form needed by the twisted Gelfand weight-multiplicity criterion.
Mathlib's `Representation.averageMap` is the corresponding untwisted construction.
-/

namespace Representation

variable {G A V : Type*} [Group G] [AddCommGroup A] [Fintype A]
  [AddCommGroup V] [Module ℂ V]

@[expose] public noncomputable def characterAverage
    (rho : Representation ℂ G V) (u : AddChar A G) (psi : AddChar A ℂ) :
    Module.End ℂ V :=
  (Fintype.card A : ℂ)⁻¹ • ∑ parameter : A, (psi parameter)⁻¹ • rho (u parameter)

private theorem characterAverage_left
    (rho : Representation ℂ G V) (u : AddChar A G) (psi : AddChar A ℂ)
    (parameter : A) :
    rho (u parameter) * characterAverage rho u psi =
      psi parameter • characterAverage rho u psi := by
  classical
  have hsum :
      ∑ other : A, (psi other)⁻¹ • (rho (u parameter) * rho (u other)) =
        ∑ other : A, psi parameter • ((psi other)⁻¹ • rho (u other)) := by
    apply Fintype.sum_equiv (Equiv.addLeft parameter)
    intro other
    simp only [Equiv.coe_addLeft, u.map_add_eq_mul, map_mul,
      psi.map_add_eq_mul, mul_inv_rev, smul_smul]
    congr 1
    simp [mul_comm, (psi.val_isUnit parameter).ne_zero]
  simp only [characterAverage, Algebra.mul_smul_comm, Finset.mul_sum]
  rw [hsum, ← Finset.smul_sum, smul_comm]

private theorem characterAverage_right
    (rho : Representation ℂ G V) (u : AddChar A G) (psi : AddChar A ℂ)
    (parameter : A) :
    characterAverage rho u psi * rho (u parameter) =
      psi parameter • characterAverage rho u psi := by
  classical
  rw [← characterAverage_left rho u psi parameter]
  simp only [characterAverage, Algebra.smul_mul_assoc, Algebra.mul_smul_comm,
    Finset.sum_mul, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro other _
  rw [← rho.map_mul, ← rho.map_mul, ← u.map_add_eq_mul, ← u.map_add_eq_mul, add_comm]

public theorem characterAverage_spec
    (rho : Representation ℂ G V) (u : AddChar A G) (psi : AddChar A ℂ) :
    LinearMap.IsProj
      (⨅ parameter : A, Module.End.eigenspace (rho (u parameter)) (psi parameter))
      (characterAverage rho u psi) ∧
    (∀ parameter, rho (u parameter) * characterAverage rho u psi =
      psi parameter • characterAverage rho u psi) ∧
    (∀ parameter, characterAverage rho u psi * rho (u parameter) =
      psi parameter • characterAverage rho u psi) := by
  classical
  refine ⟨⟨?_, ?_⟩, characterAverage_left rho u psi, characterAverage_right rho u psi⟩
  · intro vector
    simp only [Submodule.mem_iInf, Module.End.mem_eigenspace_iff]
    intro parameter
    exact LinearMap.congr_fun (characterAverage_left rho u psi parameter) vector
  · intro vector hvector
    have hweight : ∀ parameter, rho (u parameter) vector = psi parameter • vector := by
      simpa only [Submodule.mem_iInf, Module.End.mem_eigenspace_iff] using hvector
    have hcard : (Fintype.card A : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
    simp [characterAverage, LinearMap.sum_apply, hweight, smul_smul,
      (psi.val_isUnit _).ne_zero, ← Nat.cast_smul_eq_nsmul ℂ, hcard]

end Representation
