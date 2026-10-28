module
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# A checked minor bounds displacement in a quotient

If selected coordinates vanish on the kernel of a linear quotient, an
invertible minor in those coordinates remains independent in the quotient.
This allows small literal minors to certify a lower bound on the actual
displacement subspace without computing an abstract matrix rank.
-/
public section
namespace BinaryEndpointInduction
open Matrix Module

/-- An invertible coordinate minor survives a quotient whose kernel vanishes
on those coordinates. Its rows force the stated dimension in any subspace
containing their images. -/
theorem card_le_finrank_of_quotient_minor
    {F W ι κ : Type*} [Field F] [AddCommGroup W] [Module F W]
    [Fintype ι] [Fintype κ] [DecidableEq κ]
    (f : (ι → F) →ₗ[F] W) (D : Submodule F W) [FiniteDimensional F D]
    (v : Matrix κ ι F) (cols : κ → ι) (inverse : Matrix κ κ F)
    (hinverse : (v.submatrix id cols) * inverse=1)
    (hker : ∀ x, f x=0 → ∀ j, x (cols j)=0)
    (hmem : ∀ i, f (v i) ∈ D) : Fintype.card κ ≤ finrank F D := by
  classical
  let a : (κ → F) →ₗ[F] W := f.comp v.vecMulLinear
  have ha (x : κ → F) : a x ∈ D := by
    have he : x ᵥ* v=∑ i, x i • v i := by
      ext j
      simp [Matrix.vecMul, dotProduct, Finset.sum_apply]
    change f (x ᵥ* v) ∈ D
    rw [he, map_sum]
    exact D.sum_mem fun i _ => by simpa only [map_smul] using D.smul_mem (x i) (hmem i)
  let b : (κ → F) →ₗ[F] D := a.codRestrict D ha
  have hb : Function.Injective b := by
    apply (injective_iff_map_eq_zero b).mpr
    intro x hx
    have hx0 : f (x ᵥ* v)=0 := congrArg Subtype.val hx
    have hm : x ᵥ* (v.submatrix id cols)=0 := by
      ext j
      exact hker (x ᵥ* v) hx0 j
    calc
      x = x ᵥ* ((v.submatrix id cols) * inverse) := by rw [hinverse, vecMul_one]
      _ = (x ᵥ* (v.submatrix id cols)) ᵥ* inverse := (vecMul_vecMul _ _ _).symm
      _ = 0 := by rw [hm, zero_vecMul]
  simpa using LinearMap.finrank_le_finrank_of_injective hb

end BinaryEndpointInduction
