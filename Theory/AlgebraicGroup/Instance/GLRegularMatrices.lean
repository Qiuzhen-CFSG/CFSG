module

public import Theory.AlgebraicGroup.Instance.GL
public import Theory.AlgebraicGroup.CoordinateRing.Point
public import Mathlib.RingTheory.Ideal.Nonunits

/-!
# Matrices of regular functions

A polynomial matrix whose determinant never vanishes defines a morphism to the
presented general linear group. The inverse determinant is a polynomial
function: otherwise a maximal ideal containing it would give a rational zero
by the affine Nullstellensatz. The exported entry formula preserves the literal
matrix rather than only its abstract invertibility.

This is the local matrix-family construction used in Borel, *Linear Algebraic
Groups*, §10.8 for the inverse on triples of projective-line points.
-/

open scoped MatrixGroups
namespace Theory.AlgebraicGroup
universe u
variable {k : Type u} [Field k] [IsAlgClosed k]
public noncomputable section

private lemma polynomialFunction_isUnit_of_nonzero {V : Variety k}
    (f : Variety.PolynomialFunction V) (hf : ∀ x, f x ≠ 0) : IsUnit f := by
  by_contra hn
  obtain ⟨m, hm, hfm⟩ := exists_max_ideal_of_mem_nonunits hn
  obtain ⟨x, hx⟩ := V.exists_pointPrime_eq_of_isMaximal m hm
  apply hf x
  have hmem : f ∈ (V.pointPrime x).asIdeal := by
    rw [hx]
    exact hfm
  exact hmem

def regularMatrix {V : Variety k} (M : Matrix (Fin 2) (Fin 2) (Variety.PolynomialFunction V))
    (hM : ∀ x : Variety.Point V, (M.map (fun f => f x)).det ≠ 0) :
    Variety.Morphism V (glVariety 2 : Variety k) where
  toFun x := (glPointEquiv 2).symm (Matrix.GeneralLinearGroup.mkOfDetNeZero _ (hM x))
  regular := by
    intro c
    cases c with
    | inl ij =>
        obtain ⟨p, hp⟩ := (M ij.1 ij.2).representedBy
        exact ⟨p, hp⟩
    | inr _ =>
        have hdet (x : Variety.Point V) : M.det x = (M.map (fun f => f x)).det := by
          exact (polynomialFunctionPointAlgHom V x).toRingHom.map_det M
        have hu := polynomialFunction_isUnit_of_nonzero M.det (fun x => by rw [hdet]; exact hM x)
        let inverse : Variety.PolynomialFunction V := (hu.unit⁻¹).val
        obtain ⟨p, hp⟩ := inverse.representedBy
        refine ⟨p, fun x => ?_⟩
        change (M.map (fun f => f x)).det⁻¹ = evalPolynomial x.val p
        rw [← hp]
        have hh : M.det x * inverse x = 1 := by
          change ((hu.unit).val * (hu.unit⁻¹).val) x = 1
          simp
          rfl
        rw [hdet] at hh
        exact (inv_eq_of_mul_eq_one_right hh)

lemma regularMatrix_entries {V : Variety k}
    (M : Matrix (Fin 2) (Fin 2) (Variety.PolynomialFunction V))
    (hM : ∀ x : Variety.Point V, (M.map (fun f => f x)).det ≠ 0)
    (x : Variety.Point V) (i j : Fin 2) :
    (glPointEquiv 2 ((regularMatrix M hM).toFun x)).val i j = M i j x := by
  simp [regularMatrix]

end
end Theory.AlgebraicGroup
