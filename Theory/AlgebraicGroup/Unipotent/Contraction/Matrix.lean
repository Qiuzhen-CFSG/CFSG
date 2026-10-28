module

public import Theory.AlgebraicGroup.Unipotent.Contraction.Defs
public import Theory.AlgebraicGroup.Variety.AffineDuality
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic

/-!
A regular matrix representation sends a cocharacter-contracted element to a
unipotent matrix, in every characteristic. The characteristic-polynomial
coefficients are regular functions, constant on the conjugation orbit. Their
pullbacks to the contracting affine line are constant away from zero, hence
also at zero. Cayley–Hamilton gives the explicit nilpotence exponent.

This is the linear-algebra step behind the contraction argument used in
Borel, §14.5, and GLS3, §§1.2–1.3 and Theorem 1.11.2.
-/

open Polynomial
namespace Theory.AlgebraicGroup
universe u
variable {k : Type u} [Field k] [IsAlgClosed k]

private theorem contraction_line_constant
    (p : Variety.PolynomialFunction (KPlus k)) (c : k)
    (h : ∀ a : k, a ≠ 0 → p (kPlusPoint a) = c) :
    p (kPlusPoint 0) = c := by
  obtain ⟨q, hq⟩ := p.representedBy
  let Q : Polynomial k := MvPolynomial.uniqueAlgEquiv k PUnit q
  have heval (a : k) : p (kPlusPoint a) = Q.eval a := by
    rw [hq]
    change MvPolynomial.eval₂ (RingHom.id k) (fun _ ↦ a) q = Q.eval a
    rw [← MvPolynomial.eval₂_const_uniqueAlgEquiv]
    rfl
  have hQ : Q = C c := by
    apply Polynomial.eq_of_infinite_eval_eq
    apply (Set.infinite_univ.sdiff (Set.finite_singleton (0 : k))).mono
    intro a ha
    have ha' : a ≠ 0 := ha.2
    change Q.eval a = (C c).eval a
    rw [Polynomial.eval_C, ← heval]
    exact h a ha'
  rw [heval, hQ, Polynomial.eval_C]

variable {G : Variety k} [AlgebraicGroup G]

/-- A contracted element acts unipotently in every finite-dimensional matrix
representation with regular coefficients. No faithfulness is needed. -/
public theorem IsCocharacterContracted.matrix_sub_one_pow_eq_zero
    {n : ℕ} (ρ : Variety.Point G →* Matrix (Fin n) (Fin n) k)
    (c : Matrix (Fin n) (Fin n) (Variety.PolynomialFunction G))
    (hc : ∀ x i j, c i j x = ρ x i j)
    {lambda : AlgebraicGroup.Morphism (KMult k) G} {g : Variety.Point G}
    (hg : IsCocharacterContracted lambda g) : (ρ g - 1) ^ n = 0 := by
  classical
  obtain ⟨f, hf0, hf⟩ := hg
  have hchar (x : Variety.Point G) (i : ℕ) :
      c.charpoly.coeff i x = (ρ x).charpoly.coeff i := by
    let ev := (Variety.PolynomialFunction.evalAlgHom G x).toRingHom
    have hm : c.map ev = ρ x := by
      ext a b
      exact hc x a b
    have hmap := congrArg (fun p : Polynomial k => p.coeff i)
      (Matrix.charpoly_map c ev)
    rw [hm, Polynomial.coeff_map] at hmap
    exact hmap.symm
  have hconj (x : Variety.Point G) :
      (ρ (x⁻¹ * g * x)).charpoly = (ρ g).charpoly := by
    rw [map_mul, map_mul, Matrix.charpoly_mul_comm]
    rw [← mul_assoc, ← map_mul, mul_inv_cancel, map_one, one_mul]
  have heq : (ρ g).charpoly = (1 : Matrix (Fin n) (Fin n) k).charpoly := by
    ext i
    let p := Variety.PolynomialFunction.pullback f (c.charpoly.coeff i)
    have hp : p (kPlusPoint 0) = (ρ g).charpoly.coeff i := by
      apply contraction_line_constant
      intro a ha
      let t : Variety.Point (KMult k) :=
        (dPointEquiv 1).symm (fun _ => Units.mk0 a ha)
      have ht : (dPointEquiv 1 t 0 : k) = a := by
        simp [t]
      change c.charpoly.coeff i (f.toFun (kPlusPoint a)) = _
      rw [← ht, hf, hchar, hconj]
    change c.charpoly.coeff i (f.toFun (kPlusPoint 0)) = _ at hp
    rw [hf0, hchar, map_one] at hp
    exact hp.symm
  have h := Matrix.aeval_self_charpoly (ρ g)
  rw [heq, Matrix.charpoly_one] at h
  simpa using h
end Theory.AlgebraicGroup
