module

public import Mathlib.LinearAlgebra.QuadraticForm.Basis
public import Mathlib.FieldTheory.ChevalleyWarning
public import Mathlib.FieldTheory.Finiteness
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.Tactic

/-!
# Dimension bound for anisotropic binary quadratic maps

An anisotropic quadratic map of finite binary vector spaces has source
dimension at most twice its target dimension. Choose a bilinear map whose
diagonal is the quadratic map, then express its target coordinates as
polynomials of total degree at most two. If the claimed dimension bound failed,
Chevalley–Warning would make the number of common zeros even, whereas
anisotropy makes the zero vector the unique common zero.

The polynomial divisibility input is Mathlib's Chevalley–Warning theorem,
`char_dvd_card_solutions_of_fintype_sum_lt`.
-/

open Module MvPolynomial
open scoped BigOperators

namespace QuadraticMap

set_option backward.isDefEq.respectTransparency false in
/-- An anisotropic quadratic map between finite binary vector spaces has
source dimension at most twice its target dimension. -/
public theorem finrank_le_twice_of_anisotropic_binary
    {V W : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    (Q : QuadraticMap (ZMod 2) V W) (hQ : Q.Anisotropic) :
    finrank (ZMod 2) V ≤ 2 * finrank (ZMod 2) W := by
  classical
  let n := finrank (ZMod 2) V
  let m := finrank (ZMod 2) W
  let b := finBasis (ZMod 2) V
  let c := finBasis (ZMod 2) W
  let B := Q.toBilin b
  let f (k : Fin m) : MvPolynomial (Fin n) (ZMod 2) :=
    ∑ i, ∑ j, C (c.equivFun (B (b i) (b j)) k) * X i * X j
  have hdegree (k : Fin m) : (f k).totalDegree ≤ 2 := by
    apply (totalDegree_finsetSum _ _).trans
    apply Finset.sup_le
    intro i hi
    apply (totalDegree_finsetSum _ _).trans
    apply Finset.sup_le
    intro j hj
    have h1 := totalDegree_mul (C (c.equivFun (B (b i) (b j)) k) * X i)
      (X j : MvPolynomial (Fin n) (ZMod 2))
    have h2 := totalDegree_mul (C (c.equivFun (B (b i) (b j)) k))
      (X i : MvPolynomial (Fin n) (ZMod 2))
    simp only [totalDegree_C, totalDegree_X, zero_add] at h1 h2
    omega
  have heval (v : V) (k : Fin m) : eval (b.equivFun v) (f k) = c.equivFun (Q v) k := by
    have hB : B v v = Q v :=
      congrArg (fun q : QuadraticMap (ZMod 2) V W => q v) (Q.toQuadraticMap_toBilin b)
    have h : (∑ i, ∑ j, b.repr v i • b.repr v j • B (b i) (b j)) = B v v := by
      calc
        _ = B (∑ i, b.repr v i • b i) (∑ j, b.repr v j • b j) := by
          simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
            Finset.smul_sum]
          rw [Finset.sum_comm]
          congr 1
          funext i
          congr 1
          funext j
          exact smul_comm _ _ _
        _ = B v v := by rw [b.sum_repr]
    have hh := congrArg (fun w : W => c.equivFun w k) h
    simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hh
    rw [hB] at hh
    rw [← hh]
    simp only [f, eval_sum, eval_mul, eval_C, eval_X]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    change _ * b.repr v i * b.repr v j = b.repr v i * (b.repr v j * _)
    ring
  by_contra hnot
  have hlt : (∑ k : Fin m, (f k).totalDegree) < Fintype.card (Fin n) := by
    have hh := Finset.sum_le_sum (fun k (_ : k ∈ (Finset.univ : Finset (Fin m))) => hdegree k)
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hh
    simp only [Fintype.card_fin]
    change ¬ n ≤ 2 * m at hnot
    omega
  have hdiv := char_dvd_card_solutions_of_fintype_sum_lt (K := ZMod 2) 2 hlt
  let zeros := {x : Fin n → ZMod 2 // ∀ k, eval x (f k) = 0}
  have hzero (x : zeros) : x.val = 0 := by
    have hv : Q (b.equivFun.symm x.val) = 0 := by
      apply c.equivFun.injective
      apply funext
      intro k
      have hh := heval (b.equivFun.symm x.val) k
      rw [LinearEquiv.apply_symm_apply, x.property k] at hh
      simpa only [map_zero, Pi.zero_apply] using hh.symm
    have hx := congrArg b.equivFun (hQ _ hv)
    simpa only [LinearEquiv.apply_symm_apply, map_zero] using hx
  let : Unique zeros :=
    { default := ⟨0, by intro k; simp [f]⟩
      uniq x := Subtype.ext (hzero x) }
  have hbad : 2 ∣ 1 := by
    simpa only [Fintype.card_unique] using hdiv
  norm_num at hbad

end QuadraticMap
