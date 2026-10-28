module

public import Theory.AlgebraicGroup.Unipotent.Contraction.Defs
public import Mathlib.Algebra.Polynomial.Reverse

/-!
# Separation by opposite cocharacter limits

An affine-group element contracted to one by inverse conjugation is the identity
if its direct-conjugation orbit also extends regularly to the affine line.
Coordinate polynomials of the two extensions agree under parameter inversion.
Reversing one polynomial and comparing degrees shows that both are constant.
This works over every infinite field and does not require a faithful matrix
representation or a choice of invariant flag.

This is the contraction separation argument used for opposite root groups in
GLS3, Theorem 1.11.4 and Steinberg (6.2); see
`refs/KGroup/GLS3/Chapter1.tex` and `refs/KGroup/GLS3/Chapter2St2.tex`.
-/

open Polynomial
namespace Theory.AlgebraicGroup

universe u
variable {k : Type u} [Field k] [Infinite k]

private lemma polynomial_constant_of_inverse (p q : Polynomial k)
    (h : ∀ a : k, a ≠ 0 → p.eval a = q.eval a⁻¹) (a b : k) :
    p.eval a = p.eval b := by
  by_cases hp : p = 0
  · simp [hp]
  have he : p * X ^ q.natDegree = q.reverse := by
    apply Polynomial.eq_of_infinite_eval_eq
    apply (Set.infinite_univ.sdiff (Set.finite_singleton (0 : k))).mono
    intro t ht
    have ht' : t ≠ 0 := ht.2
    let _ : Invertible (t⁻¹) := invertibleOfNonzero (inv_ne_zero ht')
    have hr := Polynomial.eval₂_reverse_mul_pow (RingHom.id k) (t⁻¹) q
    have hr' : q.reverse.eval t * (t⁻¹) ^ q.natDegree = q.eval t⁻¹ := by
      simpa [invOf_eq_inv] using hr
    change (p * X ^ q.natDegree).eval t = q.reverse.eval t
    rw [eval_mul, eval_pow, eval_X, h t ht', ← hr']
    rw [mul_assoc, inv_pow, inv_mul_cancel₀ (pow_ne_zero _ ht'), mul_one]
  have hd := congrArg Polynomial.natDegree he
  rw [Polynomial.natDegree_mul_X_pow _ hp] at hd
  have hle := Polynomial.reverse_natDegree_le q
  have hz : p.natDegree = 0 := by omega
  rw [Polynomial.eq_C_of_natDegree_eq_zero hz]
  simp

private lemma curve_constant_of_inverse {V : Variety k} (f q : Variety.Morphism (KPlus k) V)
    (h : ∀ a : k, a ≠ 0 → f.toFun (kPlusPoint a) = q.toFun (kPlusPoint a⁻¹))
    (a b : k) : f.toFun (kPlusPoint a) = f.toFun (kPlusPoint b) := by
  apply Variety.Point.ext
  funext i
  obtain ⟨p, hp⟩ := f.regular i
  obtain ⟨r, hr⟩ := q.regular i
  let P := MvPolynomial.uniqueAlgEquiv k PUnit p
  let R := MvPolynomial.uniqueAlgEquiv k PUnit r
  have hP (t : k) : (f.toFun (kPlusPoint t)).val i = P.eval t := by
    rw [hp]
    change MvPolynomial.eval₂ (RingHom.id k) (fun _ ↦ t) p = P.eval t
    rw [← MvPolynomial.eval₂_const_uniqueAlgEquiv]
    rfl
  have hR (t : k) : (q.toFun (kPlusPoint t)).val i = R.eval t := by
    rw [hr]
    change MvPolynomial.eval₂ (RingHom.id k) (fun _ ↦ t) r = R.eval t
    rw [← MvPolynomial.eval₂_const_uniqueAlgEquiv]
    rfl
  rw [hP, hP]
  apply polynomial_constant_of_inverse P R
  intro t ht
  rw [← hP, ← hR, h t ht]

/-- A contracted element whose opposite conjugation orbit has a regular limit
is the identity. No value for that opposite limit is assumed. -/
public theorem IsCocharacterContracted.eq_one_of_opposite_curve {G : Variety k} [AlgebraicGroup G]
    {lambda : Theory.AlgebraicGroup.Morphism (KMult k) G} {g : Variety.Point G}
    (hg : IsCocharacterContracted lambda g)
    (q : Variety.Morphism (KPlus k) G)
    (hq : ∀ t : Variety.Point (KMult k),
      q.toFun (kPlusPoint (dPointEquiv 1 t 0 : k)) =
        lambda.onPoints t * g * (lambda.onPoints t)⁻¹) : g = 1 := by
  obtain ⟨f, hf0, hf1, hf⟩ := hg.exists_curve
  have hfg : f.toFun (kPlusPoint 1) = f.toFun (kPlusPoint 0) := by
    apply curve_constant_of_inverse f q
    intro a ha
    let t : Variety.Point (KMult k) := (dPointEquiv 1).symm (fun _ => Units.mk0 a ha)
    have ht : (dPointEquiv 1 t 0 : k) = a := by simp [t]
    have hti : (dPointEquiv 1 t⁻¹ 0 : k) = a⁻¹ := by
      let d : Variety.Point (KMult k) →* (Fin 1 → kˣ) :=
        ⟨⟨dPointEquiv 1, dPointEquiv_one 1⟩, dPointEquiv_mul 1⟩
      have hi : dPointEquiv 1 t⁻¹ = (dPointEquiv 1 t)⁻¹ := map_inv d t
      simp only [hi, Pi.inv_apply, Units.val_inv_eq_inv_val, ht]
    rw [← hti, hq, ← ht, hf, map_inv, inv_inv]
  rwa [hf1, hf0] at hfg

end Theory.AlgebraicGroup
