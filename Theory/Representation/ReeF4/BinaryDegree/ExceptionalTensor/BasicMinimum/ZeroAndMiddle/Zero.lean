module

public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.BasicMinimum.ZeroAndMiddle.Geometry
public import Theory.AlgebraicGroup.Representations.Operations
public import Mathlib.Algebra.Polynomial.Reverse

/-!
# Negative-simple-root fixation at highest weight zero

For a vector fixed by the positive simple root and its coroot, the rank-one
normalizer relation makes the coroot fix its Weyl translate as well. The
normalizer word expresses the negative-root orbit on the punctured affine
line as the positive-root orbit of that translate at the inverse parameter.
Rationality supplies polynomial matrix coefficients on both root curves.
A polynomial in `t` that is also a polynomial in `t⁻¹` is constant; evaluation
at zero therefore proves fixation by the negative simple root.

This is the zero-exponent version of the rank-one polynomial argument in
`Representations/Algebraic/SL2HighestWeight.lean`, applied directly to the
actual F4 curves and their checked coroot identities. In particular it needs
no uninstantiated SL2 embedding or Borel big-cell package.
Source: GLS3, §1.14, especially the uniqueness assertion in 1.14.6(c).
-/

public section

open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
namespace ReeF4.BinaryDegree.ExceptionalTensor.ZeroAndMiddle
noncomputable section
universe u v
variable {k : Type u} [Field k] [IsAlgClosed k]
private noncomputable def additiveCurveCoefficientPolynomial
    {G : Variety k} [AlgebraicGroup G]
    {V : Type v} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (rho : RationalRepresentation G V)
    (e : Module.Basis (Fin (Module.finrank k V)) k V)
    (f : Theory.AlgebraicGroup.Morphism G (glVarietyOf k V))
    (curve : Theory.AlgebraicGroup.Morphism (KPlus k) G)
    (l : Module.Dual k V) (x : V) : Polynomial k :=
  let c : Variety.PolynomialFunction (KPlus k) :=
    Variety.PolynomialFunction.pullback curve.toVariety
      (rationalRepresentationLinearMatrixCoefficient rho e f l x)
  MvPolynomial.uniqueAlgEquiv k PUnit (Classical.choose c.representedBy)

private lemma additiveCurveCoefficientPolynomial_eval
    {G : Variety k} [AlgebraicGroup G]
    {V : Type v} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (rho : RationalRepresentation G V)
    (e : Module.Basis (Fin (Module.finrank k V)) k V)
    (f : Theory.AlgebraicGroup.Morphism G (glVarietyOf k V))
    (hf : ∀ g, glPointEquivOf k V e (f.onPoints g) = rho.action g)
    (curve : Theory.AlgebraicGroup.Morphism (KPlus k) G)
    (l : Module.Dual k V) (x : V) (t : k) :
    (additiveCurveCoefficientPolynomial rho e f curve l x).eval t =
      l ((rho.action (curve.onPoints (kPlusPoint t)) : Module.End k V) x) := by
  let c : Variety.PolynomialFunction (KPlus k) :=
    Variety.PolynomialFunction.pullback curve.toVariety
      (rationalRepresentationLinearMatrixCoefficient rho e f l x)
  let r : MvPolynomial PUnit k := Classical.choose c.representedBy
  have hr := Classical.choose_spec c.representedBy (kPlusPoint t)
  calc
    (additiveCurveCoefficientPolynomial rho e f curve l x).eval t =
        (MvPolynomial.uniqueAlgEquiv k PUnit r).eval t := by rfl
    _ = MvPolynomial.eval₂ (RingHom.id k) (fun _ ↦ t) r := by
      simpa using
        (MvPolynomial.eval₂_const_uniqueAlgEquiv
          (R := k) (S := k) (f := r) (φ := RingHom.id k) (a := t))
    _ = evalPolynomial (kPlusPoint t).val r := by rfl
    _ = c (kPlusPoint t) := hr.symm
    _ = rationalRepresentationLinearMatrixCoefficient rho e f l x
        (curve.onPoints (kPlusPoint t)) := rfl
    _ = l ((rho.action (curve.onPoints (kPlusPoint t)) : Module.End k V) x) :=
      rationalRepresentationLinearMatrixCoefficient_apply rho e f hf l x _

omit [IsAlgClosed k] in
private lemma eval_reflect_natDegree (q : Polynomial k) (t : k) (ht : t ≠ 0) :
    (q.reflect q.natDegree).eval t = t ^ q.natDegree * q.eval t⁻¹ := by
  let _ : Invertible (t⁻¹) := invertibleOfNonzero (inv_ne_zero ht)
  have h := Polynomial.eval₂_reflect_mul_pow (RingHom.id k) (t⁻¹)
    q.natDegree q le_rfl
  have h' : (q.reflect q.natDegree).eval t * (t⁻¹) ^ q.natDegree =
      q.eval t⁻¹ := by
    simpa [invOf_eq_inv] using h
  calc
    (q.reflect q.natDegree).eval t =
        ((q.reflect q.natDegree).eval t * (t⁻¹) ^ q.natDegree) *
          t ^ q.natDegree := by
      rw [mul_assoc, inv_pow, inv_mul_cancel₀ (pow_ne_zero q.natDegree ht), mul_one]
    _ = q.eval t⁻¹ * t ^ q.natDegree := by rw [h']
    _ = t ^ q.natDegree * q.eval t⁻¹ := mul_comm _ _


private theorem reciprocal_polynomial_constant (p q : Polynomial k)
    (h : ∀ t : k, t ≠ 0 → p.eval t = q.eval t⁻¹) (t : k) :
    p.eval t = p.eval 0 := by
  have he : Polynomial.X ^ q.natDegree * p = q.reflect q.natDegree := by
    apply Polynomial.eq_of_infinite_eval_eq
    apply (Set.infinite_of_finite_compl
      (by simp : ({t : k | t ≠ 0} : Set k)ᶜ.Finite)).mono
    intro t ht
    simp only [Set.mem_ofPred_eq] at ht ⊢
    rw [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X, h t ht,
      eval_reflect_natDegree q t ht]
  have hp : p = Polynomial.C (p.eval 0) := by
    ext n
    cases n with
    | zero => simp [Polynomial.coeff_zero_eq_eval_zero]
    | succ n =>
      have hh := congrArg (fun f : Polynomial k => f.coeff (n + 1 + q.natDegree)) he
      rw [Polynomial.coeff_X_pow_mul] at hh
      have hd : (q.reflect q.natDegree).natDegree < n + 1 + q.natDegree :=
        lt_of_le_of_lt (by simpa using (Polynomial.natDegree_reflect_le (p := q) (N := q.natDegree)))
          (by omega)
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt hd] at hh
      simpa using hh
  rw [hp]
  simp

variable {F : Type u} [Field F] [IsAlgClosed F] [CharP F 2]
local instance : InvolutiveNeg F4Chevalley.Root := typeF4RootPairing.indexNeg

private theorem root_mul_self (r : F4Chevalley.Root) (t : F) :
    algebraicRootElement r t * algebraicRootElement r t = 1 := by
  have hi : (algebraicRootElement r t)⁻¹ = algebraicRootElement r t := by
    rw [root_inv, CharTwo.neg_eq]
  calc
    _ = algebraicRootElement r t * (algebraicRootElement r t)⁻¹ := by rw [hi]
    _ = 1 := mul_inv_cancel _

private theorem lower_bruhat (r : F4Chevalley.Root) (t : F) (ht : t ≠ 0) :
    algebraicRootElement (-r) t =
      algebraicRootElement r t⁻¹ *
        (algebraicCorootElement r (Units.mk0 t ht)⁻¹ * algebraicNElement r 1) *
        algebraicRootElement r t⁻¹ := by
  have he : algebraicCorootElement r (Units.mk0 t ht)⁻¹ * algebraicNElement r 1 =
      algebraicNElement r (Units.mk0 t ht)⁻¹ := by
    rw [algebraicCorootElement]
    group
  rw [he]
  have hn : algebraicNElement r (Units.mk0 t ht)⁻¹ =
      algebraicRootElement r t⁻¹ * algebraicRootElement (-r) t *
        algebraicRootElement r t⁻¹ := by
    simp [algebraicNElement, CharTwo.neg_eq]
  rw [hn]
  simp only [← mul_assoc, root_mul_self, one_mul]
  rw [mul_assoc, root_mul_self, mul_one]

/-- The rank-one zero-exponent argument on the actual root curves. -/
theorem negative_simple_fixed_of_zero (B : AlgebraicFactor F) (v : B.Space)
    (hupper : ∀ i : Fin 4, ∀ t : F,
      (B.action.action (algebraicRootElement (typeF4SimpleRootIndex i) t) : Module.End F B.Space) v = v)
    (htorus : ∀ i : Fin 4, ∀ t : Fˣ,
      (B.action.action (algebraicCorootElement (typeF4SimpleRootIndex i) t) : Module.End F B.Space) v = v)
    (i : Fin 4) (t : F) :
    (B.action.action (algebraicRootElement (-typeF4SimpleRootIndex i) t) : Module.End F B.Space) v = v := by
  obtain ⟨e, f, hf⟩ := B.irreducible.1
  let wx := (B.action.action (algebraicNElement (typeF4SimpleRootIndex i) 1) : Module.End F B.Space) v
  have hdiag (s : Fˣ) :
      (B.action.action (algebraicCorootElement (typeF4SimpleRootIndex i) s) : Module.End F B.Space) wx = wx := by
    dsimp only [wx]
    change ((B.action.action _ * B.action.action _ : LinearMap.GeneralLinearGroup F B.Space) : Module.End F B.Space) v = _
    rw [← map_mul, coroot_n_inverse, map_mul]
    change (B.action.action _ : Module.End F B.Space)
      ((B.action.action _ : Module.End F B.Space) v) = _
    rw [htorus]
  have hcoeff (l : Module.Dual F B.Space) :
      l ((B.action.action (algebraicRootElement (-typeF4SimpleRootIndex i) t) : Module.End F B.Space) v) = l v := by
    let p := additiveCurveCoefficientPolynomial B.action e f
      (F4Chevalley.rootMorphism (-typeF4SimpleRootIndex i)) l v
    let q := additiveCurveCoefficientPolynomial B.action e f
      (F4Chevalley.rootMorphism (typeF4SimpleRootIndex i)) l wx
    have hp (s : F) : p.eval s =
        l ((B.action.action (algebraicRootElement (-typeF4SimpleRootIndex i) s) : Module.End F B.Space) v) :=
      additiveCurveCoefficientPolynomial_eval B.action e f hf _ l v s
    have hq (s : F) : q.eval s =
        l ((B.action.action (algebraicRootElement (typeF4SimpleRootIndex i) s) : Module.End F B.Space) wx) :=
      additiveCurveCoefficientPolynomial_eval B.action e f hf _ l wx s
    have hpq (s : F) (hs : s ≠ 0) : p.eval s = q.eval s⁻¹ := by
      rw [hp, hq, lower_bruhat _ s hs, map_mul, map_mul, map_mul]
      change l ((B.action.action _ : Module.End F B.Space)
        ((B.action.action _ : Module.End F B.Space)
          ((B.action.action _ : Module.End F B.Space)
            ((B.action.action _ : Module.End F B.Space) v)))) = _
      rw [hupper]
      change l ((B.action.action _ : Module.End F B.Space)
        ((B.action.action _ : Module.End F B.Space) wx)) = _
      rw [hdiag]
    have heq := reciprocal_polynomial_constant p q hpq t
    rw [hp, hp, root_zero, map_one] at heq
    exact heq
  by_contra hne
  obtain ⟨l, hl⟩ := Module.Projective.exists_dual_eq_one F (sub_ne_zero.mpr hne)
  have heq := hcoeff l
  rw [map_sub, heq, sub_self] at hl
  exact zero_ne_one hl

end
end ReeF4.BinaryDegree.ExceptionalTensor.ZeroAndMiddle
