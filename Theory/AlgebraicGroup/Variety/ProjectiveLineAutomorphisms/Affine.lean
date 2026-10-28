module

public import Theory.AlgebraicGroup.Variety.ProjectiveLine
public import Theory.AlgebraicGroup.Variety.AffineGeometricMorphism
public import Mathlib.Algebra.Polynomial.Degree.SmallDegree
public import Mathlib.Algebra.Polynomial.Degree.Lemmas

/-!
# The actual polynomial affine line and its automorphisms

Rational points of Spec k[X] are evaluations, and every morphism over k acts
on those points by the polynomial obtained from its actual Spec pullback of X.
For an inverse pair, multiplicativity of polynomial degree forces degree one.
Fixing zero and one then forces the identity. The pointwise consumer retains
the original scheme morphisms, not a proposed polynomial-action certificate.

This is the affine-chart calculation for projective-line automorphism rigidity
(Borel, Linear Algebraic Groups, 10.8). No separability or characteristic-zero
hypothesis is used; infinitude is only needed for the final polynomial-function
comparison and is available over every algebraically closed field.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
namespace Theory.AlgebraicGroup.Variety.Geometric.ProjectiveLineAutomorphisms
noncomputable section
universe u
variable {k : Type u} [Field k]

def affinePoint (t : k) : Point (polynomialAffineLine k) where
  val := Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom t))
  property := by
    change Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom t)) ≫
      Spec.map (CommRingCat.ofHom (Polynomial.C : k →+* Polynomial k)) = _
    rw [← Spec.map_comp]
    have he : CommRingCat.ofHom (Polynomial.C : k →+* Polynomial k) ≫
        CommRingCat.ofHom (Polynomial.evalRingHom t) = 𝟙 (CommRingCat.of k) := by
      ext r
      simp
    rw [he,Spec.map_id]

theorem affinePoint_injective : Function.Injective (affinePoint (k := k)) := by
  intro a b h
  have hh := congrArg (fun p : Point (polynomialAffineLine k) =>
    (Spec.preimage p.val).hom Polynomial.X) h
  simpa only [affinePoint,Spec.preimage_map,CommRingCat.hom_ofHom,Polynomial.coe_evalRingHom,
    Polynomial.eval_X] using hh

def affinePullback (f : Morphism (polynomialAffineLine k) (polynomialAffineLine k)) :
    Polynomial k →+* Polynomial k := (Spec.preimage f.hom).hom

set_option backward.isDefEq.respectTransparency false in
theorem affinePullback_C (f : Morphism (polynomialAffineLine k) (polynomialAffineLine k))
    (a : k) : affinePullback f (Polynomial.C a) = Polynomial.C a := by
  have h := congrArg Spec.preimage f.commutes
  have h' := congrArg CommRingCat.Hom.hom h
  change (Spec.preimage (f.hom ≫ Spec.map
    (CommRingCat.ofHom (Polynomial.C : k →+* Polynomial k)))).hom =
    (Spec.preimage (Spec.map (CommRingCat.ofHom (Polynomial.C : k →+* Polynomial k)))).hom at h'
  rw [Spec.preimage_comp,Spec.preimage_map,CommRingCat.hom_comp] at h'
  exact DFunLike.congr_fun h' a

def affinePolynomial (f : Morphism (polynomialAffineLine k) (polynomialAffineLine k)) :
    Polynomial k := affinePullback f Polynomial.X

set_option backward.isDefEq.respectTransparency false in
theorem affineMorphism_apply (f : Morphism (polynomialAffineLine k) (polynomialAffineLine k))
    (t : k) : f (affinePoint t) = affinePoint ((affinePolynomial f).eval t) := by
  apply Subtype.ext
  change Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom t)) ≫ f.hom = _
  conv_lhs => rw [← Spec.map_preimage f.hom,← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  apply Polynomial.ringHom_ext
  · intro a
    simp only [CommRingCat.hom_comp,CommRingCat.hom_ofHom,RingHom.comp_apply,
      Polynomial.coe_evalRingHom,Polynomial.eval_C]
    change Polynomial.eval t (affinePullback f (Polynomial.C a)) = a
    rw [affinePullback_C]
    simp
  · simp [CommRingCat.hom_comp,affinePolynomial,affinePullback]

set_option backward.isDefEq.respectTransparency false in
theorem affinePoint_surjective : Function.Surjective (affinePoint (k := k)) := by
  intro p
  refine ⟨(Spec.preimage p.val).hom Polynomial.X,?_⟩
  apply Subtype.ext
  conv_rhs => rw [← Spec.map_preimage p.val]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  apply Polynomial.ringHom_ext
  · intro a
    have h := congrArg Spec.preimage p.property
    have h' := congrArg CommRingCat.Hom.hom h
    change (Spec.preimage (p.val ≫ Spec.map
      (CommRingCat.ofHom (Polynomial.C : k →+* Polynomial k)))).hom =
      (Spec.preimage (𝟙 (Spec (.of k)))).hom at h'
    rw [Spec.preimage_comp,Spec.preimage_map,Spec.preimage_id,CommRingCat.hom_comp] at h'
    simpa only [CommRingCat.hom_id,CommRingCat.hom_ofHom,RingHom.comp_apply,
      RingHom.id_apply,Polynomial.coe_evalRingHom,Polynomial.eval_C] using
      (DFunLike.congr_fun h' a).symm
  · simp

variable [Infinite k]
theorem polynomial_eq_X_of_inverse_fix_zero_one (p q : Polynomial k)
    (hinv : ∀ x, p.eval (q.eval x) = x)
    (h0 : p.eval 0 = 0) (h1 : p.eval 1 = 1) : p = Polynomial.X := by
  have he : p.comp q = Polynomial.X := by
    apply Polynomial.funext
    intro x
    simpa only [Polynomial.eval_comp,Polynomial.eval_X] using hinv x
  have hd := congrArg Polynomial.natDegree he
  rw [Polynomial.natDegree_comp,Polynomial.natDegree_X] at hd
  have hp : p.natDegree ≤ 1 := (Nat.eq_one_of_mul_eq_one_right hd).le
  have hform := Polynomial.eq_X_add_C_of_natDegree_le_one hp
  have hc0 : p.coeff 0 = 0 := (Polynomial.coeff_zero_eq_eval_zero p).trans h0
  have hc1 : p.coeff 1 = 1 := by
    rw [hform] at h1
    simpa [hc0] using h1
  rw [hform,hc0,hc1]
  simp


set_option backward.isDefEq.respectTransparency false in
theorem affineMorphism_pointwise_id_of_inverse_fix_zero_one
    (f g : Morphism (polynomialAffineLine k) (polynomialAffineLine k))
    (hfg : Morphism.comp g f = Morphism.id (polynomialAffineLine k))
    (h0 : f (affinePoint 0) = affinePoint 0)
    (h1 : f (affinePoint 1) = affinePoint 1) :
    ∀ p, f p = p := by
  have hp : affinePolynomial f = Polynomial.X := by
    apply polynomial_eq_X_of_inverse_fix_zero_one _ (affinePolynomial g)
    · intro x
      have hh := congrArg (fun m : Morphism (polynomialAffineLine k) (polynomialAffineLine k) =>
        m (affinePoint x)) hfg
      change f (g (affinePoint x)) = affinePoint x at hh
      rw [affineMorphism_apply g,affineMorphism_apply f] at hh
      exact affinePoint_injective hh
    · rw [affineMorphism_apply] at h0
      exact affinePoint_injective h0
    · rw [affineMorphism_apply] at h1
      exact affinePoint_injective h1
  intro p
  obtain ⟨x,rfl⟩ := affinePoint_surjective p
  rw [affineMorphism_apply,hp,Polynomial.eval_X]

end
end Theory.AlgebraicGroup.Variety.Geometric.ProjectiveLineAutomorphisms
