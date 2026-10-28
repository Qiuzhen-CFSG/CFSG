module

public import Theory.AlgebraicGroup.Morphism.FrobeniusPowerDescent
public import Theory.AlgebraicGroup.CoordinateRing.PolynomialFunction

/-!
# Frobenius descent in nonstandard coordinates

The reverse-isogeny construction in `FrobeniusPowerDescent` extends to target
endomorphisms whose coordinates are characteristic powers of polynomial
functions. This condition is invariant under changes of linear coordinates over
a perfect field, unlike literal coordinatewise Frobenius.

First, extract roots of polynomial coefficients and substitute the given
coordinate roots. Then coordinate-power descent makes the inverse point map
composed with the target endomorphism regular. Bijectivity gives surjectivity
and a trivial point kernel. No regularity of the inverse point map is assumed.

This supplies the inseparability step in the version comparison of GLS3,
Chapter 1, §§1.10–1.12 (`refs/KGroup/GLS3/Chapter1.tex`), including presentations
such as the left-regular Clifford carrier with an arbitrary chosen basis.
-/

public section
open Theory.AlgebraicGroup
noncomputable section
universe u
variable {k : Type u} [Field k]

namespace Theory.AlgebraicGroup
variable (p n : ℕ) [ExpChar k p] [PerfectRing k p]

/-- Polynomial expressions in coordinates with polynomial Frobenius roots also
have polynomial Frobenius roots. Constants are handled by perfectness of the field. -/
theorem Variety.exists_polynomial_frobenius_root_of_coordinate_roots {G : Variety k}
    (Fr : Variety.Point G → Variety.Point G)
    (hcoord : ∀ i : G.Coordinates, ∃ f : G.PolynomialFunction,
      ∀ x, (Fr x).val i = (f x) ^ (p ^ n))
    (q : MvPolynomial G.Coordinates k) :
    ∃ f : G.PolynomialFunction, ∀ x,
      evalPolynomial (Fr x).val q = (f x) ^ (p ^ n) := by
  induction q using MvPolynomial.induction_on with
  | C a =>
    refine ⟨algebraMap k _ ((iterateFrobeniusEquiv k p n).symm a), fun x => ?_⟩
    simp only [evalPolynomial, MvPolynomial.eval₂_C]
    rw [polynomialFunction_algebraMap_apply]
    exact ((iterateFrobeniusEquiv k p n).apply_symm_apply a).symm
  | add q r hq hr =>
    obtain ⟨f, hf⟩ := hq
    obtain ⟨g, hg⟩ := hr
    refine ⟨f + g, fun x => ?_⟩
    change evalPolynomial (Fr x).val (q + r) = (f x + g x) ^ (p ^ n)
    simp only [evalPolynomial, MvPolynomial.eval₂_add]
    change evalPolynomial (Fr x).val q + evalPolynomial (Fr x).val r = _
    rw [hf, hg]
    exact (map_add (iterateFrobeniusEquiv k p n) (f x) (g x)).symm
  | mul_X q i hq =>
    obtain ⟨f, hf⟩ := hq
    obtain ⟨g, hg⟩ := hcoord i
    refine ⟨f * g, fun x => ?_⟩
    rw [evalPolynomial_mul, evalPolynomial_X, hf, hg, polynomialFunction_mul_apply,
      mul_pow]

/-- Reverse a surjective morphism after a bijective group endomorphism whose
coordinates have polynomial Frobenius roots. The coordinate presentation need
not be defined over the prime field. -/
theorem Morphism.exists_reverse_isogeny_of_polynomial_frobenius_roots
    {H G : Variety k} [AlgebraicGroup H] [AlgebraicGroup G]
    (φ : Morphism H G) (hsurj : Function.Surjective φ.onPoints)
    (Fr : Monoid.End (Variety.Point G)) (hFr : Function.Bijective Fr)
    (hFrcoord : ∀ i : G.Coordinates, ∃ f : G.PolynomialFunction,
      ∀ x, (Fr x).val i = (f x) ^ (p ^ n))
    (hpow : ∀ i : H.Coordinates, ∃ q : MvPolynomial G.Coordinates k,
      ∀ x : Variety.Point H,
        x.val i ^ (p ^ n) = evalPolynomial (φ.onPoints x).val q) :
    ∃ ψ : Morphism G H, IsIsogeny ψ ∧ (φ.comp ψ).onPoints = Fr := by
  let e : Variety.Point H ≃* Variety.Point G :=
    MulEquiv.ofBijective φ.onPoints
      ⟨φ.toVariety.injective_of_coordinate_frobenius_powers p n hpow, hsurj⟩
  let f : Variety.Point G →* Variety.Point H := e.symm.toMonoidHom.comp Fr
  have hf (x : Variety.Point G) : φ.onPoints (f x) = Fr x :=
    e.apply_symm_apply (Fr x)
  let ψ : Morphism G H :=
    { toVariety :=
        { toFun := f
          regular := by
            intro i
            obtain ⟨q, hq⟩ := hpow i
            obtain ⟨r, hr⟩ :=
              Variety.exists_polynomial_frobenius_root_of_coordinate_roots p n Fr hFrcoord q
            obtain ⟨s, hs⟩ := r.representedBy
            refine ⟨s, fun x => ?_⟩
            apply (iterateFrobeniusEquiv k p n).injective
            change (f x).val i ^ (p ^ n) = _ ^ (p ^ n)
            rw [hq, hf, hr, hs] }
      map_one := f.map_one
      map_mul := f.map_mul }
  have hbij : Function.Bijective ψ.onPoints := e.symm.bijective.comp hFr
  refine ⟨ψ, ⟨hbij.2, ?_⟩, ?_⟩
  · have hker : ψ.kernel = ⊥ := (MonoidHom.ker_eq_bot_iff ψ.onPoints).mpr hbij.1
    rw [hker]
    infer_instance
  · ext x
    exact hf x

end Theory.AlgebraicGroup
