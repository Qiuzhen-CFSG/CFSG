module

public import Mathlib.RingTheory.Derivation.Basic
public import Theory.AlgebraicGroup.Representations.Algebraic.WeightSetFinite
public import Theory.AlgebraicGroup.RootSubgroups.Tangent
import all Theory.AlgebraicGroup.RootSubgroups.Tangent

/-!
# Tangent rigidity and finite root sets

This module builds on the public identity-tangent API in
`RootSubgroups.Tangent`.  Its rigidity theorem compares two equivariant
one-parameter curves with proportional tangents.  Their least unequal
coefficient would give a nonzero higher inverse-character weight vector, so
the absence of such weights forces the ambient curves to agree after scalar
rescaling.  The private import of the tangent module is intentional: it gives
this proof access to the polynomial implementation lemmas without exposing
those lemmas as public API.

The resulting tangent weight vectors also embed the torus root set into the
finite weight set of a finite-dimensional rational representation.  These are
lower-layer inputs for root-weight multiplicity one in GLS3 Theorem 1.9.5(b);
no unresolved clause of that theorem is used.
-/

universe u

namespace Theory.AlgebraicGroup

variable {k : Type u} [Field k] [IsAlgClosed k]

omit [IsAlgClosed k] in
private lemma coefficient_mul_of_coeff_lt_eq_zero
    (n : Nat) (p q : Polynomial k)
    (hp : ∀ m, m < n → p.coeff m = 0) :
    (p * q).coeff n = p.coeff n * q.coeff 0 := by
  rw [Polynomial.coeff_mul]
  apply Finset.sum_eq_single (n, 0)
  · intro ij hij hne
    rw [Finset.mem_antidiagonal] at hij
    have hle : ij.1 ≤ n := by omega
    have hlt : ij.1 < n := lt_of_le_of_ne hle (by
      intro heq
      apply hne
      apply Prod.ext
      · exact heq
      · omega)
    rw [hp ij.1 hlt, zero_mul]
  · simp

omit [IsAlgClosed k] in
private lemma coefficient_mul_of_coeff_lt_eq_zero_right
    (n : Nat) (p q : Polynomial k)
    (hq : ∀ m, m < n → q.coeff m = 0) :
    (p * q).coeff n = p.coeff 0 * q.coeff n := by
  rw [mul_comm]
  simpa [mul_comm] using coefficient_mul_of_coeff_lt_eq_zero n q p hq

/-- Proportional tangents of equivariant one-parameter curves integrate to the
corresponding ambient scalar rescaling when no higher inverse-character weight
can carry a Frobenius discrepancy.

The higher-weight hypothesis is essential in positive characteristic: an
equivariant additive curve may acquire terms of degree `p ^ r` whose first
derivative vanishes.  The proof takes the least degree at which the two
coordinate pullbacks differ and shows that its coefficient difference is a
nonzero derivation of weight `(chi⁻¹) ^ n`. -/
public theorem includePoint_eq_rescale_of_oneParameterTangent_eq_smul
    {K : Variety k} [AlgebraicGroup K]
    (T X Y : ClosedSubgroup K) {χ : TorusWeight T}
    (hXχ : RootWeightEquation T X χ)
    (hYχ : RootWeightEquation T Y χ)
    (x : OneParameterParametrization X.carrierVariety)
    (y : OneParameterParametrization Y.carrierVariety)
    (higherWeights : ∀ n : Nat, 2 ≤ n →
      weightSpace (identityTangentRepresentation K) T ((χ⁻¹) ^ n) = ⊥)
    (c : k) (hc : c ≠ 0)
    (htangent : oneParameterTangent X x = c • oneParameterTangent Y y) :
    ∀ t : k,
      X.includePoint (x.value t) = Y.includePoint (y.value (c * t)) := by
  classical
  let y' : OneParameterParametrization Y.carrierVariety := y.rescale c hc
  have htangent' : oneParameterTangent X x = oneParameterTangent Y y' := by
    rw [oneParameterTangent_rescale Y y c hc]
    exact htangent
  let φ : Variety.PolynomialFunction K →ₐ[k] Polynomial k :=
    kPlusPolynomialFunctionAlgEquiv.toAlgHom.comp
      (X.inclusion.comp x.hom).toVariety.pullbackAlgHom
  let ψ : Variety.PolynomialFunction K →ₐ[k] Polynomial k :=
    kPlusPolynomialFunctionAlgEquiv.toAlgHom.comp
      (Y.inclusion.comp y'.hom).toVariety.pullbackAlgHom
  have hXinc (z : Variety.Point X.carrierVariety) :
      X.includePoint z = X.inclusion.onPoints z := by
    apply Variety.Point.ext
    funext i
    rfl
  have hYinc (z : Variety.Point Y.carrierVariety) :
      Y.includePoint z = Y.inclusion.onPoints z := by
    apply Variety.Point.ext
    funext i
    rfl
  have hTinc (z : Variety.Point T.carrierVariety) :
      T.includePoint z = T.inclusion.onPoints z := by
    apply Variety.Point.ext
    funext i
    rfl
  have hφ_zero (f : Variety.PolynomialFunction K) :
      (φ f).coeff 0 = f 1 := by
    change (kPlusPolynomialFunctionAlgEquiv
      ((X.inclusion.comp x.hom).toVariety.pullbackAlgHom f)).coeff 0 = f 1
    rw [Polynomial.coeff_zero_eq_eval_zero,
      kPlusPolynomialFunctionAlgEquiv_eval, kPlusPoint_zero]
    change f ((X.inclusion.comp x.hom).onPoints 1) = f 1
    rw [map_one]
  have hψ_zero (f : Variety.PolynomialFunction K) :
      (ψ f).coeff 0 = f 1 := by
    change (kPlusPolynomialFunctionAlgEquiv
      ((Y.inclusion.comp y'.hom).toVariety.pullbackAlgHom f)).coeff 0 = f 1
    rw [Polynomial.coeff_zero_eq_eval_zero,
      kPlusPolynomialFunctionAlgEquiv_eval, kPlusPoint_zero]
    change f ((Y.inclusion.comp y'.hom).onPoints 1) = f 1
    rw [map_one]
  have hφ_one (f : Variety.PolynomialFunction K) :
      (φ f).coeff 1 = (ψ f).coeff 1 := by
    have h := congrArg (fun D : IdentityPointDerivation K ↦ D f) htangent'
    rw [oneParameterTangent_apply, oneParameterTangent_apply,
      kPlusIdentityDerivation_apply, kPlusIdentityDerivation_apply] at h
    change (φ f).derivative.eval 0 = (ψ f).derivative.eval 0 at h
    simpa [← Polynomial.coeff_zero_eq_eval_zero,
      Polynomial.coeff_derivative] using h
  by_contra hne
  push Not at hne
  have hmaps_ne : φ ≠ ψ := by
    intro heq
    obtain ⟨t, ht⟩ := hne
    apply ht
    apply Variety.Point.ext
    funext i
    let f : Variety.PolynomialFunction K :=
      Variety.PolynomialFunction.ofPolynomial K (MvPolynomial.X i)
    have hpoly := DFunLike.congr_fun heq f
    have heval := congrArg (Polynomial.eval t) hpoly
    change (kPlusPolynomialFunctionAlgEquiv
      ((X.inclusion.comp x.hom).toVariety.pullbackAlgHom f)).eval t =
      (kPlusPolynomialFunctionAlgEquiv
        ((Y.inclusion.comp y'.hom).toVariety.pullbackAlgHom f)).eval t at heval
    rw [kPlusPolynomialFunctionAlgEquiv_eval,
      kPlusPolynomialFunctionAlgEquiv_eval] at heval
    change f (X.inclusion.onPoints (x.hom.onPoints (kPlusPoint t))) =
      f (Y.inclusion.onPoints (y'.hom.onPoints (kPlusPoint t))) at heval
    rw [hXinc, hYinc]
    change (X.inclusion.onPoints (x.hom.onPoints (kPlusPoint t))).val i =
      (Y.inclusion.onPoints ((y.rescale c hc).hom.onPoints (kPlusPoint t))).val i
    dsimp [f, Variety.PolynomialFunction.toFun,
      Variety.PolynomialFunction.ofPolynomial] at heval
    simpa only [evalPolynomial_X] using heval
  have hexists : ∃ n : Nat, ∃ f : Variety.PolynomialFunction K,
      (φ f).coeff n ≠ (ψ f).coeff n := by
    by_contra h
    push Not at h
    apply hmaps_ne
    ext f n
    exact h n f
  let n : Nat := Nat.find hexists
  obtain ⟨f₀, hf₀⟩ := Nat.find_spec hexists
  change (φ f₀).coeff n ≠ (ψ f₀).coeff n at hf₀
  have hlower (m : Nat) (hm : m < n) (f : Variety.PolynomialFunction K) :
      (φ f).coeff m = (ψ f).coeff m := by
    by_contra hcoeff
    exact Nat.find_min hexists hm ⟨f, hcoeff⟩
  have hn₀ : n ≠ 0 := by
    intro hn
    rw [hn] at hf₀
    exact hf₀ ((hφ_zero f₀).trans (hψ_zero f₀).symm)
  have hn₁ : n ≠ 1 := by
    intro hn
    rw [hn] at hf₀
    exact hf₀ (hφ_one f₀)
  have hn₂ : 2 ≤ n := by omega
  let D : IdentityPointDerivation K :=
    { toLinearMap :=
        { toFun := fun f ↦ (φ f).coeff n - (ψ f).coeff n
          map_add' := by
            intro f g
            simp
            ring
          map_smul' := by
            intro a f
            simp [smul_eq_mul, mul_sub] }
      map_one_eq_zero' := by simp
      leibniz' := by
        intro f g
        have hφψ_f (m : Nat) (hm : m < n) :
            (φ f - ψ f).coeff m = 0 := by
          rw [Polynomial.coeff_sub, hlower m hm f, sub_self]
        have hφψ_g (m : Nat) (hm : m < n) :
            (φ g - ψ g).coeff m = 0 := by
          rw [Polynomial.coeff_sub, hlower m hm g, sub_self]
        change (φ (f * g)).coeff n - (ψ (f * g)).coeff n =
          f 1 * ((φ g).coeff n - (ψ g).coeff n) +
            g 1 * ((φ f).coeff n - (ψ f).coeff n)
        rw [map_mul, map_mul]
        have hidentity : φ f * φ g - ψ f * ψ g =
            (φ f - ψ f) * ψ g + φ f * (φ g - ψ g) := by ring
        rw [← Polynomial.coeff_sub, hidentity, Polynomial.coeff_add,
          coefficient_mul_of_coeff_lt_eq_zero n (φ f - ψ f) (ψ g)
            hφψ_f,
          coefficient_mul_of_coeff_lt_eq_zero_right n (φ f) (φ g - ψ g)
            hφψ_g,
          Polynomial.coeff_sub, Polynomial.coeff_sub,
          hψ_zero, hφ_zero]
        ring }
  have hD_ne : D ≠ 0 := by
    intro hD
    have := congrArg (fun E : IdentityPointDerivation K ↦ E f₀) hD
    change (φ f₀).coeff n - (ψ f₀).coeff n = 0 at this
    exact hf₀ (sub_eq_zero.mp this)
  have hD_weight : D ∈ weightSpace (identityTangentRepresentation K) T
      ((χ⁻¹) ^ n) := by
    intro s
    apply Derivation.ext
    intro f
    let a : k := (χ⁻¹).pointCharacter s
    have hφ_scale : φ
        ((AlgebraicGroup.conjugationByMorphism K (T.includePoint s)).pullbackAlgHom f) =
        (φ f).comp (Polynomial.C a * Polynomial.X) := by
      apply Polynomial.funext
      intro t
      change (kPlusPolynomialFunctionAlgEquiv
          ((X.inclusion.comp x.hom).toVariety.pullbackAlgHom
            ((AlgebraicGroup.conjugationByMorphism K
              (T.includePoint s)).pullbackAlgHom f))).eval t =
        Polynomial.eval t
          ((kPlusPolynomialFunctionAlgEquiv
            ((X.inclusion.comp x.hom).toVariety.pullbackAlgHom f)).comp
              (Polynomial.C a * Polynomial.X))
      rw [Polynomial.eval_comp, Polynomial.eval_mul, Polynomial.eval_C,
        Polynomial.eval_X, kPlusPolynomialFunctionAlgEquiv_eval,
        kPlusPolynomialFunctionAlgEquiv_eval]
      change f ((AlgebraicGroup.conjugationByMorphism K (T.includePoint s)).toFun
          (X.inclusion.onPoints (x.value t))) =
        f (X.inclusion.onPoints (x.value (a * t)))
      congr 1
      rw [AlgebraicGroup.conjugationByMorphism_apply]
      have hroot := hXχ x t s⁻¹
      simp_rw [hXinc] at hroot
      rw [hTinc, map_inv, inv_inv] at hroot
      change T.inclusion.onPoints s *
          X.inclusion.onPoints (x.hom.onPoints (kPlusPoint t)) *
            (T.inclusion.onPoints s)⁻¹ =
        X.inclusion.onPoints
          (x.hom.onPoints (kPlusPoint (χ.pointCharacter s⁻¹ * t))) at hroot
      rw [hTinc]
      simpa [a, OneParameterParametrization.value,
        TorusCharacter.pointCharacter_inv_apply,
        TorusCharacter.pointCharacter_apply_inv] using hroot
    have hψ_scale : ψ
        ((AlgebraicGroup.conjugationByMorphism K (T.includePoint s)).pullbackAlgHom f) =
        (ψ f).comp (Polynomial.C a * Polynomial.X) := by
      apply Polynomial.funext
      intro t
      change (kPlusPolynomialFunctionAlgEquiv
          ((Y.inclusion.comp y'.hom).toVariety.pullbackAlgHom
            ((AlgebraicGroup.conjugationByMorphism K
              (T.includePoint s)).pullbackAlgHom f))).eval t =
        Polynomial.eval t
          ((kPlusPolynomialFunctionAlgEquiv
            ((Y.inclusion.comp y'.hom).toVariety.pullbackAlgHom f)).comp
              (Polynomial.C a * Polynomial.X))
      rw [Polynomial.eval_comp, Polynomial.eval_mul, Polynomial.eval_C,
        Polynomial.eval_X, kPlusPolynomialFunctionAlgEquiv_eval,
        kPlusPolynomialFunctionAlgEquiv_eval]
      change f ((AlgebraicGroup.conjugationByMorphism K (T.includePoint s)).toFun
          (Y.inclusion.onPoints (y'.value t))) =
        f (Y.inclusion.onPoints (y'.value (a * t)))
      congr 1
      rw [AlgebraicGroup.conjugationByMorphism_apply]
      have hroot := hYχ y' t s⁻¹
      simp_rw [hYinc] at hroot
      rw [hTinc, map_inv, inv_inv] at hroot
      change T.inclusion.onPoints s *
          Y.inclusion.onPoints (y'.hom.onPoints (kPlusPoint t)) *
            (T.inclusion.onPoints s)⁻¹ =
        Y.inclusion.onPoints
          (y'.hom.onPoints (kPlusPoint (χ.pointCharacter s⁻¹ * t))) at hroot
      rw [hTinc]
      simpa [a, OneParameterParametrization.value,
        TorusCharacter.pointCharacter_inv_apply,
        TorusCharacter.pointCharacter_apply_inv] using hroot
    change D
        ((AlgebraicGroup.conjugationByMorphism K (T.includePoint s)).pullbackAlgHom f) =
      (((χ⁻¹) ^ n).pointCharacter s) • D f
    change
      (φ ((AlgebraicGroup.conjugationByMorphism K
        (T.includePoint s)).pullbackAlgHom f)).coeff n -
        (ψ ((AlgebraicGroup.conjugationByMorphism K
          (T.includePoint s)).pullbackAlgHom f)).coeff n = _
    rw [hφ_scale, hψ_scale,
      Polynomial.comp_C_mul_X_coeff, Polynomial.comp_C_mul_X_coeff]
    change (φ f).coeff n * a ^ n - (ψ f).coeff n * a ^ n =
      (((χ⁻¹) ^ n).pointCharacter s) *
        ((φ f).coeff n - (ψ f).coeff n)
    have hpow : ((((χ⁻¹) ^ n).pointCharacter s : k)) = a ^ n := by
      induction n with
      | zero =>
          rw [pow_zero, pow_zero]
          change (1 : k) = 1
          rfl
      | succ n ih =>
          rw [pow_succ, pow_succ]
          change ((((χ⁻¹) ^ n).pointCharacter s : k) *
              ((χ⁻¹).pointCharacter s : k)) =
            a ^ n * a
          rw [ih]
    rw [hpow]
    change _ = a ^ n * _
    ring
  have hD_zero : D = 0 := by
    have hbot : D ∈ (⊥ : Submodule k (IdentityPointDerivation K)) := by
      rw [← higherWeights n hn₂]
      exact hD_weight
    simpa using hbot
  exact hD_ne hD_zero

/-- The set of weights of torus-invariant one-parameter closed subgroups is finite. -/
public theorem torusRootSet_finite
    {K : Variety k} [AlgebraicGroup K] (T : ClosedSubgroup K) :
    (TorusRootSet T).Finite := by
  apply Set.Finite.of_finite_image
  · apply (representationWeights_finite (identityTangentRepresentation K) T).subset
    rintro ψ ⟨χ, hχ, rfl⟩
    rcases hχ with ⟨X, hX, hweight⟩
    let x : OneParameterParametrization X.carrierVariety := Classical.choice hX.2
    have hv := oneParameterTangent_isWeightVector T X x hweight
    intro hbot
    have hmem : oneParameterTangent X x ∈
        weightSpace (identityTangentRepresentation K) T χ⁻¹ := hv.2
    rw [hbot] at hmem
    exact hv.1 hmem
  · intro χ _ ψ _ h
    exact inv_injective h

end Theory.AlgebraicGroup
