module

public import Mathlib.Algebra.CharP.Algebra
public import Theory.AlgebraicGroup.Jordan.Basic
public import Theory.AlgebraicGroup.Morphism.Basic
public import Theory.AlgebraicGroup.Variety.Iterate

universe u

/-! Finite-order criteria for semisimple and unipotent elements. -/

namespace Theory.AlgebraicGroup

open Polynomial

variable {k : Type u} [Field k]

public theorem pPowerOrder_implies_unipotent {G : Variety k} [AlgebraicGroup G]
    (g : Variety.Point G) (p n : ℕ) [CharP k p] [Fact p.Prime]
    (hg : g ^ p ^ n = 1) :
    IsUnipotentElement G g := by
  simp only [IsUnipotentElement]
  intro f
  refine ⟨p ^ n, ?_⟩
  have hcom : Commute (rightTranslationPullback G g)
      (1 : Module.End k (Variety.PolynomialFunction G)) :=
    Commute.one_right _
  have : FaithfulSMul k (Module.End k (Variety.PolynomialFunction G)) :=
    faithfulSMul_end G
  have : ExpChar (Module.End k (Variety.PolynomialFunction G)) p :=
    expChar_of_injective_algebraMap (R := k) (A := Module.End k (Variety.PolynomialFunction G))
      (FaithfulSMul.algebraMap_injective k (Module.End k (Variety.PolynomialFunction G))) p
  have hfrob : (rightTranslationPullback G g - 1 : Module.End k (Variety.PolynomialFunction G)) ^ p ^ n =
      (rightTranslationPullback G g) ^ p ^ n - 1 := by
    simpa using sub_pow_expChar_pow_of_commute (R := Module.End k (Variety.PolynomialFunction G)) p n hcom
  have hpow : (rightTranslationPullback G g) ^ p ^ n =
      (1 : Module.End k (Variety.PolynomialFunction G)) := by
    apply LinearMap.ext
    intro x
    rw [Module.End.pow_apply]
    rw [rightTranslationPullback_pow G g (p ^ n)]
    rw [hg]
    simp [rightTranslationPullback, Variety.Morphism.pullbackAlgHom,
      Variety.Morphism.pullbackRingHom, Variety.PolynomialFunction.pullback,
      AlgebraicGroup.rightMulMorphism_apply, mul_one]
    rfl
  have hzero : (rightTranslationPullback G g - 1 : Module.End k (Variety.PolynomialFunction G)) ^ p ^ n = 0 := by
    rw [hfrob, hpow]
    simp
  change ((rightTranslationPullback G g) -
    (1 : Variety.PolynomialFunction G →ₗ[k] Variety.PolynomialFunction G))^[p ^ n] f = 0
  rw [← Module.End.pow_apply]
  exact congrArg (fun φ : Module.End k (Variety.PolynomialFunction G) => φ f) hzero

/-- Proposition 1.2.2(e), semisimple direction: an element of finite order
`n` coprime to the characteristic of `k` is semisimple.  Indeed `ρ_g*^n = 1`,
so `ρ_g*` is annihilated by `X^n - 1`, which is squarefree over `k` because
`n` is nonzero in `k`; `Module.End.isSemisimple_of_squarefree_aeval_eq_zero`
then yields the semisimplicity of `ρ_g*` (in the strong module-theoretic
sense), hence the finite-dimensional form used in Definition 1.2.1. -/
public theorem finiteOrder_coprimeChar_implies_semisimple {G : Variety k} [AlgebraicGroup G]
    (g : Variety.Point G) (n : ℕ) (_hn : 0 < n) (hchar : ¬ ringChar k ∣ n)
    (hg : g ^ n = 1) :
    IsSemisimpleElement G g := by
  let T : Module.End k (Variety.PolynomialFunction G) := rightTranslationPullback G g
  have hpow : T ^ n = (1 : Module.End k (Variety.PolynomialFunction G)) := by
    rw [rightTranslationPullback_pow_end G g n, hg]
    exact rightTranslationPullback_one G
  have haeval : Polynomial.aeval T ((X : k[X]) ^ n - 1) = 0 := by
    rw [Polynomial.aeval_sub, Polynomial.aeval_X_pow, Polynomial.aeval_one, hpow]
    simp
  have hsep : ((X : k[X]) ^ n - C (1 : k)).Separable := by
    simpa using (separable_X_pow_sub_C' (ringChar k) n (1 : k) hchar one_ne_zero)
  have hsq : Squarefree ((X : k[X]) ^ n - C (1 : k)) := Separable.squarefree hsep
  have hss : T.IsSemisimple :=
    Module.End.isSemisimple_of_squarefree_aeval_eq_zero hsq haeval
  exact hss.isFinitelySemisimple

/-- Proposition 1.2.2(e) for automorphisms: a rational automorphism `ψ` of
finite order `n` coprime to the characteristic of `k` is semisimple, in the
sense that `ψ*` is semisimple on the affine algebra. -/
public theorem finiteOrder_coprimeChar_automorphism_isSemisimple {G : Variety k} [AlgebraicGroup G]
    (ψ : Variety.Morphism G G) (n : ℕ) (_hn : 0 < n) (hchar : ¬ ringChar k ∣ n)
    (hψ : (ψ.toFun)^[n] = (_root_.id : Variety.Point G → Variety.Point G)) :
    IsSemisimpleAutomorphism G ψ := by
  let φ : Module.End k (Variety.PolynomialFunction G) := ψ.pullbackAlgHom.toLinearMap
  have hpow : φ ^ n = (1 : Module.End k (Variety.PolynomialFunction G)) := by
    apply LinearMap.ext
    intro a
    rw [Module.End.pow_apply]
    have hiter : (φ^[n]) a = a := by
      calc
        (φ^[n]) a = (ψ.iterate n).pullbackAlgHom.toLinearMap a := by
          rw [Variety.Morphism.pullbackAlgHom_iterate ψ n]
        _ = a := by
          apply Variety.PolynomialFunction.ext
          intro x
          simp [Variety.Morphism.pullbackAlgHom, Variety.Morphism.pullbackRingHom,
            Variety.PolynomialFunction.pullback, Variety.Morphism.iterate_toFun ψ n, hψ]
          rfl
    exact hiter
  have haeval : Polynomial.aeval φ ((X : k[X]) ^ n - 1) = 0 := by
    rw [Polynomial.aeval_sub, Polynomial.aeval_X_pow, Polynomial.aeval_one, hpow]
    simp
  have hsep : ((X : k[X]) ^ n - C (1 : k)).Separable := by
    simpa using (separable_X_pow_sub_C' (ringChar k) n (1 : k) hchar one_ne_zero)
  have hsq : Squarefree ((X : k[X]) ^ n - C (1 : k)) := Separable.squarefree hsep
  have hss : φ.IsSemisimple :=
    Module.End.isSemisimple_of_squarefree_aeval_eq_zero hsq haeval
  exact hss.isFinitelySemisimple

/-! ## Preservation of semisimplicity and unipotence -/

/-- Proposition 1.2.2(a), finite-order case: a morphism of algebraic groups
preserves the semisimplicity of elements of order coprime to the
characteristic.  The image `φ(g)` has order dividing `n` (a morphism is a
group homomorphism), so clause (e) applies. -/
public theorem morphism_finiteOrder_preserves_semisimple {G H : Variety k}
    [AlgebraicGroup G] [AlgebraicGroup H] (φ : Theory.AlgebraicGroup.Morphism G H)
    (g : Variety.Point G) (n : ℕ) (hn : 0 < n) (hchar : ¬ ringChar k ∣ n)
    (hg : g ^ n = 1) :
    IsSemisimpleElement H (φ.onPoints g) := by
  have hφpow : (φ.onPoints g) ^ n = 1 := by
    rw [← φ.onPoints.map_pow, hg, φ.onPoints.map_one]
  exact finiteOrder_coprimeChar_implies_semisimple (φ.onPoints g) n hn hchar hφpow

/-- Proposition 1.2.2(a), finite-order case: a morphism of algebraic groups
preserves the unipotence of elements of `p`-power order in characteristic
`p`. -/
public theorem morphism_pPowerOrder_preserves_unipotent {G H : Variety k}
    [AlgebraicGroup G] [AlgebraicGroup H] (φ : Theory.AlgebraicGroup.Morphism G H)
    (g : Variety.Point G) (p n : ℕ) [CharP k p] [Fact p.Prime]
    (hg : g ^ p ^ n = 1) :
    IsUnipotentElement H (φ.onPoints g) := by
  have hφpow : (φ.onPoints g) ^ p ^ n = 1 := by
    rw [← φ.onPoints.map_pow, hg, φ.onPoints.map_one]
  exact pPowerOrder_implies_unipotent (φ.onPoints g) p n hφpow

/-! ## Closed subgroups -/

end Theory.AlgebraicGroup
