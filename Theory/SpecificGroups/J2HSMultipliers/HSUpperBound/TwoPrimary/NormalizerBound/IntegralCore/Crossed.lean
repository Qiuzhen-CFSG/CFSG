module

public import Theory.SpecificGroups.J2HSMultipliers.HSUpperBound.TwoPrimary.NormalizerBound.Prelude

/-!
# Integral conjugation errors for the HS normalizer core

For the literal normalizer N and its core Q, a split central extension
produces right crossed homomorphisms N → Hom(Q,K), trivial on Q. Changing
the section by t changes an error by t(q)/t(nqn⁻¹). `HasCyclicError` asks
for a change leaving the errors in one cyclic subgroup of order at most two.
It is an explicit calculation to be proved, not a source theorem assumption.

The application to an arbitrary cover and its actual displacement subgroup
is proved in the parent `IntegralCore` module. Source: the integral module
step behind Aschbacher–Smith I.1.3(1), p.407, and I.2.2(5), p.412. The
latter's center-order-two hypothesis is not used here.
-/

public section
open Subgroup
namespace Theory.SpecificGroups.J2HSMultipliers.HS.TwoPrimary.NormalizerBound
open Sporadic.LeechRelated.HS BlockNormalizer

/-- Multiplicative right cocycles, trivial on the actual two-core. -/
structure CoreCrossedHom (K : Type*) [CommGroup K] where
  toFun : baseNormalizer → (pCore 2 baseNormalizer →* K)
  mul_rule : ∀ n m q, toFun (n * m) q =
    toFun n (MulAut.conjNormal m q) * toFun m q
  core_rule : ∀ u : pCore 2 baseNormalizer, toFun u = 1

/-- A section change leaving only one central error of order at most two. -/
@[expose] def CoreCrossedHom.HasCyclicError {K : Type*} [CommGroup K] (β : CoreCrossedHom K) : Prop :=
  ∃ (t : pCore 2 baseNormalizer →* K) (z : K), z ^ 2 = 1 ∧
    ∀ (n : baseNormalizer) (q : pCore 2 baseNormalizer),
      β.toFun n q * t q / t (MulAut.conjNormal n q) ∈ zpowers z

end Theory.SpecificGroups.J2HSMultipliers.HS.TwoPrimary.NormalizerBound
