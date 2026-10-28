module

public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Exceptional.HigherRecognition.EvenTwisted.Absolute

/-!
# Involution estimates for the triality F-module argument

The two missing representation inputs are separated at the actual component.
An inner involution is evaluated on an arbitrary irreducible module of its
quasisimple cover; absolute irreducibility is not assumed. An involution
outside the component is evaluated on the original ambient module. Both
estimates retain the coefficient-field degree and the displacement operator.

For the F-module exclusion the proved automorphism two-rank is `5*n`, so
strictly larger displacement suffices. On the natural eight-dimensional
module over the field of order `q^3`, the source's displacement at least two
gives binary displacement at least `6*n`. The adjoint and remaining module
cases, central covers, and proper extensions still require proof.

Source: Guralnick--Malle, *Classification of 2F-modules, II*, Theorem 8.1
and Lemma 8.6, internal pp.52--57; see `EvenTwisted/Source.md`.
These definitions state prerequisites and do not assert the source theorem.
-/

@[expose] public section

open Representation

namespace CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Exceptional.Higher.EvenTwisted.Triality

universe u v

/-- The component estimate is required without absolute irreducibility. -/
def ComponentInvolutionBound (R : Type u) [Group R] (n : ℕ) : Prop :=
  ∀ (E W : Type v) [Field E] [Finite E] [Algebra (ZMod 2) E] [CharP E 2]
    [AddCommGroup W] [Module E W] [FiniteDimensional E W]
    (τ : Representation E R W),
    IsIrreducible τ → Function.Injective τ →
    ∀ t : R, t ≠ 1 → t ^ 2 = 1 →
      5 * n < Module.finrank (ZMod 2) E *
        Module.finrank E (LinearMap.range (τ t - LinearMap.id))

/-- The proper-extension estimate retains the literal ambient operator and
only irreducibility, not absolute irreducibility, on the component. -/
def OuterInvolutionBound (H : Type u) [Group H] (N : Subgroup H) (n : ℕ) : Prop :=
  ∀ (E W : Type v) [Field E] [Finite E] [Algebra (ZMod 2) E] [CharP E 2]
    [AddCommGroup W] [Module E W] [FiniteDimensional E W]
    (σ : Representation E H W),
    IsAbsolutelyIrreducible σ → IsIrreducible (σ.comp N.subtype) →
    Function.Injective σ →
    ∀ t : H, t ∉ N → t ^ 2 = 1 →
      5 * n < Module.finrank (ZMod 2) E *
        Module.finrank E (LinearMap.range (σ t - LinearMap.id))

end CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Exceptional.Higher.EvenTwisted.Triality
