module

public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Sporadic.Mathieu.Large.Source

/-!
# The independent calculations in the large Mathieu degree sieve

GM02 Proposition 5.1 first uses bounded involution-conjugate generation to
bound the binary degree. The low-degree spectra then leave eleven for M23,
and eleven or forty-four for M24. In the latter case every involution moves
at least eighteen dimensions, contradicting the two-rank bound six.

These are unproved input contracts, not a representation classification.
The spectrum and displacement contracts retain arbitrary quasisimple covers
and do not assume the cubic-ratio bound or the desired degree conclusion.

Source: Guralnick--Malle, Classification of 2F-modules I, equations (2.5)--(2.6),
Proposition 5.1, Theorem 6.6 and Table 6.7; author manuscript pp.4,16--17,21.
-/

@[expose] public section
namespace CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Sporadic.LargeMathieu.GM02
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Sporadic.Mathieu
universe u v

/-- An intrinsic finite conjugate-generation calculation in the simple model. -/
def InvolutionGeneration (S : Type*) [Group S] (n : ℕ) : Prop :=
  ∀ t : S, t ≠ 1 → t ^ 2 = 1 →
    ∃ c : Fin n → S, closure (Set.range fun i => c i * t * (c i)⁻¹) = ⊤

/-- The low-degree binary spectrum for covers of M23, without an offender premise. -/
def M23SmallSpectrum : Prop :=
  ∀ {L : Type u} [Group L] [Finite L] [IsQuasisimple L]
    {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V] (ρ : Representation (ZMod 2) L V),
    Function.Injective ρ → ρ.IsIrreducible →
    Nonempty (L ⧸ center L ≃* M23) →
    Module.finrank (ZMod 2) V ≤ 24 → Module.finrank (ZMod 2) V = 11

/-- The two low-degree binary possibilities for covers of M24. -/
def M24SmallSpectrum : Prop :=
  ∀ {L : Type u} [Group L] [Finite L] [IsQuasisimple L]
    {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V] (ρ : Representation (ZMod 2) L V),
    Function.Injective ρ → ρ.IsIrreducible →
    Nonempty (L ⧸ center L ≃* M24) → Module.finrank (ZMod 2) V ≤ 48 →
    Module.finrank (ZMod 2) V = 11 ∨ Module.finrank (ZMod 2) V = 44

/-- The involution displacement estimate on every degree-forty-four module. -/
def M24Degree44Displacement : Prop :=
  ∀ {L : Type u} [Group L] [Finite L] [IsQuasisimple L]
    {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V] (ρ : Representation (ZMod 2) L V),
    Function.Injective ρ → ρ.IsIrreducible →
    Nonempty (L ⧸ center L ≃* M24) → Module.finrank (ZMod 2) V = 44 →
    ∀ t : L, t ≠ 1 → t ^ 2 = 1 → 18 ≤ fixedCodim ρ (zpowers t)

end CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Sporadic.LargeMathieu.GM02
