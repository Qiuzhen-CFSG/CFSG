module

public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.SignalizerElimination.Setup

/-!
# Intermediate conclusions in the E.6.20 argument

These predicates specify two mathematical obligations, rather than asserting
them. Quotient transport and central-kernel splitting must establish oddness
and exact centralizers for the actual local closure. Inversion, the quasithin
rank bound, and coprime generation must then identify each local prime closure
with a centralizer prime core at corank at most two. The globalization proof
uses the latter identity; final E.6.20 assembly must discharge both obligations.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), E.6.20,
printed pp.252–253 (PDF pp.263–264), including identity (*).
-/

@[expose] public section

namespace CFSG.Quasithin.ChapterE.Section06.Hyperplanes.SignalizerElimination

variable {G : Type*} [Group G] [Finite G]

/-- Oddness and exact centralizers of the lifted, actually generated closure. -/
def CompletedLocalOddClosure (V : Subgroup G) : Prop :=
  ∀ U₀ : Subgroup G, U₀ ≤ V → subgroupCorank V U₀ = 3 →
    Odd (Nat.card (localOddClosure V U₀)) ∧
      ∀ A : Subgroup G, U₀ < A → A ≤ V →
        localOddClosure V U₀ ⊓ Subgroup.centralizer (A : Set G) = oddCentralizer A

/-- The local identity (*) together with its corank-two localization. -/
def LocalPrimeLocalization (p : ℕ) (V : Subgroup G) : Prop :=
  ∀ U₀ : Subgroup G, U₀ ≤ V → subgroupCorank V U₀ = 3 →
    ∃ U₄ : Subgroup G, U₀ ≤ U₄ ∧ U₄ ≤ V ∧ subgroupCorank V U₄ ≤ 2 ∧
      localPrimeClosure p V U₀ = primeCentralizer p U₄

end CFSG.Quasithin.ChapterE.Section06.Hyperplanes.SignalizerElimination
