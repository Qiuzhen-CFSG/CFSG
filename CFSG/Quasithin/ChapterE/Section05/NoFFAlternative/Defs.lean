module

public import CFSG.Quasithin.ChapterE.Section05.Defs
public import Theory.Representation.BinaryOffender.Defs

/-!
# Exact additional input and module exclusion for E.5.4

The E.5.1 input below quantifies over precisely its Sylow group, elementary
subgroup, E-member, positive index and residual-centralizer bound. The no-FF
condition tests faithful finite-dimensional binary representations of the
actual quotients G/X, for normal X between O₂(G) and O∞(G).

These are specifications, not assertions of E.5.1 or E.5.4.
Source: Aschbacher–Smith, combined manuscript (1 March 2004), pp.242 and 244.
-/

@[expose] public section
universe u
namespace CFSG.Quasithin.ChapterE.NoFFAlternative
open ChapterB Subgroup Stellmacher Representation.BinaryOffender

/-- The center-containment clause of E.5.1, with its published hypotheses. -/
def CenterContainmentSchema (G : Type u) [Group G] [Finite G] : Prop :=
  ∀ (P : Sylow 2 G) (A K : Subgroup G) (i j : ℕ), 0 < j →
    A ∈ thompsonFamily (P : Subgroup G) i →
    IsEMemberAt j (P : Subgroup G) A K →
    WeakClosureCentralizerBound (P : Subgroup G) A K →
    higherThompsonCenter (P : Subgroup G) (i + j) ≤
      omegaOneCenterAmbient (higherThompsonCore (P : Subgroup G) K (i + j))

/-- The source excludes only faithful binary FF-modules of these quotients.
The module universe matches G and hence all its literal finite chief sections. -/
def HasNoFFQuotients (G : Type u) [Group G] : Prop :=
  ∀ (X : Subgroup G) (_ : X.Normal), pCore 2 G ≤ X → X ≤ solvableRadical G →
    ∀ (V : Type u) [AddCommGroup V] [Module (ZMod 2) V]
      [FiniteDimensional (ZMod 2) V] (ρ : Representation (ZMod 2) (G ⧸ X) V),
      Function.Injective ρ → ¬ IsFFModule ρ

end CFSG.Quasithin.ChapterE.NoFFAlternative
