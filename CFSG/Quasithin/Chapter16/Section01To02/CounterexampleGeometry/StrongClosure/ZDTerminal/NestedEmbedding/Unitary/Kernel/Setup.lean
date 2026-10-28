module

public import CFSG.Quasithin.Chapter16.Section01To02.CounterexampleGeometry.StrongClosure.ZDTerminal.FactorAlternatives.SpanPlacement.QuotientAction

/-!
# The Sylow normalizer lift for the terminal kernel argument

This is a specification of the remaining lifting input, not an asserted
theorem. A normalizing element in the involution span must centralize the
Sylow part of the ambient action kernel and have no nonidentity fixed points
on the image of the span's Sylow subgroup. Strong closure then makes its
commutators fill the larger factor, placing that factor in the span.

The unitary model supplies a torus element with the stated fixed-point
property. Lifting through the odd core is a separate finite-group argument;
oddness of the full ambient kernel is neither supplied nor required.

Source: Aschbacher (1975), Lemma 3.4, printed pp.94–96, terminal argument;
Huppert II.10.12 for the unitary root and torus action.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter16.CounterexampleGeometry.StrongClosure.Asc75

open Subgroup Theory.GroupTheory BenderSuzuki.PFchapter1section1

/-- The actual normalizer lift needed by the kernel proof. All subgroup
containments and the centralizer are in the original ambient group. -/
def TerminalSylowNormalizerLift
    {G : Type*} [Group G] (S : Sylow 2 G) {A₁ A₂ : Subgroup G}
    (hL : (closure (terminalInvolutions A₁ A₂)).Normal) : Prop :=
  ∃ T : Sylow 2 (closure (terminalInvolutions A₁ A₂)),
    (T : Subgroup (closure (terminalInvolutions A₁ A₂))) =
      (S : Subgroup G).subgroupOf (closure (terminalInvolutions A₁ A₂)) ∧
    ∃ g ∈ closure (terminalInvolutions A₁ A₂),
      g ∈ normalizer ((T : Subgroup (closure (terminalInvolutions A₁ A₂))).map
        (closure (terminalInvolutions A₁ A₂)).subtype : Subgroup G) ∧
      g ∈ centralizer ((S : Subgroup G) ⊓ (terminalQuotientAction hL).ker : Set G) ∧
      ∀ t ∈ (T : Subgroup (closure (terminalInvolutions A₁ A₂))).map
        (closure (terminalInvolutions A₁ A₂)).subtype,
        Commute (terminalQuotientAction hL g) (terminalQuotientAction hL t) →
          terminalQuotientAction hL t = 1

end CFSG.Quasithin.Chapter16.CounterexampleGeometry.StrongClosure.Asc75
end
