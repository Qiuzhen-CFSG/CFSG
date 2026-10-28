module

public import CFSG.Quasithin.Chapter16.Section01To02.CounterexampleGeometry.StrongClosure.SourceStatements
public import CFSG.Quasithin.Chapter16.Section01To02.CounterexampleGeometry.StrongClosure.ZDTerminal.Span
public import CFSG.Quasithin.Chapter16.Section01To02.CounterexampleGeometry.StrongClosure.ZDTerminal.NestedEmbedding.Transfer
public import CFSG.Quasithin.Chapter16.Section01To02.CounterexampleGeometry.StrongClosure.ZDTerminal.NestedEmbedding.Linear
public import CFSG.Quasithin.Chapter16.Section01To02.CounterexampleGeometry.StrongClosure.ZDTerminal.NestedEmbedding.Suzuki
public import CFSG.Quasithin.Chapter16.Section01To02.CounterexampleGeometry.StrongClosure.ZDTerminal.NestedEmbedding.Unitary

/-!
# The nested normal-closure case of Asc75 Lemma 3.4

The odd-core quotient of the involution span is a simple Bender group by
`ZDTerminal.Span`. In each of its three actual model families, the nested
absorption theorem puts every involution of H ∩ normalClosure A₁ into that
span. The transfer theorem then proves strong embedding in normalClosure A₁,
retaining this same ambient group in both nesting orientations. The final
application supplies alternative (2) of the original source conclusion.

Source: M. Aschbacher, *On finite groups of component type* (1975),
Lemma 3.4, alternative (2), printed p.94 and final paragraph p.96;
GLS, Volume 4, Chapter 2, Theorem ZD(a)–(e).
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter16.CounterexampleGeometry.StrongClosure.Asc75

open Subgroup Theory.GroupTheory BenderSuzuki.PFchapter1section1
  BenderSuzuki.PFAppendixIII

universe u
variable {G : Type u} [Group G] [Finite G]
  {S : Sylow 2 G} {A₁ A₂ : Subgroup G}

/-- The three actual Bender models exhaust the odd-core quotient of the span.
Their nested absorption theorems all concern the original left normal closure. -/
theorem terminal_nested_involution_absorption
    (h : Hypotheses S A₁ A₂) (f : FusionConclusion S A₁ A₂)
    (hp : intersectionGenerated A₁ A₂ ≠ ⊤)
    (hs : BenderSuzuki.ZD.StructureConclusion (terminalInvolutions A₁ A₂)
      (intersectionGenerated A₁ A₂)) (hn : A₁ ≤ A₂ ∨ A₂ ≤ A₁) :
    ∀ z ∈ normalClosure (A₁ : Set G), z ∈ intersectionGenerated A₁ A₂ →
      IsInvolution z → z ∈ closure (terminalInvolutions A₁ A₂) := by
  rcases (terminal_structure_perfect_bender h.left_rank hs).2 with
    ⟨⟨n, hn₂, ⟨e⟩⟩⟩ | ⟨⟨m, hm, ⟨e⟩⟩⟩ |
      ⟨⟨n, hn₂, E, hEfield, hEfinite, J, hJ, hcard, hfixed, ⟨e⟩⟩⟩
  · exact terminal_nested_involution_absorption_linear h f hp hs hn n hn₂ e
  · exact terminal_nested_involution_absorption_suzuki h f hp hs hn m hm e
  · exact terminal_nested_involution_absorption_unitary h f hp hs hn n hn₂
      J hJ hcard hfixed e

/-- Alternative (2)'s strong embedding, inside the normal closure of A₁ in
either nesting orientation, with no additional model or kernel premise. -/
theorem terminal_nested_stronglyEmbedded_in_normalClosure
    (h : Hypotheses S A₁ A₂) (f : FusionConclusion S A₁ A₂)
    (hp : intersectionGenerated A₁ A₂ ≠ ⊤)
    (hs : BenderSuzuki.ZD.StructureConclusion (terminalInvolutions A₁ A₂)
      (intersectionGenerated A₁ A₂)) (hn : A₁ ≤ A₂ ∨ A₂ ≤ A₁) :
    BenderSuzuki.IsStronglyEmbedded
      ((intersectionGenerated A₁ A₂).subgroupOf (normalClosure (A₁ : Set G))) := by
  exact terminal_stronglyEmbedded_in_normalClosure_of_involution_absorption h f hp hs
    (terminal_nested_involution_absorption h f hp hs hn)

/-- The nested branch supplies the literal source conclusion of Lemma 3.4.
The terminal assembly retains responsibility for obtaining ZD and nesting. -/
theorem terminal_conclusion_of_nested
    (h : Hypotheses S A₁ A₂) (f : FusionConclusion S A₁ A₂)
    (hp : intersectionGenerated A₁ A₂ ≠ ⊤)
    (hs : BenderSuzuki.ZD.StructureConclusion (terminalInvolutions A₁ A₂)
      (intersectionGenerated A₁ A₂)) (hn : A₁ ≤ A₂ ∨ A₂ ≤ A₁) :
    Conclusion A₁ A₂ := by
  exact Or.inr (Or.inl ⟨hn,
    terminal_nested_stronglyEmbedded_in_normalClosure h f hp hs hn⟩)

end CFSG.Quasithin.Chapter16.CounterexampleGeometry.StrongClosure.Asc75
end
