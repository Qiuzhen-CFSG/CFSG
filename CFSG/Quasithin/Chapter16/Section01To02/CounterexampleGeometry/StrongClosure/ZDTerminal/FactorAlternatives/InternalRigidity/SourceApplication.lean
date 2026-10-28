module

public import CFSG.Quasithin.Chapter16.Section01To02.CounterexampleGeometry.StrongClosure.ZDTerminal.FactorAlternatives.InternalRigidity

/-!
# The terminal source alternative for factors in the involution span

Internal rigidity supplies whole-factor nesting with no model premise. Since
the span is normal, placement of the first factor also puts its normal closure
in the span. The reverse inclusion follows from terminal involution fusion.
Thus the strong embedding already proved in the span is strong embedding in
the literal normal closure required by alternative (2) of Lemma 3.4.

This is the FactorAlternatives consumer of internal rigidity. Both placement
hypotheses remain explicit for the independent placement and final-assembly
owners to discharge; this does not assert the unconditional source theorem.

Source: M. Aschbacher, *On finite groups of component type* (1975), Lemma 3.4,
pp.94–96, alternative (2) and the final paragraph on p.96.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter16.CounterexampleGeometry.StrongClosure.Asc75

open Subgroup Theory.GroupTheory

variable {G : Type*} [Group G] [Finite G] {S : Sylow 2 G} {A₁ A₂ : Subgroup G}

/-- Internal rigidity gives the source conclusion, including strong embedding
in the actual normal closure, when both factors lie in the terminal span. -/
theorem terminal_conclusion_of_le_span
    (h : Hypotheses S A₁ A₂) (f : FusionConclusion S A₁ A₂)
    (hp : intersectionGenerated A₁ A₂ ≠ ⊤)
    (hs : BenderSuzuki.ZD.StructureConclusion (terminalInvolutions A₁ A₂)
      (intersectionGenerated A₁ A₂))
    (h₁L : A₁ ≤ closure (terminalInvolutions A₁ A₂))
    (h₂L : A₂ ≤ closure (terminalInvolutions A₁ A₂)) :
    Conclusion A₁ A₂ := by
  refine Or.inr (Or.inl ⟨terminal_factors_nested_of_le_span h f hp hs h₁L h₂L, ?_⟩)
  let L := closure (terminalInvolutions A₁ A₂)
  let : L.Normal := (terminalInvolutions_productDisconnected h f hp).closure_normal
  have hNL : normalClosure (A₁ : Set G) = L :=
    le_antisymm (normalClosure_le_normal h₁L)
      (terminal_span_le_normalClosure_left h f hp hs)
  exact Eq.mpr
    (congrArg (fun N : Subgroup G =>
      BenderSuzuki.IsStronglyEmbedded ((intersectionGenerated A₁ A₂).subgroupOf N)) hNL)
    (terminal_stronglyEmbedded_in_span h f hp hs)

end CFSG.Quasithin.Chapter16.CounterexampleGeometry.StrongClosure.Asc75

end
