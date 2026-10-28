module

public import CFSG.Quasithin.Chapter16.Section01To02.CounterexampleGeometry.StrongClosure.SourceStatements
public import CFSG.Quasithin.Chapter16.Section01To02.CounterexampleGeometry.StrongClosure.ZDTerminal.Span
public import CFSG.Quasithin.Chapter16.Section01To02.CounterexampleGeometry.StrongClosure.ZDTerminal.FactorAlternatives.Reduction
public import CFSG.Quasithin.Chapter16.Section01To02.CounterexampleGeometry.StrongClosure.ZDTerminal.FactorAlternatives.SpanPlacement
public import CFSG.Quasithin.Chapter16.Section01To02.CounterexampleGeometry.StrongClosure.ZDTerminal.FactorAlternatives.InternalRigidity

/-!
# Factor alternatives in the terminal step of Asc75 Lemma 3.4

The proved reductions identify every involution of the terminal span with
the distinguished set, nest the factor involutions, and construct an
actual elementary four in the factor intersection. Hence the exact source
exception is excluded under the terminal fusion assumptions. The fixed
Sylow subgroup lies in the intersection-generated subgroup, and each factor
meets the centralizer of the terminal span trivially.

For incomparable factors, the concrete Bender quotient models place both
whole factors in the involution span. Internal rigidity then gives nesting,
a contradiction. Thus the terminal fusion and exact ZD structure imply
whole-subgroup nesting, and in particular the requested nesting-or-exception
alternative. Both placement and model rigidity are discharged. Strong embedding
in the larger normal closure remains with the terminal assembly owner.

Source: Aschbacher (1975), Lemma 3.4, pp.94–96, final paragraph on p.96;
GLS, Volume 4, Chapter 2, Theorem ZD.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter16.CounterexampleGeometry.StrongClosure.Asc75

variable {G : Type*} [Group G] [Finite G] {S : Sylow 2 G} {A₁ A₂ : Subgroup G}

/-- The terminal fusion and ZD structure force containment of one whole factor
in the other, with all span-placement and concrete-model premises discharged. -/
theorem terminal_factors_nested
    (h : Hypotheses S A₁ A₂) (f : FusionConclusion S A₁ A₂)
    (hp : intersectionGenerated A₁ A₂ ≠ ⊤)
    (hs : BenderSuzuki.ZD.StructureConclusion (terminalInvolutions A₁ A₂)
      (intersectionGenerated A₁ A₂)) :
    A₁ ≤ A₂ ∨ A₂ ≤ A₁ := by
  by_cases h12 : A₁ ≤ A₂
  · exact Or.inl h12
  by_cases h21 : A₂ ≤ A₁
  · exact Or.inr h21
  obtain ⟨h₁L, h₂L⟩ := terminal_factors_le_span h f hp hs h12 h21
  exact terminal_factors_nested_of_le_span h f hp hs h₁L h₂L

/-- The factor alternatives required in the terminal step of Asc75 Lemma 3.4.
`Exceptional` retains the conjugator fused into A₁, the actual dihedral or
semidihedral model equivalence, and the intersection of cardinality two. -/
theorem terminal_factor_alternatives
    (h : Hypotheses S A₁ A₂) (f : FusionConclusion S A₁ A₂)
    (hp : intersectionGenerated A₁ A₂ ≠ ⊤)
    (hs : BenderSuzuki.ZD.StructureConclusion (terminalInvolutions A₁ A₂)
      (intersectionGenerated A₁ A₂)) :
    (A₁ ≤ A₂ ∨ A₂ ≤ A₁) ∨ Exceptional A₁ A₂ :=
  Or.inl (terminal_factors_nested h f hp hs)

end CFSG.Quasithin.Chapter16.CounterexampleGeometry.StrongClosure.Asc75

end
