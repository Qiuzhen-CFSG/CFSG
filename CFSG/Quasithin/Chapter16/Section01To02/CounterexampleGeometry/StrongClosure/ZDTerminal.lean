module

public import CFSG.Quasithin.Chapter16.Section01To02.CounterexampleGeometry.StrongClosure.SourceStatements
public import CFSG.Quasithin.Chapter16.Section01To02.CounterexampleGeometry.StrongClosure.ZDTerminal.Span
public import CFSG.Quasithin.Chapter16.Section01To02.CounterexampleGeometry.StrongClosure.ZDTerminal.FactorAlternatives
public import CFSG.Quasithin.Chapter16.Section01To02.CounterexampleGeometry.StrongClosure.ZDTerminal.NestedEmbedding

/-!
# Terminal reduction of Asc75 Lemma 3.4 to exact ZD

The invariant involution set and all product-disconnection clauses are proved
in `ZDTerminal.Involutions`. `ZDTerminal.Span` removes the central factor,
proves strong embedding inside the perfect involution span, and places that
span inside the normal closure of the first factor. The factor alternatives
and the nested normal-closure embedding now give the full source conclusion.
If the intersection-generated subgroup is proper, its product-disconnected
involution set contains an elementary four, so exact ZD supplies its structural
alternative. The concrete Bender-model deductions then finish the argument.

Only the exact universal Theorem ZD and the preceding fusion conclusion remain
explicit inputs. The parent Lemma 3.4 induction supplies that fusion conclusion.

Source: Aschbacher (1975), Lemma 3.4, final paragraph on printed p.96.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter16.CounterexampleGeometry.StrongClosure.Asc75

universe u

/-- The terminal appeal to exact ZD in Asc75 Lemma 3.4. In the nested case,
strong embedding is in the normal closure of the original first factor. -/
theorem terminal_conclusion_of_theoremZD (zd : TheoremZD.{u})
    {G : Type u} [Group G] [Finite G] (S : Sylow 2 G) (A₁ A₂ : Subgroup G)
    (h : Hypotheses S A₁ A₂) (f : FusionConclusion S A₁ A₂) :
    Conclusion A₁ A₂ := by
  by_cases hp : intersectionGenerated A₁ A₂ = ⊤
  · exact Or.inl hp
  have hs := terminal_structure_of_theoremZD zd h f hp
  rcases terminal_factor_alternatives h f hp hs with hn | he
  · exact terminal_conclusion_of_nested h f hp hs hn
  · exact Or.inr (Or.inr he)

end CFSG.Quasithin.Chapter16.CounterexampleGeometry.StrongClosure.Asc75

end
