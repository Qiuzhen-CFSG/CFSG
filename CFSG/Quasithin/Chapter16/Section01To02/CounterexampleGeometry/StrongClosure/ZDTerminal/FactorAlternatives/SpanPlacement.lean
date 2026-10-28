module

public import CFSG.Quasithin.Chapter16.Section01To02.CounterexampleGeometry.StrongClosure.SourceStatements
public import CFSG.Quasithin.Chapter16.Section01To02.CounterexampleGeometry.StrongClosure.ZDTerminal.Span
public import CFSG.Quasithin.Chapter16.Section01To02.CounterexampleGeometry.StrongClosure.ZDTerminal.FactorAlternatives.Reduction
public import CFSG.Quasithin.Chapter16.Section01To02.CounterexampleGeometry.StrongClosure.ZDTerminal.FactorAlternatives.SpanPlacement.QuotientAction
public import CFSG.Quasithin.Chapter16.Section01To02.CounterexampleGeometry.StrongClosure.ZDTerminal.FactorAlternatives.SpanPlacement.Linear
public import CFSG.Quasithin.Chapter16.Section01To02.CounterexampleGeometry.StrongClosure.ZDTerminal.FactorAlternatives.SpanPlacement.Suzuki
public import CFSG.Quasithin.Chapter16.Section01To02.CounterexampleGeometry.StrongClosure.ZDTerminal.FactorAlternatives.SpanPlacement.Unitary

/-!
# Terminal factor placement in the involution span

The four-group in the distinguished involution set removes ZD's central
factor, so the actual odd-core quotient of the span is a simple Bender
group. Its three concrete model alternatives supply whole-factor placement
from the corresponding linear, Suzuki and unitary theorems. The unitary
case retains both the matrix-field and Hermitian fixed-field cardinalities.

This discharges placement for incomparable factors in the terminal argument.
The family proofs use the genuine quotient conjugation action and its
restricted kernel; they do not assume that the ambient kernel is odd.

Source: Aschbacher (1975), Lemma 3.4, pp.94–96, final paragraph on p.96;
GLS, Volume 4, Chapter 2, Theorem ZD(a)–(e).
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter16.CounterexampleGeometry.StrongClosure.Asc75

open Subgroup

variable {G : Type*} [Group G] [Finite G] {S : Sylow 2 G} {A₁ A₂ : Subgroup G}

/-- Every element of either incomparable terminal factor lies in the
involution span. All three actual Bender quotient models are discharged. -/
theorem terminal_factors_le_span
    (h : Hypotheses S A₁ A₂) (f : FusionConclusion S A₁ A₂)
    (hp : intersectionGenerated A₁ A₂ ≠ ⊤)
    (hs : BenderSuzuki.ZD.StructureConclusion (terminalInvolutions A₁ A₂)
      (intersectionGenerated A₁ A₂))
    (h12 : ¬ A₁ ≤ A₂) (h21 : ¬ A₂ ≤ A₁) :
    A₁ ≤ closure (terminalInvolutions A₁ A₂) ∧
      A₂ ≤ closure (terminalInvolutions A₁ A₂) := by
  rcases (terminal_structure_perfect_bender h.left_rank hs).2 with
    ⟨⟨n, hn, ⟨e⟩⟩⟩ | ⟨⟨m, hm, ⟨e⟩⟩⟩ |
      ⟨⟨n, hn, E, hEfield, hEfinite, J, hJ, hcard, hfixed, ⟨e⟩⟩⟩
  · exact terminal_factors_le_span_linear h f hp hs h12 h21 n hn e
  · exact terminal_factors_le_span_suzuki h f hp hs h12 h21 m hm e
  · exact terminal_factors_le_span_unitary h f hp hs h12 h21 n hn
      J hJ hcard hfixed e

end CFSG.Quasithin.Chapter16.CounterexampleGeometry.StrongClosure.Asc75

end
