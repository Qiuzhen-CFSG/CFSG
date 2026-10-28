module

public import CFSG.Quasithin.Chapter16.Section01To02.CounterexampleGeometry.StrongClosure.SourceStatements

/-!
# The induction assembly for Aschbacher's Lemma 3.4

Strong induction assembles two independent mathematical obligations: local
fusion in a minimal counterexample, and the terminal deduction from that
fusion and the exact Theorem ZD. Neither obligation is asserted here. The
induction ranges over all smaller finite groups, so it supplies the central
quotients used on pp.95–96 of Aschbacher (1975).
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter16.CounterexampleGeometry.StrongClosure.Asc75
universe u

/-- Conditional assembly of the full source statement. The two reduction
premises remain proof obligations of this Lemma 3.4 development. -/
theorem conclusion_of_fusion_and_terminal
    (zd : TheoremZD.{u})
    (fusion : ∀ {G : Type u} [Group G] [Finite G]
      (S : Sylow 2 G) (A₁ A₂ : Subgroup G),
      MinimalCounterexample S A₁ A₂ → FusionConclusion S A₁ A₂)
    (terminal : TheoremZD.{u} →
      ∀ {G : Type u} [Group G] [Finite G]
        (S : Sylow 2 G) (A₁ A₂ : Subgroup G),
        Hypotheses S A₁ A₂ → FusionConclusion S A₁ A₂ → Conclusion A₁ A₂)
    {G : Type u} [Group G] [Finite G]
    (S : Sylow 2 G) (A₁ A₂ : Subgroup G) (h : Hypotheses S A₁ A₂) :
    Conclusion A₁ A₂ := by
  have main : ∀ n : ℕ, ∀ {X : Type u} [Group X] [Finite X],
      Nat.card X = n → ∀ (P : Sylow 2 X) (B₁ B₂ : Subgroup X),
        Hypotheses P B₁ B₂ → Conclusion B₁ B₂ := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro X _ _ hcard P B₁ B₂ hB
      by_contra hfail
      have hm : MinimalCounterexample P B₁ B₂ := by
        refine ⟨hB, hfail, ?_⟩
        intro Y _ _ hY Q C₁ C₂ hC
        exact ih (Nat.card Y) (hcard ▸ hY) rfl Q C₁ C₂ hC
      exact hfail (terminal zd P B₁ B₂ hB (fusion P B₁ B₂ hm))
  exact main (Nat.card G) rfl S A₁ A₂ h

/-- The unique fixed-point assertion includes centralizer containment. -/
theorem UniqueConjugateMembership.centralizer_le
    {G : Type u} [Group G] {H : Subgroup G} {x : G}
    (h : UniqueConjugateMembership H x) :
    Subgroup.centralizer ({x} : Set G) ≤ H := by
  intro g hg
  apply (h.2 g).mp
  have hc := Subgroup.mem_centralizer_singleton_iff.mp hg
  simpa only [mul_assoc, ← hc, inv_mul_cancel_left] using h.1

end CFSG.Quasithin.Chapter16.CounterexampleGeometry.StrongClosure.Asc75
end
