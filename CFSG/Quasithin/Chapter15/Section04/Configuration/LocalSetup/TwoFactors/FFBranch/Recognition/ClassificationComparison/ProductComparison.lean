module

public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.FFBranch.Recognition.ClassificationComparison.ProductComparison.PrimeRow
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.FFBranch.Recognition.ClassificationComparison.ProductComparison.ClassicalComponents
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.FFBranch.Recognition.ClassificationComparison.ProductComparison.PermutationComponents

/-!
# The product branches of the F.6.18/B.5.6 comparison

For each of the full product, outer A₆–C₃ and hyperplane FF alternatives,
F.6.18(2) gives the actual ambient S₃ × S₃ equivalence, and row (3) is
impossible. Both orientations of the Goldschmidt generators are covered.
Every such FF branch also forces the ambient F* to be nonquasisimple, whereas
the actual classical, permutation, covering and Mathieu models in rows
(4)–(13) have quasisimple F* when O₂(D) = 1. Thus `product_comparison`
completes all three branches with an actual ambient S₃ × S₃ equivalence.

The full FF records remain explicit branch inputs on the actual offender
subgroup. No identification of that subgroup with D, module splitting,
fixed-space exclusion or additional classification premise is used. In
particular the double-natural, four-dimensional indecomposable, hyperplane
and nonsplit alternatives are all covered. The older reduction interface
is preserved for consumers that need its intermediate conclusions.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
B.5.6(3)–(5), pp.105–110; F.6.18, pp.309–310; 15.4.18, p.1163.
-/

@[expose] public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison
namespace ProductComparison

/-- The ten literal F.6.18 rows with quasisimple generalized Fitting subgroup
when O₂ = 1. The full group and local-subgroup data are retained. -/
def ComponentRows {D : Type*} [Group D] (G₁ G₂ : Subgroup D) : Prop :=
  GoldschmidtAlternatives.Case4 G₁ G₂ ∨ GoldschmidtAlternatives.Case5 G₁ G₂ ∨
  GoldschmidtAlternatives.Case6 G₁ G₂ ∨ GoldschmidtAlternatives.Case7 G₁ G₂ ∨
  GoldschmidtAlternatives.Case8 G₁ G₂ ∨ GoldschmidtAlternatives.Case9 G₁ G₂ ∨
  GoldschmidtAlternatives.Case10 G₁ G₂ ∨ GoldschmidtAlternatives.Case11 G₁ G₂ ∨
  GoldschmidtAlternatives.Case12 G₁ G₂ ∨ GoldschmidtAlternatives.Case13 G₁ G₂

universe u v
variable {D : Type u} [Group D] [Finite D]
    {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
    {ρ : Representation (ZMod 2) D V} {G₁ G₂ : Subgroup D} {K : GroupClass.{u}}

private theorem ordered_reduction (h : ClassifiedAction K ρ G₁ G₂)
    (hb : Branch (ρ.comp (offenderSubgroup ρ).subtype))
    (hr : GoldschmidtAlternatives.RemainingOrdered G₁ G₂) :
    Nonempty (D ≃* (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))) ∨ ComponentRows G₁ G₂ := by
  rcases hr with h2 | h3 | hr
  · exact Or.inl (case2_equiv h hb h2)
  · exact (not_case3 h hb h3).elim
  · exact Or.inr hr

private theorem classified_swap (h : ClassifiedAction K ρ G₁ G₂) :
    ClassifiedAction K ρ G₂ G₁ :=
  ⟨h.faithful, h.twoCore, h.threePrimeCore, h.triple.symm, h.goldschmidt.symm,
    h.ffHypothesis, h.ffWitness, h.ffAlternatives, h.quotient_twoGroup, h.sylow_fixedSpace⟩

/-- Source-complete reduction of all three product branches, in both generator
orientations. `product_comparison` discharges the retained component rows. -/
theorem product_comparison_reduction (h : ClassifiedAction K ρ G₁ G₂)
    (hb : Branch (ρ.comp (offenderSubgroup ρ).subtype)) :
    ¬ IsQuasisimple (generalizedFitting D) ∧
      (Nonempty (D ≃* (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))) ∨
        ComponentRows G₁ G₂ ∨ ComponentRows G₂ G₁) := by
  refine ⟨branch_not_quasisimple ρ hb, ?_⟩
  rcases h.goldschmidt with hr | hr
  · rcases ordered_reduction h hb hr with he | hr
    · exact Or.inl he
    · exact Or.inr (Or.inl hr)
  · rcases ordered_reduction (classified_swap h) hb hr with he | hr
    · exact Or.inl he
    · exact Or.inr (Or.inr hr)

/-- Every literal row (4)–(13) has quasisimple F* when O₂(D) = 1.
The concrete model proofs cover both signs, both central covers, and the
field and graph extensions without requiring those extensions to split. -/
theorem componentRows_quasisimple (hcore : pCore 2 D = ⊥)
    (hr : ComponentRows G₁ G₂) : IsQuasisimple (generalizedFitting D) := by
  rcases hr with h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13
  · exact ClassicalComponents.case4_fitting h4
  · exact ClassicalComponents.case5_fitting h5 hcore
  · rcases h6.1 with h | ⟨p, e, _, _, _, hpe, hm⟩
    · exact triple_alternating_six_quasisimple_fitting h hcore
    · exact ClassicalComponents.pslTwo_fitting (by omega) hm
  · rcases h7.1 with h | h
    · exact alternating_seven_quasisimple_fitting h hcore
    · exact triple_alternating_seven_quasisimple_fitting h hcore
  · rcases h8.1 with h | ⟨p, _, hp8, hm⟩
    · exact triple_symmetric_six_quasisimple_fitting h hcore
    · exact ClassicalComponents.fieldExtension_fitting hp8 hm hcore
  · rcases h9.1 with h | h
    · exact symmetric_seven_quasisimple_fitting h hcore
    · exact triple_symmetric_seven_quasisimple_fitting h hcore
  · exact ClassicalComponents.case10_fitting h10
  · exact ClassicalComponents.case11_fitting h11 hcore
  · exact m12_quasisimple_fitting h12.1 hcore
  · exact aut_m12_quasisimple_fitting h13.1 hcore

/-- Exhaustive comparison of B.5.6(3)–(5) with the retained F.6.18 rows,
in either generator orientation and on the literal ambient action group. -/
theorem product_comparison (h : ClassifiedAction K ρ G₁ G₂)
    (hb : Branch (ρ.comp (offenderSubgroup ρ).subtype)) :
    Nonempty (D ≃* (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))) := by
  obtain ⟨hn, he | hr | hr⟩ := product_comparison_reduction h hb
  · exact he
  · exact (hn (componentRows_quasisimple h.twoCore hr)).elim
  · exact (hn (componentRows_quasisimple h.twoCore hr)).elim

/-- B.5.6(3), retaining natural, double-natural and indecomposable factors. -/
theorem sourceTwoFactor_equiv (h : ClassifiedAction K ρ G₁ G₂)
    (hb : Nonempty (FFAlternatives.SourceTwoFactorCase
      (ρ.comp (offenderSubgroup ρ).subtype))) :
    Nonempty (D ≃* (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))) :=
  product_comparison h (Or.inl hb)

/-- B.5.6(4), retaining the actual outer actions and full module record. -/
theorem outerSixThree_equiv (h : ClassifiedAction K ρ G₁ G₂)
    (hb : Nonempty (FFAlternatives.OuterSixThreeCase
      (ρ.comp (offenderSubgroup ρ).subtype))) :
    Nonempty (D ≃* (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))) :=
  product_comparison h (Or.inr (Or.inl hb))

/-- B.5.6(5), retaining the hyperplane and both second-factor module cases. -/
theorem hyperplane_equiv (h : ClassifiedAction K ρ G₁ G₂)
    (hb : Nonempty (FFAlternatives.HyperplaneCase
      (ρ.comp (offenderSubgroup ρ).subtype))) :
    Nonempty (D ≃* (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))) :=
  product_comparison h (Or.inr (Or.inr hb))

end ProductComparison
end CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison
