module

public import CFSG.Quasithin.ChapterB.Section01.FittingStructure.MovedFactors.Induction
public import CFSG.Quasithin.ChapterB.Section01.FittingStructure.MovedFactors.Terminal
public import CFSG.Quasithin.ChapterB.Section01.FittingStructure.MovedFactors.ReducedStructure
public import CFSG.Quasithin.ChapterB.Section01.FittingStructure.MovedFactors.DecompositionControl

/-!
# Moved factors and the Fitting subgroup

This module owns the quotient induction in Aschbacher–Smith B.1.10,
printed p.72 (PDF p.83), conditional on the universal earlier B.1.9
`FittingStructure.SourceTheorem`. The fixed-space calculation is proved
without assuming any reduced-counterexample properties. The minimal-offender
case below uses B.1.9(5), including the separate case [F(G),J*] = 1.

Strong induction on group order first forces G = F(G)KA. The reduced
generalized-Fitting calculation makes every minimal offender faithful on
F(G), supplying all local hypotheses of B.1.9. Its decomposition makes K
centralize [F(G),J*], so noncentrality persists on E = C_F(G)(J*). The
second quotient reduction forces G = EKA, and a minimal offender inside A
then gives the terminal contradiction. The initial centralizing case also
covers F(G) = 1 without invoking B.1.9.

`moved_factor_le_of_source` proves the exact B.1.10 implication for an
arbitrary best offender. Its only additional premise is the universal
earlier B.1.9 `SourceTheorem`, whose construction remains with the parent
Fitting-structure assembly.
-/

public section
namespace CFSG.Quasithin.ChapterB.FittingStructure.MovedFactors
open Subgroup Theory.GroupTheory Representation.BinaryOffender
universe u v
variable {G : Type u} {V : Type v} [Group G] [Finite G]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

/-- B.1.9 discharges B.1.10 when the given offender is already minimal.
This does not impose a nonzero Fitting commutator hypothesis. -/
theorem minimal_case (source : SourceTheorem.{u,v}) (hfaith : Function.Injective ρ)
    (hcore : pCore 2 G = ⊥) {K A : Subgroup G}
    (hA : IsMinimalBestOffender ρ A) (hKA : K = ⁅K,A⁆) :
    K ≤ offenderSubgroup ρ ⊓ centralizer (fittingSubgroup G : Set G) := by
  have hh : K ≤ minimalGenerated ρ ⊓ centralizer (fittingSubgroup G : Set G) := by
    by_cases hF : fittingMoved ρ = ⊥
    · exact minimal_centralization_of_fittingMoved_eq_bot ρ hF hA hKA
    · obtain ⟨d⟩ := source G V ρ hfaith hcore hF
      exact d.moved_subgroup_centralizes A hA K hKA
  exact le_inf ((le_trans hh inf_le_left).trans (minimalGenerated_le ρ))
    (le_trans hh inf_le_right)

omit [FiniteDimensional (ZMod 2) V] in
/-- Faithfulness of minimal offenders on F(G) supplies the nonzero-commutator
hypothesis needed to invoke B.1.9. Existence is obtained from the given best
offender, not imposed as an additional assumption. -/
theorem fittingMoved_ne_bot_of_minimal_faithful {A : Subgroup G}
    (hA : IsBestOffender ρ A)
    (hfaithful : ∀ B, IsMinimalBestOffender ρ B →
      B ⊓ centralizer (fittingSubgroup G : Set G) = ⊥) :
    fittingMoved ρ ≠ ⊥ := by
  obtain ⟨B, hB, _⟩ := hA.exists_minimal ρ
  apply (fittingMoved_ne_bot_iff ρ).mpr
  refine ⟨B, hB, ?_⟩
  intro hz
  have hBC : B ≤ centralizer (fittingSubgroup G : Set G) :=
    le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hz)
  have hb := hfaithful B hB
  rw [inf_of_le_left hBC] at hb
  exact hB.1.1.1 hb

/-- The earlier universal source implication now has all its local premises. -/
theorem conclusion_of_minimal_faithful (source : SourceTheorem.{u,v})
    (hfaith : Function.Injective ρ) (hcore : pCore 2 G = ⊥) {A : Subgroup G}
    (hA : IsBestOffender ρ A)
    (hfaithful : ∀ B, IsMinimalBestOffender ρ B →
      B ⊓ centralizer (fittingSubgroup G : Set G) = ⊥) :
    Nonempty (Conclusion ρ) :=
  source G V ρ hfaith hcore (fittingMoved_ne_bot_of_minimal_faithful ρ hA hfaithful)

private theorem centralizes_fitting_step (source : SourceTheorem.{u,v})
    (hsmall : SmallerCases.{u,v} (Nat.card G))
    (hfaith : Function.Injective ρ) (hcore : pCore 2 G = ⊥) (K A : Subgroup G)
    (hK : IsQuasisimple K ∨ Nat.card K = 3)
    (hA : IsBestOffender ρ A) (hKA : K = ⁅K, A⁆) :
    K ≤ centralizer (fittingSubgroup G : Set G) := by
  by_cases hz : ⁅fittingSubgroup G, K⁆ = ⊥
  · exact le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hz)
  · obtain ⟨hgen, _⟩ := fitting_reduction ρ hsmall hfaith hcore K A hK hA hKA hz
    obtain ⟨d⟩ := conclusion_of_minimal_faithful ρ source hfaith hcore hA
      (minimalBestOffender_inf_fitting_centralizer_eq_bot ρ hcore K A hK hA hKA hgen hz)
    have hE := (bestOffender_decomposition_control ρ d.toDecomposition K A hK hA hKA hz).2
    have hEgen := (centralizer_reduction ρ hsmall hfaith hcore K A hK hA hKA hE).1
    exact (contradiction_of_centralizer_generation ρ d hcore K A hK hA hKA hz hEgen).elim

/-- The centralization assertion of B.1.10, conditional only on the universal
earlier B.1.9 implication. Strong induction discharges both smaller-group
premises; no decomposition or reduced-counterexample properties are assumed. -/
theorem centralizes_fitting_of_source (source : SourceTheorem.{u,v})
    (hfaith : Function.Injective ρ) (hcore : pCore 2 G = ⊥) (K A : Subgroup G)
    (hK : IsQuasisimple K ∨ Nat.card K = 3)
    (hA : IsBestOffender ρ A) (hKA : K = ⁅K, A⁆) :
    K ≤ centralizer (fittingSubgroup G : Set G) := by
  have hall : ∀ n, SmallerCases.{u,v} n := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro D _ _ W _ _ _ σ hlt hfaith hcore K A hK hA hKA
      exact centralizes_fitting_step σ source (ih (Nat.card D) hlt)
        hfaith hcore K A hK hA hKA
  exact hall (Nat.card G + 1) G V ρ (Nat.lt_succ_self _) hfaith hcore K A hK hA hKA

/-- Exact B.1.10 conclusion for a moved quasisimple or order-three subgroup.
The parent assembly must supply the universal B.1.9 `SourceTheorem`; all
other hypotheses are precisely those of B.1.10. -/
theorem moved_factor_le_of_source (source : SourceTheorem.{u,v})
    (hfaith : Function.Injective ρ) (hcore : pCore 2 G = ⊥) (K A : Subgroup G)
    (hK : IsQuasisimple K ∨ Nat.card K = 3)
    (hA : IsBestOffender ρ A) (hKA : K = ⁅K, A⁆) :
    K ≤ offenderSubgroup ρ ⊓ centralizer (fittingSubgroup G : Set G) :=
  le_inf (moved_by_best_le ρ hA hKA)
    (centralizes_fitting_of_source ρ source hfaith hcore K A hK hA hKA)

end CFSG.Quasithin.ChapterB.FittingStructure.MovedFactors
