module
public import CFSG.Quasithin.Chapter14.Section03.Prelim.FaithfulSource
public import CFSG.Quasithin.Chapter12.Section02.SourceHypotheses
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.LocalSetup.Configuration.Flags.Transport
/-!
# Original data for the A₅ branch before abelian closure

The record keeps Hypothesis 13.3.1, the chosen Irr⁺ module, its genuine
A₅ action and the source Sylow flag. The third flag subgroup is specified
by its containment, order and Sylow invariance. No conjugate-span conclusion,
component classification or coordinate marking of the third subgroup is an
input. The action already identifies the original two-core quotient with A₅.

The preceding 12.2.2/13.3.2 source assembly constructs the marked module.
This interface retains that construction separately from the 13.5.10–12
argument, and can also be used by the nonsingular centralizer branch.

Source: Aschbacher–Smith, Hypothesis 13.3.1, Notation 13.2.1 (p.877),
and the A₅ case of 13.5.10–12 (pp.918–925).
-/
@[expose] public section
open Subgroup
namespace CFSG.Quasithin.Chapter13.Section05.A5Source
open Section06.CentralizerReduction
universe u
variable {G : Type u} [Group G] [Finite G]
/-- The original A₅ source data, before either centralizer-closure conclusion. -/
structure Context (T : Sylow 2 G) (L V V₁ V₂ V₃ : Subgroup G) where
  hypothesis : Chapter14.Section03.FaithfulSource.Hypothesis1331 T L
  chosen : Chapter12.Section02.ChosenModule T L V
  flag : A5Module.FlagSource T L V V₁ V₂
  third_le : V₃ ≤ V
  third_card : Nat.card V₃ = 8
  third_invariant : (T : Subgroup G) ≤ normalizer (V₃ : Set G)
namespace Context
variable {T : Sylow 2 G} {L V V₁ V₂ V₃ : Subgroup G}
  (d : Context T L V V₁ V₂ V₃)
include d
/-- The two-core quotient is identified by the original action, not a model tag. -/
noncomputable def quotient : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5) :=
  (QuotientGroup.quotientMulEquivOfEq d.flag.action_kernel.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective d.flag.module.action d.flag.module.onto)
@[simp] theorem quotient_mk (l : L) :
    d.quotient (QuotientGroup.mk' (pCore 2 L) l) = d.flag.module.action l := rfl
/-- Original 13.3.1(4), specialized using that same quotient. -/
theorem uniform_A5 : ∀ K ∈ MainForward.faithfulLocalComponents T,
    Nonempty ((K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5)) :=
  d.hypothesis.five_minimal ⟨d.quotient⟩
/-- The chosen module supplies its genuine elementary abelian structure. -/
theorem elementary : IsElementaryAbelian 2 V := d.chosen.elementary
end Context
end CFSG.Quasithin.Chapter13.Section05.A5Source
