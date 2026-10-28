module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanLocalQuotientKernel
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericExceptionalCartanLocal

/-!
# The original Chapter 12 omega-span loses order in the local quotient

The wholeReduced source input gives the kernel obstruction on the actual
chosen Sylow and original L-span of its omega-center. This applies in
particular to the remaining binary-triality container. A lower bound on
the span itself therefore cannot be transported using an injective
restriction of Y → Y/O₂(Y).

This is a diagnostic for that proposed local proof step. It neither
excludes binary triality nor proves the original Cartan escape theorem.
Source: Aschbacher--Smith 1.1.4(6), 5.1.13 and 12.2.2,
printed pp.501,635--638,795, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source Chapter6.Source.RankOneGeneric
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H Y : Subgroup G}
  (a : ChosenModule T L V)
include a

/-- The literal local quotient kills omega and strictly shrinks its original L-span. -/
theorem rankOne_local_cartan_omega_span_quotient_kernel
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hY : Y ∈ Chapter1.HOver G (H : Set G)) :
    let U := conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) L
    omegaOneCenterAmbient (T : Subgroup G) ≤ Y.pCoreIn 2 ∧
      ¬ Function.Injective ((QuotientGroup.mk' (pCore 2 Y)).comp
        (U.subgroupOf Y).subtype) ∧
      Nat.card ((U.subgroupOf Y).map (QuotientGroup.mk' (pCore 2 Y))) < Nat.card U := by
  have hs := a.rankOne_generic_input_of_many h.toHypothesis1221 hmany hn hpsl
  exact ⟨hs.local_omega_le_twoCore hH hY,
    hs.local_omega_span_quotient_not_injective hH hY,
    hs.local_omega_span_quotient_card_lt hH hY⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
