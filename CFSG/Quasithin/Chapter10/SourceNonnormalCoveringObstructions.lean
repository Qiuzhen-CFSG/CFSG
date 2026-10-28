module
public import CFSG.Quasithin.Chapter10.SourceNonnormalCoveringCounterexample
public import CFSG.Quasithin.ChapterC.Section02.SourceConsequences.NormalityReduction

/-!
# Source placement obstructions in the original covering counterexample

Failure of uniqueness for an original nonnormal covering subgroup produces
the genuine strict C.2.8 configuration. The proved normality reductions show
that its literal component cannot be an ambient C-component of H, and that
its local conjugate span cannot have a quasisimple two-core quotient.
These are exactly the two placement conclusions still required from the
contained and escaping source branches of C.4.8; neither is assumed here.

Source: Aschbacher–Smith, C.2.13 and C.4.8, printed pp.148,153,
applied in 4.2.12–13, printed pp.610–611 (1 March 2004 manuscript).
-/

public section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 Chapter4 Chapter4.Section02.Unitary
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

/-- The actual contrary source configuration fails both sufficient
placement conditions from the C.4.8 normality reduction. -/
theorem source_covering_counterexample_obstructions
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {I : Subgroup G} (hIM : I ≤ D.maximalLocal)
    (hcover : (localOrbit T L : Set G) ⊆
      (I : Set G) * ((localOrbit T L).pCoreIn 2 : Set G))
    (hcore : I.pCoreIn 2 ≠ ⊥)
    (horbit : componentOrbit L I = localOrbit T L)
    (hnot : ¬ UniqueMaximalOvergroup I D.maximalLocal) :
    ∃ (J H : Subgroup G)
      (S : Sylow 2 (sectionCentralizerIn D.maximalLocal (localOrbit T L))),
      let LH := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
      let M0 := conjugateSpanBy LH (H ⊓ D.maximalLocal)
      PushLE (localOrbit T L) I J ∧ IsMaximalTwoLocal H ∧ J ≤ H ∧
      H ⊓ D.maximalLocal < H ∧
      ChapterC.HypothesisC28 KnownSimple.IsKnownSimple H (H ⊓ D.maximalLocal)
        LH (J.pCoreIn 2)
        (fullModule (localOrbit T L)
          ((S : Subgroup (sectionCentralizerIn D.maximalLocal (localOrbit T L))).map
            (sectionCentralizerIn D.maximalLocal (localOrbit T L)).subtype)) ∧
      ¬ H ⊓ D.maximalLocal ≤ normalizer (LH : Set G) ∧
      ¬ (LH.subgroupOf H).IsCComponent ∧ ¬ IsQuasisimple (M0 ⧸ pCore 2 M0) := by
  obtain ⟨J,H,S,hIJ,hH,hJH,hlt,hC28,hnorm⟩ :=
    source_covering_counterexample_C28 D hn hIM hcover hcore horbit hnot
  exact ⟨J,H,S,hIJ,hH,hJH,hlt,hC28,hnorm,hC28.nonnormal_obstructions hlt hnorm⟩
end CFSG.Quasithin.Chapter10
