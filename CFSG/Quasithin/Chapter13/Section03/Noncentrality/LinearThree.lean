module

public import CFSG.Quasithin.Chapter13.Section03.Noncentrality.Residual
public import CFSG.Quasithin.Chapter12.Section08.Setup.Escape

/-!
# The actual L₃(2) application in reduction (b) of 13.3.14

The input is the original natural module and its invariant flag from
Hypothesis 12.8.1(1), which 13.3.2 supplies in this branch. The universal
12.2.2, 1.2.7 and 12.2.13 implications remain explicit. They supply
normalization, uniqueness and escape; no normalizer control of Y or
vanishing residual is an input. All flags and cores are the original ones.

Since V₃=V, the residual theorem applies to U=⟨V₃^G₁⟩ and proves Y=1.
This source branch is a completed part of (b), not the full noncentrality
lemma: reductions (c)–(g) and the diagonal A₅ contradiction remain needed.
Source: Aschbacher–Smith, combined manuscript (1 March 2004), p.891.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter13.Section03.Noncentrality
open Subgroup
open Chapter12.Section02 Chapter12.Section08
universe u
variable {G : Type u} [Group G] [Finite G]
  {K : GroupClass.{u}} {T : Sylow 2 G} {L V : Subgroup G}

/-- Reduction (b) in the literal natural L₃(2) flag. In this branch it holds
without the contrary centrality assumption needed in the rest of 13.3.14. -/
theorem linearThree_centralizingResidual_eq_bot
    (h : HigherRankHypothesis K T L V 3) (F : InvariantFlag T V 3)
    (earlier : EarlierSetupResults K) :
    centralizingResidual (conjugateSpanBy (F.Vi 3) F.H) = ⊥ := by
  rw [F.last]
  have hpoint : F.Vi 1 ≠ ⊥ := by
    intro he
    have hc := F.card 1 (by decide)
    simp [he] at hc
  have hpointp : IsPGroup 2 (F.Vi 1) :=
    T.isPGroup'.to_le ((F.le_seed 1).trans h.chosen.le_sylow)
  have hH : F.H ∈ Chapter1.He G :=
    Chapter1.twoLocal_mem_He_of_sylow_le T (h.source.simpleQTKE.toIsQTKE.evenCharacteristic T)
      ⟨F.Vi 1, hpoint, hpointp, rfl⟩ (F.invariant 1)
  have hQT : L.pCoreIn 2 ≤ (T : Subgroup G) := by
    have hn : L ⊔ (T : Subgroup G) ≤ normalizer (L : Set G) :=
      sup_le L.le_normalizer (h.sylow_normalizes earlier.structural)
    apply (pCoreIn_mono_of_normalizes (show L ≤ L ⊔ (T : Subgroup G) from le_sup_left) hn).trans
    simpa only [Sylow.coe_subtype, map_subgroupOf_eq_of_le le_sup_right] using
      pCoreIn_le_sylow (L ⊔ (T : Subgroup G)) (T.subtype le_sup_right)
  apply centralizingResidual_eq_bot_of_natural_kernel L (T : Subgroup G) V (F.Vi 1)
    (F.invariant 1) (F.le_seed 1) hH
    (h.seed_centralizer_le earlier.structural earlier.uniqueness)
    h.chosen.normalizes h.centralizer_L hQT
  · intro N hN hLN
    exact Set.mem_singleton_iff.mp
      ((h.maximal_unique earlier.structural earlier.uniqueness).2 ▸
        show N ∈ {N : Subgroup G | IsMaximalTwoLocal N ∧ L ⊔ (T : Subgroup G) ≤ N}
          from ⟨hN, hLN⟩)
  · exact h.flag_escape F earlier.alternatives

end CFSG.Quasithin.Chapter13.Section03.Noncentrality
