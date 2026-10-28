module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.StarAction.Centerless

/-!
# From containment to the star obstruction in the centerless cases

For each centerless model remaining after 13.6.18–19, the marked source
action proves [K⁺,L_v⁺] ≠ 1. The actual star-to-plus comparison therefore
rules out normalization of L_v* by K*. Relative normality of L_v in M_v
then gives K ⊄ M, exactly as in the final step of 13.6.21.

The explicit inputs are the genuine earlier local marking, Sylow and
invariance data, the R₂ consequence O₂(G⁺)=1, and L_v≤K from 13.6.20.
The covered A₆ branch is still required for the complete conditional
13.6.21 implication. This module does not claim that branch or discharge
any of the earlier inputs from Hypothesis 13.3.1; those source premises
remain with the respective assembly owners.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
printed pp.926–932, especially 13.6.11, 13.6.14 and 13.6.20–21.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.StarAction
open ComponentSelection
variable {G : Type*} [Group G]

section Application
variable [Finite G] {L V : Subgroup G}
    (s : A5Module.Marking L V) (K T : Subgroup G)
    [IsElementaryAbelian 2 (Uv (A5Module.markedZ s) (A5Module.markedV s))]
    (S : Sylow 2 (Gv (A5Module.markedV s)))
    (hS : (S : Subgroup (Gv (A5Module.markedV s))).map
      (Gv (A5Module.markedV s)).subtype = Tv T (A5Module.markedV s))
    (hL : Tv T (A5Module.markedV s) ≤ normalizer (Lv L (A5Module.markedV s) : Set G))
    (hz : Tv T (A5Module.markedV s) ≤ centralizer ({A5Module.markedZ s} : Set G))
    (hK : K ∈ Yz L T (A5Module.markedZ s) (A5Module.markedV s))
    (hn : Tv T (A5Module.markedV s) ≤ normalizer (K : Set G))
    (hLK : Lv L (A5Module.markedV s) ≤ K)
    (hR : pCore 2 (Gplus K L T (A5Module.markedZ s) (A5Module.markedV s) hL hz) = ⊥)
    (hcard : Nat.card (Lv L (A5Module.markedV s) ⧸ pCore 2 (Lv L (A5Module.markedV s))) = 3)
    (hmodel : CenterlessModel (plusImage K L T (A5Module.markedZ s) (A5Module.markedV s) hL hz K))

include S hS hK hn hLK hR hmodel in
/-- Derive noncentrality for the literal reduced centerless actor. Its
quasisimplicity is constructed from Y_z and the earlier two-core output. -/
theorem plus_commutator_ne_bot_of_model :
    ⁅plusImage K L T (A5Module.markedZ s) (A5Module.markedV s) hL hz K,
      plusImage K L T (A5Module.markedZ s) (A5Module.markedV s) hL hz
        (Lv L (A5Module.markedV s))⁆ ≠ ⊥ := by
  let : IsQuasisimple (plusImage K L T (A5Module.markedZ s) (A5Module.markedV s) hL hz K) :=
    plusImage_K_quasisimple K L T _ _ hL hz hK hR
  exact plus_commutator_ne_bot_of_centerless s K T S hS hL hz hK hn hLK hmodel.center_eq_bot

include S hS hL hz hK hn hLK hR hcard hmodel in
/-- The source star-action consequence in every centerless reduced case.
Neither noncentrality nor nonnormalization is an input. -/
theorem star_action_obstruction_of_model :
    ¬ starImage (A5Module.markedZ s) (A5Module.markedV s) K ≤
      normalizer (starImage (A5Module.markedZ s) (A5Module.markedV s)
        (Lv L (A5Module.markedV s)) : Set (Gstar (A5Module.markedZ s) (A5Module.markedV s))) :=
  star_action_obstruction_of_plus_commutator K L T _ _ hL hz hK hR hcard
    (plus_commutator_ne_bot_of_model s K T S hS hL hz hK hn hLK hR hmodel)

include S hS hL hz hK hn hLK hR hcard hmodel in
/-- The actual 13.6.21 consumer, using normality relative to M_v and the
literal star map. The covered A₆ case remains a separate branch. -/
theorem not_le_M_of_model (M : Subgroup G)
    (hLM : Lv L (A5Module.markedV s) ≤ Mv M (A5Module.markedV s))
    (hN : ((Lv L (A5Module.markedV s)).subgroupOf (Mv M (A5Module.markedV s))).Normal) :
    ¬ K ≤ M :=
  Source.not_le_M_of_star_action_obstruction L M K _ _ hLM hN hK.1.1
    (star_action_obstruction_of_model s K T S hS hL hz hK hn hLK hR hcard hmodel)

end Application
end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.StarAction
