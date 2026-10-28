module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Action.Counting.SectionThree.Counts
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Action.Counting.SectionThree.Indices
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Action.Counting.SectionThree.Local.Sylow

/-!
# Assembly of the distinguished Section 3 facts

Point swapping and the centralizer-index identities follow from product
disconnection. Z-star gives the relative odd-core containment, which supplies
the invariant-Sylow and centralizer-Sylow assertions even when the two-point
stabilizer has even order. These inputs give the remaining cardinal bounds
and invariant-Sylow equivalence, with all local premises discharged.

Source: GLS, Volume 4, Chapter 2, Lemma 3.4 and Propositions 3.5--3.8, pp.28--31.
-/

namespace BenderSuzuki.ZD
open Theory.GroupTheory PFAppendixIII
universe u
variable {G : Type u} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}

/-- Assemble Section 3 after discharging its local geometry and index inputs. -/
public theorem actionSectionThree_of_local_and_indices
    (h : IsProductDisconnected Z M)
    (hl : SectionThreeLocal Z M) (hi : SectionThreeIndices Z M) :
    ActionSectionThree Z M := by
  refine ⟨sectionThree_swap h, hl.swapping_core, hl.swapping_sylow, ?_, ?_, ?_⟩
  · intro z hz hzM t ht beta hb p hp hpOdd P hPp hPD hPNorm
    exact sectionThree_swapping_bound h hl hi hz hzM ht beta hb hp hpOdd hPp hPD hPNorm
  · intro z hz hzM p hp hpOdd beta hb P hPp hPD hPNorm
    exact sectionThree_base_bound h hl hi hz hzM hp hpOdd beta hb hPp hPD hPNorm
  · intro z hz hzM p hp hpOdd beta hb
    exact sectionThree_invariant_sylow h hl hi hz hzM hp hpOdd beta hb

/-- All distinguished Section 3 facts follow from product disconnection. -/
public theorem actionSectionThree_of_productDisconnected
    (h : IsProductDisconnected Z M) : ActionSectionThree Z M :=
  actionSectionThree_of_local_and_indices h
    (sectionThreeLocal_of_productDisconnected h)
    (sectionThreeIndices_of_productDisconnected h)

/-- Section 3 at the minimal-counterexample assembly boundary. -/
public theorem actionSectionThree_of_minimalCounterexample
    (h : MinimalCounterexample Z M) (_hs : SimpleReduction Z M) :
    ActionSectionThree Z M :=
  actionSectionThree_of_productDisconnected h.disconnected

end BenderSuzuki.ZD
