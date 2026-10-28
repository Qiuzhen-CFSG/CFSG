module

public import CFSG.Quasithin.ChapterK.Section01To04.RankOne.Source
public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.LinearExclusion.RankThree.ActorBounds
public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.LinearExclusion.RankThree.SmallDegree.NativeCalculation
public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.LinearExclusion.RankThree.TwelveFixedSpaces.InnerFour
public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.LinearExclusion.RankThree.TwelveFixedSpaces.GraphWitnesses
public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.LinearExclusion.RankThree.TwelveFixedSpaces
public import Theory.SpecificGroups.PSL3.OrdinaryCenterRecognition
public import Theory.SpecificGroups.PSL3Three.GraphWitnesses.Conjugacy
public import Theory.SpecificGroups.PSL3Three.GraphWitnesses.EightCentralizers


/-!
# The PSL₃(3) exclusion at the cubic threshold

The ordinary scalar covering forces the original component center to vanish.
Three conjugate involutions and the ambient two-rank bound give degree at most
eighteen; the native representation and field calculations force degree twelve.
Two inner four-group conjugates bound the inner fixed space. The actual graph
involution and elementary-eight witnesses give the remaining outer bounds,
contradicting the fixed space of a cubic actor of ratio at most two.

All covers, quotient markings and ambient graph actions are retained.
Source: Aschbacher--Smith K.2, printed p.453 (PDF p.464), citing
Guralnick--Malle, Classification of 2F-modules I, Proposition 4.2.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.LinearExclusion
namespace CFSG.Quasithin.ChapterK.OddCharacteristic

/-- Strict K.2 cubic bound on the original action, including graph automorphisms. -/
theorem source_pslThree_three_cubic_bound {G V : Type*} [Group G] [Finite G] [AddCommGroup V]
    [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) (h : SourceAction ρ)
    (hm : ClassicalGroup.IsPSL
      ((generalizedFitting G) ⧸ center (generalizedFitting G)) 3 3) :
    2 < cubicRatio ρ := by
  have hz : center (generalizedFitting G) = ⊥ := by
    let : IsQuasisimple (generalizedFitting G) := h.quasisimple
    obtain ⟨F, _, _, hc, ⟨e⟩⟩ := hm
    have hd := Matrix.PSL3.OrdinaryCenterRecognition.center_card_dvd
      (by omega : Nat.card F ≠ 2) (by omega : Nat.card F ≠ 4) e
    rw [hc] at hd
    norm_num at hd
    exact hd
  by_contra hn
  have hq : cubicRatio ρ ≤ 2 := le_of_not_gt hn
  have hr := RankThree.source_two_rank_pslThree ρ h (by decide) (by decide) hm
  have hgen := RankThree.source_three_conjugates_pslThree ρ h (by decide) (by decide) hm
  have hlo := RankThree.source_degree_at_least_twelve ρ h hm
  have hup := RankThree.source_degree_le_six_rank ρ h hgen hq
  have hd := RankThree.source_degree_twelve_of_centerless_native_calculation
    ρ h hm hr hlo hup hz
  have hw := RankThree.TwelveFixedSpaces.GraphWitnesses.source_witnesses_of_centerless_graph_calculations
    ρ h hm hz Matrix.PSL3Three.GraphWitnesses.outer_involution_graph_conjugate
    (Matrix.PSL3Three.GraphWitnesses.EightCentralizers.eight_witness
      Matrix.PSL3Three.GraphWitnesses.outer_involution_graph_conjugate)
  have hb := RankThree.TwelveFixedSpaces.source_bounds_of_local_calculations ρ h hd
    (RankThree.TwelveFixedSpaces.source_inner_four_fixedSpace_le_six ρ h hm hd) hw.1 hw.2
  exact (not_lt_of_ge hq) (RankThree.source_twelve_exclusion_of_fixed_spaces
    ρ h hd hr hgen (fun A hA => (hb A hA).1) (fun A hA => (hb A hA).2))

/-- The PSL₃(3) central quotient is excluded by the threshold-two source premise. -/
theorem not_pslThree_three {G V : Type*} [Group G] [Finite G] [AddCommGroup V]
    [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    {ρ : Representation (ZMod 2) G V} {L : Subgroup G}
    (hs : RankOne.SourceHypotheses ρ L)
    (hm : ClassicalGroup.IsPSL (L ⧸ center L) 3 3) : False := by
  rcases hs with ⟨hsq, hfit, hquasi, hfaith, hirr, hsmall⟩
  subst L
  exact (not_lt_of_ge hsmall)
    (source_pslThree_three_cubic_bound ρ ⟨hsq, hquasi, hfaith, hirr⟩ hm)

end CFSG.Quasithin.ChapterK.OddCharacteristic
