module
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.OrdinaryRecognitionJankoFour
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.OrdinaryRecognitionRudvalis
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.OrdinaryRootGeometry

/-!
# The original ordinary symplectic marking

The actual central-quotient catalogue has been reduced to the symplectic
marking, J₄, and Rudvalis. The last two original-source exclusions close
that disjunction. The surviving marking identifies the original field
cardinality, the component itself, the original local subgroup, the literal
Sylow intersection, and the full source module simultaneously.

The final application constructs the second root-normalizer residual used
by the ordinary-component argument: together with the original L it
generates K, and the original T does not normalize it. No recognition,
action, field-comparison or placement premise remains in these statements.
Source: Aschbacher--Smith C.3.1, pp.149--151, and 4.3.6, pp.614--615.
-/

public section
open Subgroup Theory.GroupTheory ClassicalGroup
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.SourceConfiguration
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- Complete simultaneous symplectic coordinates from the original ordinary hypotheses. -/
theorem ordinarySymplecticMarking (c : SourceConfiguration T L)
    (D : Chapter12.Section02.ChosenModule T L V) (ho : IsComponent c.H c.K)
    {n : ℕ} (hn : 1 < n) (hpsl : IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n)) :
    Nonempty (OrdinarySymplecticMarking c n) := by
  rcases c.ordinary_marking_or_jankoFour_or_rudvalis D ho hn hpsl with hm | hj | hr
  · exact hm
  · exact (c.ordinary_no_jankoFour D ho hj.some).elim
  · exact (c.ordinary_no_rudvalis D ho hn hpsl hr.some).elim

/-- Actual application to the original second-root subgroup in 4.3.6. -/
theorem ordinary_symplectic_source_geometry (c : SourceConfiguration T L)
    (D : Chapter12.Section02.ChosenModule T L V) (ho : IsComponent c.H c.K)
    {n : ℕ} (hn : 1 < n) (hpsl : IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n)) :
    ∃ m : OrdinarySymplecticMarking c n,
      L ⊔ m.second = c.K.map c.H.subtype ∧
      ¬ (T : Subgroup G) ≤ normalizer (m.second : Set G) := by
  obtain ⟨m⟩ := c.ordinarySymplecticMarking D ho hn hpsl
  exact ⟨m,m.original_sup_second hn,m.second_not_normalized hn D⟩

end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.SourceConfiguration
