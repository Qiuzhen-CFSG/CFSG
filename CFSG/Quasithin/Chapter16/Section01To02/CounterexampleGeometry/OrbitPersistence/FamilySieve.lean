module

public import CFSG.Quasithin.Chapter16.Section01To02.CounterexampleGeometry.OrbitPersistence.FamilySieve.SourceReduction
public import CFSG.Quasithin.Chapter16.Section01To02.CounterexampleGeometry.OrbitPersistence.FamilySieve.PrimeModels
public import CFSG.Quasithin.Chapter16.Section01To02.CounterexampleGeometry.OrbitPersistence.FamilySieve.CoveredModels
public import CFSG.Quasithin.Chapter16.Section01To02.CounterexampleGeometry.OrbitPersistence.FamilySieve.JankoExclusion

/-!
# Conditional assembly of the component-list intersection

Apply A.3.8 in the two-core quotient of the involution centralizer. When
L has trivial two-core, the actual quotient equivalence and (E2) give the
rank-one list, with the Fermat/Mersenne restriction retained. Otherwise
L is nonsimple, so 16.1.2 supplies its central-quotient list. Its center-core
equality identifies that quotient with the one in the A.3.8 list.

The actual J₁ carrier is excluded by the complete (E2) comparison, and
the eight nonsimple-cover models meet the orbit list only in Sz(8).
The final assembly discharges both comparisons. Only the source inputs
A.3.8(3) and 16.1.2(1) remain explicit, belonging to their earlier owners;
no model comparison or orbit witness is assumed.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
(E2) and 16.1.2 on p.1170; Lemma 16.2.5 on p.1174.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter16.CounterexampleGeometry
open FamilySieve
universe u

private theorem not_simple_of_nontrivial_core {X : Type*} [Group X] [Finite X]
    [IsQuasisimple X] (hc : pCore 2 X ≠ ⊥) : ¬ IsSimpleGroup X := by
  intro hs
  let := hs
  have hz : center X = ⊥ := by
    rcases (inferInstance : (center X).Normal).eq_bot_or_eq_top with h | h
    · exact h
    · exact (Group.IsPerfect.not_isMulCommutative X (center_eq_top_iff.mp h)).elim
  exact hc (le_bot_iff.mp ((IsQuasisimple.pCore_le_center 2).trans hz.le))

variable {G : Type u} [Group G] [Finite G] {K : GroupClass.{u}}
  {T : Sylow 2 G} {z : G} {L : Subgroup G}

/-- Assemble the refined alternative from the earlier source statements and
explicit concrete model comparisons. No orbit witness is needed. -/
theorem CounterexampleSetup.refinedAlternative_of_comparisons
    (c : CounterexampleSetup K T z L)
    (a38 : SourceA38Three K) (s1612 : Source1612One K G)
    (hj : ∀ (S : Type u) [Group S] [Finite S], pCore 2 S = ⊥ →
      IsEvenTypeComponent S → Nonempty (S ≃* Janko1.Model) → False)
    (hcover : ∀ (S : Type u) [Group S] [Finite S],
      SourceOrbitModel S → NonsimpleSourceModel S →
        Nonempty (S ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup 1)) :
    RefinedComponentAlternative L := by
  let := c.localSetup.component.quasisimple
  have horbit := quotient_model c a38
  by_cases hc : pCore 2 L = ⊥
  · let e : L ≃* (L ⧸ pCore 2 L) :=
      ((QuotientGroup.quotientMulEquivOfEq hc).trans QuotientGroup.quotientBot).symm
    exact .rank_one (simple_intersection_of_janko_exclusion hj hc
      (c.global.evenType.components z L c.localSetup.involution c.localSetup.component)
      (horbit.of_mulEquiv e))
  · obtain ⟨hcenter, hmodel⟩ := s1612 c.global z L c.localSetup.involution
      c.localSetup.component (not_simple_of_nontrivial_core hc)
    exact .covered_suzuki_eight hc (hcover _ horbit
      (hmodel.of_mulEquiv (QuotientGroup.quotientMulEquivOfEq hcenter.symm)))

/-- The list intersection in 16.2.5, conditional only on the earlier source
clauses A.3.8(3) and 16.1.2(1). All concrete model comparisons are discharged.
The odd prime retains its Fermat/Mersenne restriction, and the covered Sz(8)
alternative retains the nontrivial two-core and actual quotient isomorphism. -/
theorem CounterexampleSetup.refinedAlternative
    (c : CounterexampleSetup K T z L)
    (a38 : SourceA38Three K) (s1612 : Source1612One K G) :
    RefinedComponentAlternative L :=
  c.refinedAlternative_of_comparisons a38 s1612 janko_one_exclusion
    (fun _ _ _ => covered_model_intersection)

/-- The displayed list of 16.2.5 from its earlier source inputs, forgetting
only the additional parameter restrictions retained in `refinedAlternative`. -/
theorem CounterexampleSetup.componentAlternative
    (c : CounterexampleSetup K T z L)
    (a38 : SourceA38Three K) (s1612 : Source1612One K G) :
    ComponentAlternative L :=
  (c.refinedAlternative a38 s1612).to_componentAlternative

end CFSG.Quasithin.Chapter16.CounterexampleGeometry
end
