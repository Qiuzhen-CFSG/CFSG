module

public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.OutsideStructure.Statements
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankOne.Reduction.PlaneGeometry
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.Candidates.Alternatives

/-!
# Earlier inputs for the conditional rank-one reduction

These inputs are the standing characteristic-two condition, the indicated
clauses of 15.3.7 and 15.3.9, the genuine twelve conclusions of 15.3.11,
15.3.25 for every outside overgroup, and the component facts of 15.3.33--34.
The component orbit bound is the earlier 1.2 bound. The natural action and
the original residual choice are the actual choices in `LocalData`.

There is no rank-one conclusion here: neither the selected second choice,
the residual identity, index three, plane commutator, exclusion of A₄,
inner action, component containment, nor any quotient condition is assumed.
The alternatives (i)--(iii) of 15.3.43 remain a separate explicit input to
the assembly theorem. The source owner must supply these earlier results;
this interface does not purport to prove them.

Source: Aschbacher--Smith, combined manuscript (1 March 2004),
printed pp.1122--1125, 1130--1134, and 15.3.43 on pp.1139--1140.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03.RankOne

variable {G : Type*} [Group G]

/-- Explicit earlier source results, before assuming the S₃ shadow. -/
structure ReductionSourceInputs (d : CharacteristicTwo.LocalData G)
    (I L : Subgroup G) : Prop where
  characteristic_two : centralizer (pCore 2 d.M : Set d.M) ≤ pCore 2 d.M
  residual_image : d.action.image d.Y =
    Stellmacher.twoResidualAmbient (⊤ : Subgroup OrthogonalActor)
  residual_core : (d.Y ⊔ (d.T : Subgroup G)).pCoreIn 2 =
    (d.T : Subgroup G) ⊓ centralizer (d.V : Set G)
  residual_quotient : PlaneGeometry.SourceQuotientAlternatives d.Y d.V
  not_alternating_square :
    ¬ Nonempty (d.Y ≃* (alternatingGroup (Fin 4) × alternatingGroup (Fin 4)))
  outside_structure : OutsideStructure.Conclusions d I
  outside_not_characteristic_two : ∀ A ∈ d.Hplus,
    generalizedFitting A ≠ pCore 2 A
  component_le : L ≤ I
  component : IsComponent I (L.subgroupOf I)
  component_center : (center L).map L.subtype = L.pCoreIn 2
  component_outside : ¬ L ≤ d.M
  component_rank : 1 ≤ primeRank 3 L
  overgroup_rank : primeRank 3 I ≤ 2
  component_orbit : (normalizer (L : Set G)).relIndex I ≤ 2
  invariant_subgroup : ∀ D : Subgroup G, D ≤ localSpan L d.S →
    d.Yplus ⊔ d.S ≤ normalizer (D : Set G) →
    generalizedFitting D = pCore 2 D → D ≤ d.M ⊓ I

variable [Finite G]

/-- Convert the literal quotient alternatives of 15.3.11(5) to the
numerical alternative used in `Preliminary`, preserving O^{3′}. -/
theorem preliminary_alternative_of_source (d : CharacteristicTwo.LocalData G)
    {I : Subgroup G}
    (h : OutsideStructure.RankTwoCase d I ∨ OutsideStructure.RankOneCase d I) :
    3 < (pCore 2 d.Yplus).index ∨
      (OutsideStructure.SecondChoice d ∧ d.Yplus = threeResidualIn (d.M ⊓ I)) := by
  rcases h with h | h
  · left
    rw [Subgroup.index_eq_card]
    rcases h.1 with he | hq
    · obtain ⟨e⟩ := he
      rw [Nat.card_congr e.toEquiv]
      norm_num [Nat.card_eq_fintype_card]
    · rw [hq.2.1]
      decide
  · exact Or.inr ⟨h.1, by rw [threeResidualIn_eq_primeToResidual]; exact h.2.2.1⟩

end CFSG.Quasithin.Chapter15.Section03.RankOne
