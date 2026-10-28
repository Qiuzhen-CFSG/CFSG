module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.SeedAlternativesMovedExhaustionSuzukiFixedSpace
public import CFSG.Quasithin.Chapter3.Section02.ChosenSource325.MovedExhaustionSuzukiExchange

/-!+# Suzuki exclusion and odd-degree natural SL₃ orbit exhaustion

On the literal chosen normalizer orbit, the faithful exchanged Suzuki pair
has displacement at least 3(2r+1) on its actor-centralizer fixed space.
The starred cubic bound limits that displacement to 2(2r+2), a contradiction.
Thus the earlier normal-support exclusion now proves U = W for the actual
odd-degree natural SL₃ seed. For every remaining strict enlargement, the
same original starred actor offends on the literal local section or quotient.

The multiple-overgroup hypothesis and the source standing guard inherited
by its cubic producer are retained. The other FF branches and the full
Source325 assembly remain with qt-baumann-fsu.
Source: Aschbacher--Smith D.3.9--10, printed pp.200--204, applied in
3.2.5, p.580; refs/quasithin.pdf.
-/

set_option backward.isDefEq.respectTransparency false
public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter3.Section02.ChosenSource325 ChapterB.QuasisimpleSource ChapterD
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The literal original normalizer action admits no exchanged Suzuki
support for a starred actor. The full module need not be irreducible. -/
theorem normalizer_not_starred_exchanged_suzuki_support
    (D : ChosenModule T L V) (h : Hypothesis1221 KnownSimple.IsKnownSimple T L) :
    letI := D.normalizerOrbit_elementary h
    let M := normalizer (L : Set G)
    let U := componentOrbit V M
    let hn := le_normalizer_componentOrbit V M
    let ρ := UniqueFactor.imageRepresentation M U hn
    ∀ J A : Subgroup (internalActionImage M U hn),
      IsComponent (internalActionImage M U hn) J → A ∈ QhatStar ρ →
      ∀ (r : ℕ), 0 < r →
      Nonempty (J ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup r) →
      ∀ a ∈ A, a ∉ normalizer (J : Set (internalActionImage M U hn)) →
        (normalizer (J : Set (internalActionImage M U hn))).index = 2 →
        componentOrbit J A = J ⊔ J.map (MulAut.conj a).toMonoidHom → False := by
  let := D.normalizerOrbit_elementary h
  intro M U hn ρ J A hJ hA r hr he a ha han hi horbit
  obtain ⟨e⟩ := he
  exact not_starred_exchanged_suzuki_support ρ
    (UniqueFactor.imageRepresentation_injective M U hn)
    (D.normalizerActor_twoCore_eq_bot h) J A hJ hi a ha han horbit hA r hr e

/-- Full normalizer exhaustion for the original moved odd-degree natural
SL₃ seed. Both the natural-support and exchanged-Suzuki branches are discharged. -/
theorem normalizerOrbit_eq_of_moved_odd_linearThree_of_many
    (D : ChosenModule T L V) (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hc : V ⊓ centralizer (L : Set G) = ⊥)
    (hm : V < componentOrbit V (T : Subgroup G))
    (F : BinaryField) (ho : Odd F.degree)
    (e : ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype) (linearNatural F 3)) :
    componentOrbit V (normalizer (L : Set G)) = componentOrbit V (T : Subgroup G) := by
  by_contra hne
  let := D.normalizerOrbit_elementary h.toHypothesis1221
  obtain ⟨A,hAS,hA,_⟩ := D.exists_normalizer_starred_in_sylow_of_many h hmany
  obtain ⟨J,hJ,_,r,hr,he,a,ha,han,hi,horbit⟩ :=
    D.normalizer_starred_support_suzuki_pair_of_odd_linearThree h hmany hc hm hne F ho e A hAS hA
  exact D.normalizer_not_starred_exchanged_suzuki_support h.toHypothesis1221
    J A hJ hA r hr he a ha han hi horbit

/-- Retain only the original seed marking at the three-rank boundary. -/
private theorem seed_odd_linearThree_of_component_rank_one
    (D : ChosenModule T L V) (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hc : V ⊓ centralizer (L : Set G) = ⊥)
    (hm : V < componentOrbit V (T : Subgroup G))
    (hr : primeRank 3 ((L.subgroupOf (normalizer (L : Set G))).map
      (internalHom (normalizer (L : Set G))
        (componentOrbit V (normalizer (L : Set G))) (le_normalizer_componentOrbit _ _))) ≤ 1) :
    ∃ F : BinaryField, Odd F.degree ∧
      Nonempty (ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype) (linearNatural F 3)) := by
  let := D.normalizerOrbit_elementary h.toHypothesis1221
  let := D.elementary
  obtain ⟨F,ho,e,_⟩ := D.normalizer_linearThree_of_rank_one_of_many h hmany hc hm hr
  exact ⟨F,ho,⟨e⟩⟩

/-- Retain only the original seed marking at the three-free support boundary. -/
private theorem seed_odd_linearThree_of_three_free_support
    (D : ChosenModule T L V) (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hc : V ⊓ centralizer (L : Set G) = ⊥)
    (hm : V < componentOrbit V (T : Subgroup G)) :
    letI := D.normalizerOrbit_elementary h.toHypothesis1221
    let M := normalizer (L : Set G)
    let U := componentOrbit V M
    let hn := le_normalizer_componentOrbit V M
    let ρ := UniqueFactor.imageRepresentation M U hn
    let K := (L.subgroupOf M).map (internalHom M U hn)
    let C := centralizer (K : Set (internalActionImage M U hn))
    ∀ J A : Subgroup (internalActionImage M U hn),
      IsComponent (internalActionImage M U hn) J → J ≤ C → ¬ 3 ∣ Nat.card J →
      A ∈ QhatStar ρ → ⁅componentOrbit J A,A ⊓ C⁆ = componentOrbit J A →
      ∃ F : BinaryField, Odd F.degree ∧
        Nonempty (ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype) (linearNatural F 3)) := by
  let := D.normalizerOrbit_elementary h.toHypothesis1221
  let := D.elementary
  intro M U hn ρ K C J A hJ hJC hthree hA hmove
  obtain ⟨F,ho,e,_⟩ := D.normalizer_linearThree_of_starred_suzuki_support_of_many
    h hmany hc hm J A hJ hJC hthree hA hmove
  exact ⟨F,ho,⟨e⟩⟩

/-- In a strict enlargement every original starred Sylow actor acts
faithfully by conjugation on the component. Each possible nontrivial
centralizer forces the now-excluded odd-degree natural SL₃ enlargement. -/
theorem normalizer_starred_component_centralizer_eq_bot_of_moved_of_many
    (D : ChosenModule T L V) (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hc : V ⊓ centralizer (L : Set G) = ⊥)
    (hm : V < componentOrbit V (T : Subgroup G))
    (hne : componentOrbit V (normalizer (L : Set G)) ≠ componentOrbit V (T : Subgroup G)) :
    letI := D.normalizerOrbit_elementary h.toHypothesis1221
    let M := normalizer (L : Set G)
    let U := componentOrbit V M
    let hn := le_normalizer_componentOrbit V M
    let ρ := UniqueFactor.imageRepresentation M U hn
    let K := (L.subgroupOf M).map (internalHom M U hn)
    ∀ A : Subgroup (internalActionImage M U hn),
      A ≤ internalSylow T M U hn D.sylow_normalizes_component → A ∈ QhatStar ρ →
      A ⊓ centralizer (K : Set (internalActionImage M U hn)) = ⊥ := by
  let := D.normalizerOrbit_elementary h.toHypothesis1221
  let := D.elementary
  intro M U hn ρ K A hAS hA
  by_contra hAC
  obtain ⟨X,_,_,_,hXB,hcase⟩ :=
    D.normalizer_starred_centralizer_three_or_component h.toHypothesis1221 hc A hAS hA hAC
  have hmodel : ∃ F : BinaryField, Odd F.degree ∧
      Nonempty (ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype) (linearNatural F 3)) := by
    rcases hcase with ⟨_,_,hKr,_⟩ | ⟨J,hJ,hJC,hX⟩
    · exact seed_odd_linearThree_of_component_rank_one D h hmany hc hm hKr
    · by_cases hthree : 3 ∣ Nat.card J
      · obtain ⟨_,_,hr,_⟩ :=
          D.normalizer_centralizer_component_structure_of_many h hmany hc hm J A hJ hJC hthree
        exact D.normalizer_linearThree_of_rank_one_support_of_many h hmany hc hm J hJ hJC hr
      · exact seed_odd_linearThree_of_three_free_support D h hmany hc hm
          J A hJ hJC hthree hA (by simpa only [←hX] using hXB)
  obtain ⟨F,ho,⟨e⟩⟩ := hmodel
  exact hne (D.normalizerOrbit_eq_of_moved_odd_linearThree_of_many h hmany hc hm F ho e)

/-- Strict enlargement leaves an actual FF offender on W or U/W.
Every component-support branch, including exchanged Suzuki, is discharged. -/
theorem exists_normalizer_faithful_section_offender_of_moved_of_many
    (D : ChosenModule T L V) (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hc : V ⊓ centralizer (L : Set G) = ⊥)
    (hm : V < componentOrbit V (T : Subgroup G))
    (hne : componentOrbit V (normalizer (L : Set G)) ≠ componentOrbit V (T : Subgroup G)) :
    letI := D.normalizerOrbit_elementary h.toHypothesis1221
    let M := normalizer (L : Set G)
    let U := componentOrbit V M
    let hn := le_normalizer_componentOrbit V M
    let ρ := UniqueFactor.imageRepresentation M U hn
    let K := (L.subgroupOf M).map (internalHom M U hn)
    let S := D.normalizerLocalSection h.toHypothesis1221
    ∃ A : Subgroup (internalActionImage M U hn),
      A ≤ internalSylow T M U hn D.sylow_normalizes_component ∧ A ∈ QhatStar ρ ∧
      A ⊓ centralizer (K : Set (internalActionImage M U hn)) = ⊥ ∧
      (IsOffender (imageRepresentation S.toRepresentation)
        (actionSubgroup S.toRepresentation (A.subgroupOf D.normalizerLocalActor)) ∨
      IsOffender (imageRepresentation S.quotientRepresentation)
        (actionSubgroup S.quotientRepresentation (A.subgroupOf D.normalizerLocalActor))) := by
  let := D.normalizerOrbit_elementary h.toHypothesis1221
  intro M U hn ρ K S
  obtain ⟨A,hAS,hA,hcase⟩ :=
    D.exists_normalizer_odd_linearThree_or_section_offender_of_many h hmany hc hm hne
  refine ⟨A,hAS,hA,
    D.normalizer_starred_component_centralizer_eq_bot_of_moved_of_many h hmany hc hm hne A hAS hA,?_⟩
  apply hcase.resolve_left
  rintro ⟨F,ho,⟨e⟩⟩
  exact hne (D.normalizerOrbit_eq_of_moved_odd_linearThree_of_many h hmany hc hm F ho e)

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
