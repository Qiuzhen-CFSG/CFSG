module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.SeedAlternativesMovedExhaustionThreeModels
public import CFSG.Quasithin.Chapter3.Section02.ChosenSource325.MovedExhaustionComponentRank

/-!
# Three-rank and normal components in the literal normalizer centralizer

Every marked D.3.10 constituent contains an inverted order-three subgroup.
Transport it through the characteristic seed-action kernel and the original
map from L. The strongly quasithin maximal two-local cover then bounds the
three-rank of C(K) by one, before choosing any component in that centralizer.
A selected component whose order is divisible by three is unique there and
normal in the full faithful image; its orbit collapses to that component,
and the centralizer has trivial three-core.

The final application refines the actual remaining exhaustion alternatives.
The three-free component branch and the FF-section branches, and the later
normal-component module argument, still require exclusion by qt-baumann-fsu.
No equality U = W or multiplicity bound is assumed here.
Source: Aschbacher--Smith D.3.14--15, printed p.202, used in3.2.5, p.580.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
open CFSG.Quasithin.ChapterD

namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter3.Section02.ChosenSource325 ChapterB.QuasisimpleSource
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- D.3.14's centralizer bound for every marked constituent, without the
extra three-rank-one premise on the component in the earlier SL₃ adapter. -/
theorem normalizer_component_centralizer_three_rank_bound_of_many
    (D : ChosenModule T L V) (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hc : V ⊓ centralizer (L : Set G) = ⊥)
    (hm : V < componentOrbit V (T : Subgroup G)) :
    let M := normalizer (L : Set G)
    let U := componentOrbit V M
    let hn := le_normalizer_componentOrbit V M
    let K := (L.subgroupOf M).map (internalHom M U hn)
    primeRank 3 (centralizer (K : Set (internalActionImage M U hn))) ≤ 1 := by
  let := D.normalizerOrbit_elementary h.toHypothesis1221
  let M := normalizer (L : Set G)
  let U := componentOrbit V M
  let hn := le_normalizer_componentOrbit V M
  let f := internalHom M U hn
  let K := (L.subgroupOf M).map f
  have hmodel := D.seed_constituentModel_of_moved_of_many h hmany hc hm
  obtain ⟨a,_⟩ := D.normalizer_component_actionEquiv_of_constituentModel h.toHypothesis1221 hmodel
  have hu := Chapter1.Section02.nonsolvable_uniqueness_of_theoremsAC
    (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
    (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X))
    h.simpleQTKE T h.maximal_faithful.1
  have hmax : IsMaximalTwoLocal M := by
    simpa only [D.localOrbit_eq] using hu.normalizer_maximal
  have hM : primeRank 3 M ≤ 2 :=
    (h.simpleQTKE.twoLocal_sqtk hmax.1).stronglyQuasithin 3 Nat.prime_three (by decide)
  exact component_centralizer_three_rank_le_one_of_constituentModel f
    (UniqueFactor.actionHom M U hn).rangeRestrict_surjective hM K
    (D.seedRepresentation.comp D.componentImage.subtype) hmodel a.groupEquiv

/-- A component in the literal centralizer whose order is divisible by three
is normal in the full action image. Its selected actor orbit is itself, its
three-rank is one, and the centralizer's three-core is trivial. -/
theorem normalizer_centralizer_component_structure_of_many
    (D : ChosenModule T L V) (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hc : V ⊓ centralizer (L : Set G) = ⊥)
    (hm : V < componentOrbit V (T : Subgroup G)) :
    let M := normalizer (L : Set G)
    let U := componentOrbit V M
    let hn := le_normalizer_componentOrbit V M
    let K := (L.subgroupOf M).map (internalHom M U hn)
    let C := centralizer (K : Set (internalActionImage M U hn))
    ∀ J A : Subgroup (internalActionImage M U hn),
      IsComponent (internalActionImage M U hn) J → J ≤ C → 3 ∣ Nat.card J →
      J.Normal ∧ componentOrbit J A = J ∧ primeRank 3 J = 1 ∧ pCore 3 C = ⊥ := by
  let M := normalizer (L : Set G)
  let U := componentOrbit V M
  let hn := le_normalizer_componentOrbit V M
  let f := internalHom M U hn
  let K := (L.subgroupOf M).map f
  let C := centralizer (K : Set (internalActionImage M U hn))
  let : (L.subgroupOf M).Normal := normal_subgroupOf_of_le_normalizer le_rfl
  let : K.Normal := Normal.map inferInstance f
    (UniqueFactor.actionHom M U hn).rangeRestrict_surjective
  have hr := D.normalizer_component_centralizer_three_rank_bound_of_many h hmany hc hm
  dsimp only
  intro J A hJ hJC hJthree
  exact component_orbit_structure_of_three_rank_one C hr J hJ hJC hJthree A

/-- The actual remaining exhaustion alternatives now have either a
three-free component orbit, one normal component of three-rank one, or an
FF offender on the unchanged W or U/W section. All inputs remain original. -/
theorem exists_normalizer_rank_one_component_or_section_offender_of_many
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
    let C := centralizer (K : Set (internalActionImage M U hn))
    let S := D.normalizerLocalSection h.toHypothesis1221
    ∃ A : Subgroup (internalActionImage M U hn),
      A ≤ internalSylow T M U hn D.sylow_normalizes_component ∧ A ∈ QhatStar ρ ∧
      ((∃ X : Subgroup (internalActionImage M U hn),
          X ≤ C ∧ A ≤ normalizer (X : Set _) ∧ X ≠ ⊥ ∧ ⁅X,A ⊓ C⁆ = X ∧
          ∃ J : Subgroup (internalActionImage M U hn),
            IsComponent (internalActionImage M U hn) J ∧ J ≤ C ∧ X = componentOrbit J A ∧
            (¬ 3 ∣ Nat.card J ∨
              (X = J ∧ J.Normal ∧ primeRank 3 J = 1 ∧ pCore 3 C = ⊥))) ∨
        (IsOffender (imageRepresentation S.toRepresentation)
          (actionSubgroup S.toRepresentation (A.subgroupOf D.normalizerLocalActor)) ∨
        IsOffender (imageRepresentation S.quotientRepresentation)
          (actionSubgroup S.quotientRepresentation (A.subgroupOf D.normalizerLocalActor)))) := by
  let := D.normalizerOrbit_elementary h.toHypothesis1221
  obtain ⟨A,hAS,hA,hcase⟩ :=
    D.exists_normalizer_component_or_section_offender_of_many h hmany hc hm hne
  refine ⟨A,hAS,hA,?_⟩
  rcases hcase with ⟨X,hXC,hAX,hXn,hXB,J,hJ,hJC,hX⟩ | hff
  · refine Or.inl ⟨X,hXC,hAX,hXn,hXB,J,hJ,hJC,hX,?_⟩
    by_cases hd : 3 ∣ Nat.card J
    · obtain ⟨hn,ho,hr,hcore⟩ :=
        D.normalizer_centralizer_component_structure_of_many h hmany hc hm J A hJ hJC hd
      exact Or.inr ⟨hX.trans ho,hn,hr,hcore⟩
    · exact Or.inl hd
  · exact Or.inr hff

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
