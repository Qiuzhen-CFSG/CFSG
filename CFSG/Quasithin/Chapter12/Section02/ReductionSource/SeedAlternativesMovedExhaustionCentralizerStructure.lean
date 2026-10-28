module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.SeedAlternativesMovedExhaustionSections
public import CFSG.Quasithin.Chapter3.Section02.ChosenSource325.MovedExhaustionCentralizerPrime

/-!
# The component-centralizer selection for the chosen seed

Work in the faithful image of the literal normalizer on its orbit U, retaining
K as the image of L and its central cover. The original Sylow actor's component
centralizer is faithful on the embedded generalized Fitting subgroup of C(K).
For a starred actor, a nontrivial component centralizer produces a nontrivial
A-invariant X = [X,C_A(K)] inside C(K): either a subgroup of its three-core,
or the literal A-orbit of an ordinary component. Full movement by K, supplied
by the chosen seed, excludes the five-core alternative of D.2.13.

Under the original multiple-overgroup standing guard and strict U > W, this
construction combines with the section-action argument: there is such an X
or an actual FF offender on W or U/W. The FF exclusions, order three for X,
Suzuki exclusion, and final U = W and Source325 assembly remain with
qt-baumann-fsu; no nontrivial-centralizer witness is assumed in that application.
Source: Aschbacher--Smith, D.3.9(2) and D.3.12--19, printed pp.200--204.
-/

public noncomputable section

namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Chapter3.Section02.ChosenSource325 ChapterD
open scoped IsMulCommutative ENNReal
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The component centralizer inside the original Sylow actor is faithful
on the embedded generalized Fitting subgroup of the component centralizer. -/
theorem normalizer_centralizer_fitting_kernel
    (D : ChosenModule T L V) (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hc : V ⊓ centralizer (L : Set G) = ⊥) :
    letI := D.normalizerOrbit_elementary h
    let M := normalizer (L : Set G)
    let U := componentOrbit V M
    let hn := le_normalizer_componentOrbit V M
    let K := (L.subgroupOf M).map (internalHom M U hn)
    let C := centralizer (K : Set (internalActionImage M U hn))
    ∀ A : Subgroup (internalActionImage M U hn),
      A ≤ internalSylow T M U hn D.sylow_normalizes_component →
      (A ⊓ C) ⊓ centralizer ((generalizedFitting C).map C.subtype : Set _) = ⊥ := by
  let := D.normalizerOrbit_elementary h
  let M := normalizer (L : Set G)
  let U := componentOrbit V M
  let hn := le_normalizer_componentOrbit V M
  let f := internalHom M U hn
  let K := (L.subgroupOf M).map f
  let : (L.subgroupOf M).Normal := normal_subgroupOf_of_le_normalizer le_rfl
  let : K.Normal := Normal.map inferInstance f
    (UniqueFactor.actionHom M U hn).rangeRestrict_surjective
  let := D.normalizer_component_quasisimple h hc
  dsimp only
  intro A hAS
  exact component_centralizer_twoSubgroup_fitting_kernel K
    (D.normalizerActor_twoCore_eq_bot h) _
    ((internalSylow T M U hn D.sylow_normalizes_component).isPGroup'.to_le
      (inf_le_left.trans hAS)) inf_le_right

/-- A nontrivial centralizer of the original elementary actor produces a
concrete A-invariant subgroup X in C(K), fully moved by C_A(K). The selected
component and three-core remain subgroups of the original action image. -/
theorem normalizer_starred_centralizer_moved_subgroup
    (D : ChosenModule T L V) (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hc : V ⊓ centralizer (L : Set G) = ⊥) :
    letI := D.normalizerOrbit_elementary h
    let M := normalizer (L : Set G)
    let U := componentOrbit V M
    let hn := le_normalizer_componentOrbit V M
    let ρ := UniqueFactor.imageRepresentation M U hn
    let K := (L.subgroupOf M).map (internalHom M U hn)
    let C := centralizer (K : Set (internalActionImage M U hn))
    ∀ A : Subgroup (internalActionImage M U hn), A ∈ QhatStar ρ → A ⊓ C ≠ ⊥ →
      ∃ X : Subgroup (internalActionImage M U hn),
        X ≤ C ∧ A ≤ normalizer (X : Set _) ∧ X ≠ ⊥ ∧ ⁅X,A ⊓ C⁆ = X ∧
        ((X ≤ (pCore 3 C).map C.subtype ∧ IsPGroup 3 X) ∨
          ∃ J : Subgroup (internalActionImage M U hn),
            IsComponent (internalActionImage M U hn) J ∧ J ≤ C ∧ X = componentOrbit J A) := by
  let := D.normalizerOrbit_elementary h
  let M := normalizer (L : Set G)
  let U := componentOrbit V M
  let hn := le_normalizer_componentOrbit V M
  let f := internalHom M U hn
  let K := (L.subgroupOf M).map f
  let : (L.subgroupOf M).Normal := normal_subgroupOf_of_le_normalizer le_rfl
  let : K.Normal := Normal.map inferInstance f
    (UniqueFactor.actionHom M U hn).rangeRestrict_surjective
  let := D.normalizer_component_quasisimple h hc
  dsimp only
  intro A hA hAC
  exact exists_starred_moved_subgroup_in_component_centralizer
    (UniqueFactor.imageRepresentation M U hn) (UniqueFactor.imageRepresentation_injective M U hn)
    K (D.normalizerActor_twoCore_eq_bot h) (D.normalizer_component_fully_moved h hc) hA hAC

/-- Under the source standing guard and strict U > W, a starred actor gives
one of the two literal section offenders or an explicitly constructed moved
subgroup of its component centralizer. No centralizer witness is assumed. -/
theorem exists_normalizer_moved_centralizer_or_section_offender_of_many
    (D : ChosenModule T L V) (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hc : V ⊓ centralizer (L : Set G) = ⊥)
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
          ((X ≤ (pCore 3 C).map C.subtype ∧ IsPGroup 3 X) ∨
              ∃ J : Subgroup (internalActionImage M U hn),
              IsComponent (internalActionImage M U hn) J ∧ J ≤ C ∧ X = componentOrbit J A)) ∨
        (IsOffender (imageRepresentation S.toRepresentation)
          (actionSubgroup S.toRepresentation (A.subgroupOf D.normalizerLocalActor)) ∨
        IsOffender (imageRepresentation S.quotientRepresentation)
          (actionSubgroup S.quotientRepresentation (A.subgroupOf D.normalizerLocalActor)))) := by
  let := D.normalizerOrbit_elementary h.toHypothesis1221
  obtain ⟨A,hAS,hA,hcase⟩ := D.exists_normalizer_centralizer_or_section_offender_of_many
    h hmany hc hne
  refine ⟨A,hAS,hA,?_⟩
  rcases hcase with hk | hff
  · exact Or.inl (D.normalizer_starred_centralizer_moved_subgroup h.toHypothesis1221 hc A hA hk)
  · exact Or.inr hff
end CFSG.Quasithin.Chapter12.Section02.ChosenModule
