module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.SeedAlternativesMovedExhaustionCentralizerStructure
public import CFSG.Quasithin.Chapter3.Section02.ChosenSource325.MovedExhaustionCentralizerThree

/-!
# The order-three branch on the literal chosen-seed action

For the image K of L on U = componentOrbit V (normalizer L), fixed-freeness
is transported from the actual subgroup centralizer identity. The original
normalizer is strongly quasithin, supplying the prequotient rank bound.
The three-core choice now has order three, forces K's three-rank at most one,
and makes C_A(K) nontrivial and proper. The proved centralizer identities
then give Qhat membership and ratio strictly below two on the original
Sylow orbit W = componentOrbit V T.

Under the multiple-overgroup standing guard and U > W, the resulting
alternative has no extra input: this order-three branch, a literal orbit
of a component of C(K), or an FF offender on W or U/W. The component and
section-model exclusions and final exhaustion/Source325 assembly remain
with qt-baumann-fsu. These alternatives are not themselves a contradiction.
Source: Aschbacher--Smith D.3.9(2), D.3.14, D.3.18--19 and3.2.5,
printed pp.200--204 and580.
-/

public noncomputable section
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Chapter3.Section02.ChosenSource325 ChapterD
open scoped IsMulCommutative ENNReal
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- Fixed-freeness on U for the literal image of L, with its center retained. -/
theorem normalizer_component_fixedSpace_eq_bot
    (D : ChosenModule T L V) (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hc : V ⊓ centralizer (L : Set G) = ⊥) :
    letI := D.normalizerOrbit_elementary h
    let M := normalizer (L : Set G)
    let U := componentOrbit V M
    let hn := le_normalizer_componentOrbit V M
    let K := (L.subgroupOf M).map (internalHom M U hn)
    fixedSpace (UniqueFactor.imageRepresentation M U hn) K = ⊥ := by
  let := D.normalizerOrbit_elementary h
  let M := normalizer (L : Set G)
  let U := componentOrbit V M
  let hn := le_normalizer_componentOrbit V M
  let f := internalHom M U hn
  have hz := D.normalizerOrbit_inf_centralizer_eq_bot h hc
  apply bot_unique
  intro v hv
  have hvc : v.toMul.val ∈ centralizer (L : Set G) := by
    intro l hl
    let l' : M := ⟨l,L.le_normalizer hl⟩
    have he := congrArg (fun z : Additive U => z.toMul.val)
      (hv ⟨f l',⟨l',hl,rfl⟩⟩)
    change l * v.toMul.val * l⁻¹ = v.toMul.val at he
    exact mul_inv_eq_iff_eq_mul.mp he
  have hv0 : v.toMul.val = 1 := hz.le ⟨v.toMul.property,hvc⟩
  change v.toMul = 1
  exact Subtype.ext hv0

/-- The three-core branch has an actual order-three subgroup, a proper
component centralizer and the strict D.3.19 ratio on the original W. -/
theorem normalizer_starred_centralizer_three_or_component
    (D : ChosenModule T L V) (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hc : V ⊓ centralizer (L : Set G) = ⊥) :
    letI := D.normalizerOrbit_elementary h
    let M := normalizer (L : Set G)
    let U := componentOrbit V M
    let W := componentOrbit V (T : Subgroup G)
    let hn := le_normalizer_componentOrbit V M
    let ρ := UniqueFactor.imageRepresentation M U hn
    let K := (L.subgroupOf M).map (internalHom M U hn)
    let C := centralizer (K : Set (internalActionImage M U hn))
    ∀ A : Subgroup (internalActionImage M U hn),
      A ≤ internalSylow T M U hn D.sylow_normalizes_component →
      A ∈ QhatStar ρ → A ⊓ C ≠ ⊥ →
      ∃ X : Subgroup (internalActionImage M U hn),
        X ≤ C ∧ A ≤ normalizer (X : Set _) ∧ X ≠ ⊥ ∧ ⁅X,A ⊓ C⁆ = X ∧
        ((X ≤ (pCore 3 C).map C.subtype ∧ Nat.card X = 3 ∧ primeRank 3 K ≤ 1 ∧
          ⊥ < A ⊓ C ∧ A ⊓ C < A ∧
          restrictedSubgroup ρ (internalSection U W) A ∈
            Qhat (subspaceImageRepresentation ρ (internalSection U W)) ∧
          actionRatio (subspaceImageRepresentation ρ (internalSection U W))
            (restrictedSubgroup ρ (internalSection U W) A) < 2) ∨
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
  have hu := Chapter1.Section02.nonsolvable_uniqueness_of_theoremsAC
    (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
    (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X))
    h.simpleQTKE T h.maximal_faithful.1
  have hmax : IsMaximalTwoLocal M := by
    simpa only [D.localOrbit_eq] using hu.normalizer_maximal
  have hr : primeRank 3 M ≤ 2 :=
    (h.simpleQTKE.twoLocal_sqtk hmax.1).stronglyQuasithin 3 Nat.prime_three (by decide)
  dsimp only
  intro A hAS hA hAC
  obtain ⟨X,hXC,hnX,hXn,hXB,hcase⟩ :=
    exists_starred_proper_three_or_component_in_centralizer f
      (UniqueFactor.actionHom M U hn).rangeRestrict_surjective hr
      (UniqueFactor.imageRepresentation M U hn) (UniqueFactor.imageRepresentation_injective M U hn)
      K (D.normalizerActor_twoCore_eq_bot h) (D.normalizer_component_fully_moved h hc)
      (D.normalizer_component_fixedSpace_eq_bot h hc) hA hAC
  refine ⟨X,hXC,hnX,hXn,hXB,?_⟩
  rcases hcase with ⟨hXP,hXcard,hKr,hm⟩ | hcomp
  · have hproper : A ⊓ centralizer (K : Set (internalActionImage M U hn)) < A := by
      apply lt_of_le_of_ne inf_le_left
      intro he
      exact hm (he ▸ inf_le_right)
    exact Or.inl ⟨hXP,hXcard,hKr,bot_lt_iff_ne_bot.mpr hAC,hproper,
      D.normalizer_starred_section_strict_of_component_centralizer h hc A hAS hA hAC hm⟩
  · exact Or.inr hcomp

/-- The original multiple-overgroup guard and strict U > W construct a starred
actor and reduce the missing exhaustion step to the component branch, the
order-three branch with proper centralizer, or an actual section offender. -/
theorem exists_normalizer_three_or_component_or_section_offender_of_many
    (D : ChosenModule T L V) (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hc : V ⊓ centralizer (L : Set G) = ⊥)
    (hne : componentOrbit V (normalizer (L : Set G)) ≠ componentOrbit V (T : Subgroup G)) :
    letI := D.normalizerOrbit_elementary h.toHypothesis1221
    let M := normalizer (L : Set G)
    let U := componentOrbit V M
    let W := componentOrbit V (T : Subgroup G)
    let hn := le_normalizer_componentOrbit V M
    let ρ := UniqueFactor.imageRepresentation M U hn
    let K := (L.subgroupOf M).map (internalHom M U hn)
    let C := centralizer (K : Set (internalActionImage M U hn))
    let S := D.normalizerLocalSection h.toHypothesis1221
    ∃ A : Subgroup (internalActionImage M U hn),
      A ≤ internalSylow T M U hn D.sylow_normalizes_component ∧ A ∈ QhatStar ρ ∧
      ((∃ X : Subgroup (internalActionImage M U hn),
          X ≤ C ∧ A ≤ normalizer (X : Set _) ∧ X ≠ ⊥ ∧ ⁅X,A ⊓ C⁆ = X ∧
          ((X ≤ (pCore 3 C).map C.subtype ∧ Nat.card X = 3 ∧ primeRank 3 K ≤ 1 ∧
            ⊥ < A ⊓ C ∧ A ⊓ C < A ∧
            restrictedSubgroup ρ (internalSection U W) A ∈
              Qhat (subspaceImageRepresentation ρ (internalSection U W)) ∧
            actionRatio (subspaceImageRepresentation ρ (internalSection U W))
              (restrictedSubgroup ρ (internalSection U W) A) < 2) ∨
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
  · exact Or.inl (D.normalizer_starred_centralizer_three_or_component
      h.toHypothesis1221 hc A hAS hA hk)
  · exact Or.inr hff
end CFSG.Quasithin.Chapter12.Section02.ChosenModule
