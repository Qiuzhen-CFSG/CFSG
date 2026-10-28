module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.SeedAlternativesMovedExhaustionSuzuki
public import CFSG.Quasithin.Chapter3.Section02.ChosenSource325.MovedExhaustionSuzukiFive

/-!
# Five-divisor exclusion on the literal chosen-seed action

Theorem A bounds the odd ranks of the actual semisimple layer of Aut_M(U).
If the image K of L has order divisible by five, that bound makes any Suzuki
component in C(K) invariant under the starred actor. The existing endpoint
contradiction therefore rules out every such support.

The complete constituent-model sieve leaves only odd-degree natural SL₃
in a surviving Suzuki branch. Both the seed coordinates and the coordinates
on the full-orbit image are constructed, with their compatibility under
the original map from L. For the normal rank-one component branch, adding ternary ranks in the
semisimple layer selects the same odd-degree SL₃ model. Thus the final
application leaves an actual odd-degree SL₃ seed or an FF section under
the unchanged multiple-overgroup guard.

This proves the five-divisor exclusion, not full orbit exhaustion. The
odd-degree Suzuki branch, the normal rank-one component and the FF sections,
followed by U = W and Source325 assembly, remain with qt-baumann-fsu.
Source: Aschbacher--Smith Theorem A, D.3.9--14 and3.2.5,
printed pp.33--41,200--202 and580.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
open CFSG.Quasithin.ChapterD
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter3.Section02.ChosenSource325 ChapterB.QuasisimpleSource
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- Theorem A controls the actual semisimple layer of Aut_M(U).
This does not assert that arbitrary quotients preserve odd prime rank. -/
theorem normalizer_action_layer_sqtk
    (D : ChosenModule T L V) (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) :
    let M := normalizer (L : Set G)
    let U := componentOrbit V M
    let hn := le_normalizer_componentOrbit V M
    IsSQTK KnownSimple.IsKnownSimple (componentLayer (internalActionImage M U hn)) := by
  let M := normalizer (L : Set G)
  let U := componentOrbit V M
  let hn := le_normalizer_componentOrbit V M
  let E := componentLayer (internalActionImage M U hn)
  have hu := Chapter1.Section02.nonsolvable_uniqueness_of_theoremsAC
    (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
    (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X))
    h.simpleQTKE T h.maximal_faithful.1
  have hmax : IsMaximalTwoLocal M := by
    simpa only [D.localOrbit_eq] using hu.normalizer_maximal
  have hs := h.simpleQTKE.twoLocal_sqtk hmax.1
  have hsec : ChapterA.Section02.IsSectionOf E M :=
    (ChapterA.Section02.IsSectionOf.subgroup E).ambient_surjective
      (internalHom M U hn) (UniqueFactor.actionHom M U hn).rangeRestrict_surjective
  exact ⟨ChapterA.Section02.TheoremA.stronglyQuasithin_section
    ChapterA.Section02.theoremA_knownSimple hs.stronglyQuasithin hs.isKGroup hsec
      componentLayer_idempotent,hsec.isKGroup hs.isKGroup⟩

/-- A moved three-free component forces the original component image to
have order prime to five. Otherwise layer rank makes it actor-invariant,
contradicting the proved Suzuki endpoint on the literal full module. -/
theorem normalizer_component_five_free_of_starred_suzuki_support
    (D : ChosenModule T L V) (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hc : V ⊓ centralizer (L : Set G) = ⊥) :
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
      ¬ 5 ∣ Nat.card K := by
  let := D.normalizerOrbit_elementary h.toHypothesis1221
  let M := normalizer (L : Set G)
  let U := componentOrbit V M
  let hn := le_normalizer_componentOrbit V M
  let f := internalHom M U hn
  let K := (L.subgroupOf M).map f
  let C := centralizer (K : Set (internalActionImage M U hn))
  let : (L.subgroupOf M).Normal := normal_subgroupOf_of_le_normalizer le_rfl
  let : K.Normal := Normal.map inferInstance f
    (UniqueFactor.actionHom M U hn).rangeRestrict_surjective
  let := D.normalizer_component_quasisimple h.toHypothesis1221 hc
  have hK : IsComponent (internalActionImage M U hn) K :=
    ⟨(inferInstance : K.Normal).isSubnormal,inferInstance⟩
  dsimp only
  intro J A hJ hJC hthree hA hmove hfive
  obtain ⟨r,hr,⟨e⟩⟩ := D.normalizer_action_component_suzuki_of_three_free h J hJ hthree
  have horbit : componentOrbit J A ≤ C :=
    iSup_conjugates_le_of_le_normalizer J A C hJC
      (by exact le_normalizer_of_normal)
  have hinv := (suzuki_orbit_singleton_of_component_five_dvd K J A hK hJ
    ((D.normalizer_action_layer_sqtk h).stronglyQuasithin 5 Nat.prime_five (by decide))
    hfive horbit hr e).1
  exact D.normalizer_starred_moved_three_free_component_not_normalized h hc
    J A hJ hJC hthree hA hmove hinv

/-- The five-free reduction retains both literal seed and full-image
coordinates, with the original map from L, and preserves the SL₃ cover. -/
theorem normalizer_linearThree_of_five_free_of_many
    (D : ChosenModule T L V) (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hc : V ⊓ centralizer (L : Set G) = ⊥)
    (hm : V < componentOrbit V (T : Subgroup G))
    (hfive : ¬ 5 ∣ Nat.card ((L.subgroupOf (normalizer (L : Set G))).map
      (internalHom (normalizer (L : Set G))
        (componentOrbit V (normalizer (L : Set G))) (le_normalizer_componentOrbit _ _)))) :
    letI := D.normalizerOrbit_elementary h.toHypothesis1221
    let M := normalizer (L : Set G)
    let U := componentOrbit V M
    let hn := le_normalizer_componentOrbit V M
    let j := internalHom M U hn
    ∃ F : BinaryField, Odd F.degree ∧
      ∃ e : ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype) (linearNatural F 3),
      ∃ a : ActionEquiv (internalImageSubrepresentation hn D.normalizes).toRepresentation
        (linearNatural F 3),
      ∀ l : L, a.groupEquiv ((j.subgroupMap (L.subgroupOf M))
        ((subgroupOfEquivOfLe L.le_normalizer).symm l)) = e.groupEquiv (D.componentHom l) := by
  let := D.normalizerOrbit_elementary h.toHypothesis1221
  let := D.elementary
  have hmodel := D.seed_constituentModel_of_moved_of_many h hmany hc hm
  have ha₀ := D.normalizer_component_actionEquiv_of_constituentModel h.toHypothesis1221 hmodel
  let a := Classical.choose ha₀
  have ha := Classical.choose_spec ha₀
  have hfive' : ¬ 5 ∣ Nat.card D.componentImage := by
    rwa [←Nat.card_congr a.groupEquiv.toEquiv]
  have hlinear := constituentModel_linearThree_of_five_free
    (D.seedRepresentation.comp D.componentImage.subtype) hmodel hfive'
  let F := Classical.choose hlinear
  have ho := (Classical.choose_spec hlinear).1
  let e := Classical.choice (Classical.choose_spec hlinear).2
  let b : ActionEquiv (internalImageSubrepresentation
      (le_normalizer_componentOrbit V (normalizer (L : Set G))) D.normalizes).toRepresentation
      (linearNatural F 3) :=
    ⟨a.groupEquiv.trans e.groupEquiv,a.linearEquiv.trans e.linearEquiv,by
      intro k v
      exact (congrArg e.linearEquiv (a.intertwines k v)).trans
        (e.intertwines (a.groupEquiv k) (a.linearEquiv v))⟩
  refine ⟨F,ho,e,b,?_⟩
  intro l
  exact congrArg e.groupEquiv (ha l)

/-- Every Suzuki support on the original chosen-seed action forces the
odd-degree natural SL₃ model, with both original action intertwiners. -/
theorem normalizer_linearThree_of_starred_suzuki_support_of_many
    (D : ChosenModule T L V) (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hc : V ⊓ centralizer (L : Set G) = ⊥)
    (hm : V < componentOrbit V (T : Subgroup G)) :
    letI := D.normalizerOrbit_elementary h.toHypothesis1221
    let M := normalizer (L : Set G)
    let U := componentOrbit V M
    let hn := le_normalizer_componentOrbit V M
    let j := internalHom M U hn
    let ρ := UniqueFactor.imageRepresentation M U hn
    let K := (L.subgroupOf M).map j
    let C := centralizer (K : Set (internalActionImage M U hn))
    ∀ J A : Subgroup (internalActionImage M U hn),
      IsComponent (internalActionImage M U hn) J → J ≤ C → ¬ 3 ∣ Nat.card J →
      A ∈ QhatStar ρ → ⁅componentOrbit J A,A ⊓ C⁆ = componentOrbit J A →
      ∃ F : BinaryField, Odd F.degree ∧
        ∃ e : ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype) (linearNatural F 3),
        ∃ a : ActionEquiv (internalImageSubrepresentation hn D.normalizes).toRepresentation
          (linearNatural F 3),
        ∀ l : L, a.groupEquiv ((j.subgroupMap (L.subgroupOf M))
          ((subgroupOfEquivOfLe L.le_normalizer).symm l)) = e.groupEquiv (D.componentHom l) := by
  let := D.normalizerOrbit_elementary h.toHypothesis1221
  dsimp only
  intro J A hJ hJC hthree hA hmove
  exact D.normalizer_linearThree_of_five_free_of_many h hmany hc hm
    (D.normalizer_component_five_free_of_starred_suzuki_support h hc J A hJ hJC hthree hA hmove)

/-- Small conclusion for the alternatives assembly: avoid elaborating
the unused full-image intertwiner in its large disjunction. -/
private theorem seed_linearThree_of_starred_suzuki_support_of_many
    (D : ChosenModule T L V) (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hc : V ⊓ centralizer (L : Set G) = ⊥)
    (hm : V < componentOrbit V (T : Subgroup G)) :
    letI := D.normalizerOrbit_elementary h.toHypothesis1221
    let M := normalizer (L : Set G)
    let U := componentOrbit V M
    let hn := le_normalizer_componentOrbit V M
    let j := internalHom M U hn
    let ρ := UniqueFactor.imageRepresentation M U hn
    let K := (L.subgroupOf M).map j
    let C := centralizer (K : Set (internalActionImage M U hn))
    ∀ J A : Subgroup (internalActionImage M U hn),
      IsComponent (internalActionImage M U hn) J → J ≤ C → ¬ 3 ∣ Nat.card J →
      A ∈ QhatStar ρ → ⁅componentOrbit J A,A ⊓ C⁆ = componentOrbit J A →
      ∃ F : BinaryField, Odd F.degree ∧
        Nonempty (ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype) (linearNatural F 3)) := by
  let := D.normalizerOrbit_elementary h.toHypothesis1221
  dsimp only
  intro J A hJ hJC hthree hA hmove
  have hmodel := D.seed_constituentModel_of_moved_of_many h hmany hc hm
  obtain ⟨a,_⟩ := D.normalizer_component_actionEquiv_of_constituentModel h.toHypothesis1221 hmodel
  have hfive := D.normalizer_component_five_free_of_starred_suzuki_support
    h hc J A hJ hJC hthree hA hmove
  apply constituentModel_linearThree_of_five_free _ hmodel
  rwa [←Nat.card_congr a.groupEquiv.toEquiv]

/-- A commuting rank-one component leaves the original marked component
in the odd-degree natural SL₃ branch, using Theorem A on the literal layer. -/
theorem normalizer_linearThree_of_rank_one_support_of_many
    (D : ChosenModule T L V) (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hc : V ⊓ centralizer (L : Set G) = ⊥)
    (hm : V < componentOrbit V (T : Subgroup G)) :
    letI := D.normalizerOrbit_elementary h.toHypothesis1221
    let M := normalizer (L : Set G)
    let U := componentOrbit V M
    let hn := le_normalizer_componentOrbit V M
    let K := (L.subgroupOf M).map (internalHom M U hn)
    ∀ J : Subgroup (internalActionImage M U hn),
      IsComponent (internalActionImage M U hn) J → J ≤ centralizer (K : Set _) →
      primeRank 3 J = 1 →
      ∃ F : BinaryField, Odd F.degree ∧
        Nonempty (ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype) (linearNatural F 3)) := by
  let := D.normalizerOrbit_elementary h.toHypothesis1221
  let M := normalizer (L : Set G)
  let U := componentOrbit V M
  let hn := le_normalizer_componentOrbit V M
  let f := internalHom M U hn
  let K := (L.subgroupOf M).map f
  let : (L.subgroupOf M).Normal := normal_subgroupOf_of_le_normalizer le_rfl
  let : K.Normal := Normal.map inferInstance f
    (UniqueFactor.actionHom M U hn).rangeRestrict_surjective
  let := D.normalizer_component_quasisimple h.toHypothesis1221 hc
  have hK : IsComponent (internalActionImage M U hn) K :=
    ⟨(inferInstance : K.Normal).isSubnormal,inferInstance⟩
  dsimp only
  intro J hJ hJC hrJ
  have hr := component_three_rank_le_one_of_commuting_rank_one K J hK hJ
    ((D.normalizer_action_layer_sqtk h).stronglyQuasithin 3 Nat.prime_three (by decide)) hJC hrJ
  have hmodel := D.seed_constituentModel_of_moved_of_many h hmany hc hm
  obtain ⟨a,_⟩ := D.normalizer_component_actionEquiv_of_constituentModel h.toHypothesis1221 hmodel
  apply constituentModel_linearThree_of_three_rank_le_one _ hmodel
  rwa [←primeRank_congr 3 a.groupEquiv]

set_option maxHeartbeats 400000 in
/-- Both component-support branches force the same actual odd-degree
natural SL₃ seed. Otherwise the original starred actor offends on W or U/W.
The component and support witnesses remain available in the preceding
Suzuki-or-rank-one source alternative. -/
theorem exists_normalizer_odd_linearThree_or_section_offender_of_many
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
    let S := D.normalizerLocalSection h.toHypothesis1221
    ∃ A : Subgroup (internalActionImage M U hn),
      A ≤ internalSylow T M U hn D.sylow_normalizes_component ∧ A ∈ QhatStar ρ ∧
      ((∃ F : BinaryField, Odd F.degree ∧
          Nonempty (ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype)
            (linearNatural F 3))) ∨
        (IsOffender (imageRepresentation S.toRepresentation)
          (actionSubgroup S.toRepresentation (A.subgroupOf D.normalizerLocalActor)) ∨
        IsOffender (imageRepresentation S.quotientRepresentation)
          (actionSubgroup S.quotientRepresentation (A.subgroupOf D.normalizerLocalActor)))) := by
  let := D.normalizerOrbit_elementary h.toHypothesis1221
  obtain ⟨A,hAS,hA,hcase⟩ :=
    D.exists_normalizer_moved_suzuki_or_rank_one_component_or_section_offender_of_many
      h hmany hc hm hne
  refine ⟨A,hAS,hA,?_⟩
  rcases hcase with ⟨X,_,_,_,hXB,J,hJ,hJC,hX,hcases⟩ | hff
  · apply Or.inl
    rcases hcases with ⟨hthree,_,_⟩ | ⟨_,_,hrJ,_⟩
    · exact D.seed_linearThree_of_starred_suzuki_support_of_many h hmany hc hm
        J A hJ hJC hthree hA (by simpa only [←hX] using hXB)
    · exact D.normalizer_linearThree_of_rank_one_support_of_many h hmany hc hm J hJ hJC hrJ
  · exact Or.inr hff

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
