module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.SeedAlternativesMovedExhaustionCentralizerThree
public import CFSG.Quasithin.Chapter3.Section02.ChosenSource325.MovedExhaustionThreeModels
public import CFSG.Quasithin.Chapter3.Section02.ChosenSource325.MovedExhaustionThreeExclusion

/-!
# Excluding the three-core branch on the literal normalizer orbit

The source constituent models have characteristic seed-action kernel in L.
Thus the original image K of L on U = componentOrbit V (normalizer L)
is identified with the same faithful seed model, with the original map from
L retained. Three-rank at most one leaves the natural SL₃ model over a binary
field of odd degree. An explicit inverted three-subgroup in that model and
the ambient rank-two cover force three-rank at most one in C(K).

The three-core of C(K) is cyclic. Its selected order-three subgroup X is
therefore normal in the whole faithful image. D.2.13 gives a centralizing
hyperplane whose X-moved fixed space has dimension two. But the original
starred actor stabilizes the two complementary isotypic components, each of
which contributes at least two dimensions. This excludes the three-core
branch under the original multiple-overgroup standing guard and U > W.

The concluding application leaves only the component orbit in C(K) or an
FF offender on the actual W or U/W section. Those exclusions, U = W and
Source325 assembly remain with qt-baumann-fsu. The SL₃ central cover and
separate A₇ constituent are preserved throughout the model argument.
Source: Aschbacher--Smith D.2.13(5), D.3.10--17 and3.2.5,
printed pp.184--185,201--203 and580.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Representation.BinaryOffender.Homogeneous
open scoped IsMulCommutative
open CFSG.Quasithin.ChapterD

namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter3.Section02.ChosenSource325 ChapterB.QuasisimpleSource
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- Each marked constituent model makes the literal seed-action kernel
characteristic in the original component L, retaining the SL₃ center. -/
theorem componentHom_kernel_characteristic_of_constituentModel
    (D : ChosenModule T L V) (hq : IsQuasisimple (L ⧸ pCore 2 L))
    (hmodel : ConstituentModel (D.seedRepresentation.comp D.componentImage.subtype)) :
    D.componentHom.ker.Characteristic := by
  rcases hmodel with hm | hm | hm | hm | hm
  · obtain ⟨F,⟨e⟩⟩ := hm
    exact D.componentHom_kernel_characteristic_of_linearThree hq F e.groupEquiv
  · obtain ⟨F,_,⟨e⟩⟩ := hm
    exact D.componentHom_kernel_characteristic hq (center_eq_bot_of_model_equiv e.groupEquiv
      Theory.SpecificGroups.SymplecticFour.EvenProjective.center_eq_bot)
  · obtain ⟨e⟩ := hm
    exact D.componentHom_kernel_characteristic hq (center_eq_bot_of_model_equiv e.groupEquiv
      (alternatingGroup.center_eq_bot (by norm_num)))
  · obtain ⟨n,hn,⟨e⟩⟩ := hm
    exact D.componentHom_kernel_characteristic hq (center_eq_bot_of_model_equiv e.groupEquiv
      (BinaryLinear.OuterCyclic.binary_center_eq_bot (by omega)))
  · obtain ⟨σ,_,⟨e⟩⟩ := hm
    exact D.componentHom_kernel_characteristic hq (center_eq_bot_of_model_equiv e.groupEquiv
      (alternatingGroup.center_eq_bot (by norm_num)))

/-- The original component image on U has the same marked action on V
as its seed image. The equivalence commutes with the literal map from L. -/
theorem normalizer_component_actionEquiv_of_constituentModel
    (D : ChosenModule T L V) (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmodel : ConstituentModel (D.seedRepresentation.comp D.componentImage.subtype)) :
    letI := D.normalizerOrbit_elementary h
    let M := normalizer (L : Set G)
    let U := componentOrbit V M
    let hn := le_normalizer_componentOrbit V M
    let j := internalHom M U hn
    ∃ a : ActionEquiv (internalImageSubrepresentation hn D.normalizes).toRepresentation
      (D.seedRepresentation.comp D.componentImage.subtype),
      ∀ l : L, a.groupEquiv ((j.subgroupMap (L.subgroupOf M))
        ((subgroupOfEquivOfLe L.le_normalizer).symm l)) = D.componentHom l := by
  let := D.normalizerOrbit_elementary h
  let := D.elementary
  let τ := D.seedRepresentation.comp D.componentImage.subtype
  let e : ActionEquiv τ τ := ⟨MulEquiv.refl _,LinearEquiv.refl _ _,fun _ _ => rfl⟩
  let c := D.seedConjugationCoordinates τ e
  have hk := D.componentHom_kernel_characteristic_of_constituentModel h.quasisimple hmodel
  let : (e.groupEquiv.toMonoidHom.comp D.componentHom).ker.Characteristic :=
    characteristic_kernel_model_transport D.componentHom hk (MulEquiv.refl L) e.groupEquiv
  have hτ : Function.Injective τ :=
    (subspaceImageRepresentation_injective _ _).comp D.componentImage.subtype_injective
  exact internal_component_actionEquiv_of_characteristic_kernel c hτ
    (e.groupEquiv.surjective.comp D.componentHom_surjective)

/-- Three-rank one selects the odd-degree natural SL₃ constituent and
constructs its actual coordinates on the normalizer component image. -/
theorem normalizer_linearThree_of_rank_one_of_many
    (D : ChosenModule T L V) (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hc : V ⊓ centralizer (L : Set G) = ⊥)
    (hm : V < componentOrbit V (T : Subgroup G))
    (hr : primeRank 3 ((L.subgroupOf (normalizer (L : Set G))).map
      (internalHom (normalizer (L : Set G))
        (componentOrbit V (normalizer (L : Set G))) (le_normalizer_componentOrbit _ _))) ≤ 1) :
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
  have hr' : primeRank 3 D.componentImage ≤ 1 := by
    rwa [←primeRank_congr 3 a.groupEquiv]
  have hlinear := constituentModel_linearThree_of_three_rank_le_one
    (D.seedRepresentation.comp D.componentImage.subtype) hmodel hr'
  let F := Classical.choose hlinear
  have ho := (Classical.choose_spec hlinear).1
  let e := Classical.choice (Classical.choose_spec hlinear).2
  let b : ActionEquiv (internalImageSubrepresentation
      (le_normalizer_componentOrbit V (normalizer (L : Set G))) D.normalizes).toRepresentation
      (linearNatural F 3) :=
    ⟨a.groupEquiv.trans e.groupEquiv, a.linearEquiv.trans e.linearEquiv, by
      intro k v
      exact (congrArg e.linearEquiv (a.intertwines k v)).trans
        (e.intertwines (a.groupEquiv k) (a.linearEquiv v))⟩
  refine ⟨F,ho,e,b,?_⟩
  intro l
  exact congrArg e.groupEquiv (ha l)

end CFSG.Quasithin.Chapter12.Section02.ChosenModule

namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter3.Section02.ChosenSource325 ChapterB.QuasisimpleSource
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- In the three-rank-one component branch, the marked SL₃ model bounds
the literal component centralizer using the original strongly quasithin cover. -/
theorem normalizer_component_centralizer_three_rank_le_one_of_many
    (D : ChosenModule T L V) (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hc : V ⊓ centralizer (L : Set G) = ⊥)
    (hm : V < componentOrbit V (T : Subgroup G))
    (hr : primeRank 3 ((L.subgroupOf (normalizer (L : Set G))).map
      (internalHom (normalizer (L : Set G))
        (componentOrbit V (normalizer (L : Set G))) (le_normalizer_componentOrbit _ _))) ≤ 1) :
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
  obtain ⟨F,_,_,a,_⟩ := D.normalizer_linearThree_of_rank_one_of_many h hmany hc hm hr
  have hu := Chapter1.Section02.nonsolvable_uniqueness_of_theoremsAC
    (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
    (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X))
    h.simpleQTKE T h.maximal_faithful.1
  have hmax : IsMaximalTwoLocal M := by
    simpa only [D.localOrbit_eq] using hu.normalizer_maximal
  have hM : primeRank 3 M ≤ 2 :=
    (h.simpleQTKE.twoLocal_sqtk hmax.1).stronglyQuasithin 3 Nat.prime_three (by decide)
  exact component_centralizer_three_rank_le_one_of_linearThree f
    (UniqueFactor.actionHom M U hn).rangeRestrict_surjective hM K F a.groupEquiv
end CFSG.Quasithin.Chapter12.Section02.ChosenModule


namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter3.Section02.ChosenSource325 ChapterB.QuasisimpleSource ChapterD
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- Under the actual moved-seed hypotheses, the normal three-core branch
is impossible. Only a component in the centralizer or an actual section
FF offender survives the assumed strict enlargement of the normalizer orbit. -/
theorem exists_normalizer_component_or_section_offender_of_many
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
            IsComponent (internalActionImage M U hn) J ∧ J ≤ C ∧ X = componentOrbit J A) ∨
        (IsOffender (imageRepresentation S.toRepresentation)
          (actionSubgroup S.toRepresentation (A.subgroupOf D.normalizerLocalActor)) ∨
        IsOffender (imageRepresentation S.quotientRepresentation)
          (actionSubgroup S.quotientRepresentation (A.subgroupOf D.normalizerLocalActor)))) := by
  let := D.normalizerOrbit_elementary h.toHypothesis1221
  let M := normalizer (L : Set G)
  let U := componentOrbit V M
  let hn := le_normalizer_componentOrbit V M
  let ρ := UniqueFactor.imageRepresentation M U hn
  let f := internalHom M U hn
  let K := (L.subgroupOf M).map f
  let C := centralizer (K : Set (internalActionImage M U hn))
  let I := (typePart (internalSubrepresentation hn D.normalizes)).toSubmodule
  let : (L.subgroupOf M).Normal := normal_subgroupOf_of_le_normalizer le_rfl
  let : K.Normal := Normal.map inferInstance f
    (UniqueFactor.actionHom M U hn).rangeRestrict_surjective
  obtain ⟨A,hAS,hA,hcase⟩ :=
    D.exists_normalizer_three_or_component_or_section_offender_of_many h hmany hc hne
  refine ⟨A,hAS,hA,?_⟩
  rcases hcase with ⟨X,hXC,hAX,hXn,hXB,hcase⟩ | hff
  · rcases hcase with ⟨hXP,hXcard,hKr,hpos,hproper,rest⟩ | hcomp
    · have hCr := D.normalizer_component_centralizer_three_rank_le_one_of_many h hmany hc hm hKr
      let : X.Normal := normal_of_le_three_core_centralizer_rank_one K hCr X hXP
      let := D.normalizer_component_quasisimple h.toHypothesis1221 hc
      have hXcore : X ≤ pCore 3 (internalActionImage M U hn) := hXP.trans
        (le_sSup ⟨inferInstance,pCore_isPGroup.map C.subtype⟩)
      have hXA : ⁅X,A⁆ = X := le_antisymm
        (le_normalizer_iff_commutator_le_left.mp hAX)
        (hXB.symm.le.trans (commutator_mono le_rfl inf_le_left))
      have hrne : rank A ≠ 1 := fun hr => (ne_of_gt hpos)
        (rank_one_starred_component_centralizer_eq_bot ρ
          (UniqueFactor.imageRepresentation_injective M U hn) K
          (D.normalizer_component_fully_moved h.toHypothesis1221 hc) hA hr)
      have hr : 1 < rank A := by have := hA.1.2.1.rank_pos; omega
      obtain ⟨t,_,_,hcompl,_,hdim,hperm,_⟩ :=
        D.normalizer_starred_isotypic_pair_of_moved_of_many h hmany hc hm hne
      have hneq : I ≠ I.map (ρ (f t)) := by
        intro he
        have hd : Disjoint I (I.map (ρ (f t))) := hcompl.disjoint
        rw [←he] at hd
        have hz : I = ⊥ := disjoint_self.mp hd
        change 2 < Module.finrank (ZMod 2) I at hdim
        rw [hz,finrank_bot] at hdim
        omega
      exact (no_normal_three_support_on_stable_pair ρ
        (UniqueFactor.imageRepresentation_injective M U hn) hA hr X hXcard hXcore hXA
        I (f t) hcompl hneq hperm
        (D.normalizer_starred_stabilizes_isotypic_of_moved_of_many h hmany hc hm hne A hAS hA)).elim
    · exact Or.inl ⟨X,hXC,hAX,hXn,hXB,hcomp⟩
  · exact Or.inr hff

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
