module
public import Theory.GroupTheory.GeneralizedFitting.ComponentLocalAction
public import CFSG.Quasithin.ChapterE.Section01.ParameterReduction.ChiefOrbit.LocalMembers.OddActionLift
public import CFSG.Quasithin.ChapterE.Section02.Structure.ComponentAutomizerSQTK
public import CFSG.Quasithin.ChapterE.Section02.Structure.OddLinearTwo.SameActor
/-!
# Odd witnesses on the original component stabilizer

The faithful normalizer quotient is identified with the literal core-quotient
conjugation image. The equivalence preserves the prescribed Sylow, the same
elementary actor and the image of the actual maximal overgroup. A marked odd
witness therefore lifts to its full preimage and then to the original
component-orbit generation target.

For a prime-field PSL₂ component and an inner four-group actor, the genuine
minimal-parabolic involution-centralizer geometry constructs that marked
witness. The outer actor and prime-seven branches remain separate.
Source: Aschbacher–Smith E.1.11 and E.2.2, printed pp.213–216.
-/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.ChiefOrbit
variable {G : Type*} [Group G] [Finite G]

theorem local_odd_escape_of_marked_star (T : Sylow 2 G) {K A M : Subgroup G}
    (hK : IsComponent G K) (ho : componentOrbit K (T : Subgroup G) = pResidual 2 G)
    (hc : pCore 2 K = ⊥) (hz : center (K ⧸ pCore 2 K) = ⊥)
    [IsElementaryAbelian 2 A] (hAT : A ≤ (T : Subgroup G))
    (S : Sylow 2 (NormalizerAction.Star K))
    (hS : (S : Subgroup (NormalizerAction.Star K)) =
      ((T : Subgroup G).subgroupOf (normalizer K)).map (NormalizerAction.quotient K))
    (N : Subgroup (NormalizerAction.Star K))
    (hN : (M.subgroupOf (normalizer K)).map (NormalizerAction.quotient K) ≤ N)
    (he : ∃ I : Subgroup (NormalizerAction.Star K),
      IsEMemberAt 1 (S : Subgroup _) ((A.subgroupOf (localGroup T K)).map
        (componentLocalQuotient (T : Subgroup G) K)) I ∧
      ECaseOdd ((A.subgroupOf (localGroup T K)).map
        (componentLocalQuotient (T : Subgroup G) K)) I ∧ ¬ I ≤ N) :
    ∃ P : Subgroup (localGroup T K),
      IsEMemberAt 1 ((stabilizer T K).subgroupOf (localGroup T K))
        (A.subgroupOf (localGroup T K)) P ∧
      ECaseOdd (A.subgroupOf (localGroup T K)) P ∧ ¬ P.map (localGroup T K).subtype ≤ M := by
  let e := componentCoreActionEquiv T hK ho hc
  apply exists_local_odd_escape_of_action T hK.1 hz hAT
  obtain ⟨I,hI,hodd,hIM⟩ := he
  have hsmap : (S : Subgroup _).map e.toMonoidHom =
      ((stabilizer T K).subgroupOf (localGroup T K)).map
        (pCoreJoinAction 2 (show stabilizer T K ≤ normalizer K from inf_le_right)).rangeRestrict := by
    rw [hS,componentLocalQuotient_stabilizer_image]
    exact componentCoreActionEquiv_map T hK ho hc _
  have hamap := componentCoreActionEquiv_map T hK ho hc (A.subgroupOf (localGroup T K))
  refine ⟨I.map e.toMonoidHom,?_,?_,?_⟩
  · have hm := hI.map_equiv e
    rw [hsmap,hamap] at hm
    exact hm
  · have hm := hodd.map_injective e.toMonoidHom e.injective
    rw [hamap] at hm
    exact hm
  · intro hi
    apply hIM
    apply le_trans _ hN
    apply (map_le_map_iff_of_injective (f := e.toMonoidHom) e.injective).mp
    apply hi.trans
    have hm := map_mono (f := e.toMonoidHom)
      (componentLocalQuotient_overgroup_image_le (T : Subgroup G) K M)
    rw [componentCoreActionEquiv_map T hK ho hc] at hm
    exact hm

omit [Finite G] in
private theorem simple_component_center {K : Subgroup G}
    (hK : IsComponent G K) [IsSimpleGroup K] : center K = ⊥ := by
  let := hK.2
  rcases (inferInstance : (center K).Normal).eq_bot_or_eq_top with h | h
  · exact h
  · exact (Group.IsPerfect.not_isMulCommutative K (center_eq_top_iff.mp h)).elim

theorem prime_inner_local_odd_escape
    (hG : IsStronglyQuasithin G) (T : Sylow 2 G)
    (hP : ChapterB.IsMinimalParabolicOver T ⊤) {K : Subgroup G}
    (hK : IsComponent G K) [IsSimpleGroup K] (hgen : K ⊔ (T : Subgroup G) = ⊤)
    {p : ℕ} [Fact p.Prime] (hp : 9 < p) (hop : Odd p)
    (hm : ClassicalGroup.IsPSL K 2 p)
    (A : Subgroup G) [IsElementaryAbelian 2 A] (hAT : A ≤ (T : Subgroup G))
    (hfour : Nat.card ((A.subgroupOf (localGroup T K)).map
      (componentLocalQuotient (T : Subgroup G) K)) = 4)
    (hinner : ((A.subgroupOf (localGroup T K)).map
      (componentLocalQuotient (T : Subgroup G) K)) ≤ NormalizerAction.componentImage K) :
    ∃ P : Subgroup (localGroup T K),
      IsEMemberAt 1 ((stabilizer T K).subgroupOf (localGroup T K))
        (A.subgroupOf (localGroup T K)) P ∧
      ECaseOdd (A.subgroupOf (localGroup T K)) P ∧
      ¬ P.map (localGroup T K).subtype ≤ ChapterB.minimalParabolicMax T hP := by
  let := hK.2
  have ho := Structure.generating_component_orbit_eq_residual hG T hK hgen
  have hc : pCore 2 K = ⊥ := bot_unique ((IsQuasisimple.pCore_le_center 2).trans (simple_component_center hK).le)
  let ek : K ≃* NormalizerAction.componentImage K :=
    NormalizerAction.componentEquivOfCenterEqBot K (simple_component_center hK)
  have hz : center (K ⧸ pCore 2 K) = ⊥ := by
    let e : (K ⧸ pCore 2 K) ≃* K := (QuotientGroup.quotientMulEquivOfEq hc).trans QuotientGroup.quotientBot
    apply bot_unique
    intro x hx
    have he : e x ∈ center K := (centerCongr e ⟨x,hx⟩).property
    rw [simple_component_center hK,mem_bot] at he
    exact mem_bot.mpr (e.injective (he.trans e.map_one.symm))
  obtain ⟨S,hS,hPs,hM⟩ := Structure.source_component_automizer hG T hP hK hgen
  apply local_odd_escape_of_marked_star T hK ho hc hz hAT S hS
    (ChapterB.minimalParabolicMax S hPs) hM.symm.le
  let B := (A.subgroupOf (localGroup T K)).map (componentLocalQuotient (T : Subgroup G) K)
  let : IsElementaryAbelian 2 (A.subgroupOf (localGroup T K)) := {
    toIsMulCommutative := Subgroup.subgroupOf_isMulCommutative (localGroup T K) A
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (fun a =>
      Subtype.ext (Subtype.ext (elemPow_eq_one_of_isElementaryAbelian (A:=A) _ a.property))) }
  let : IsElementaryAbelian 2 B :=
    IsElementaryAbelian.map (A := A.subgroupOf (localGroup T K))
      (componentLocalQuotient (T : Subgroup G) K)
  let : Nontrivial B := Finite.one_lt_card_iff_nontrivial.mp (by rw [hfour]; decide)
  have hB : IsKleinFour B := ⟨hfour,IsElementaryAbelian.exponent_eq_prime⟩
  have hBS : B ≤ (S : Subgroup _) := by
    rw [hS,componentLocalQuotient_stabilizer_image]
    apply map_mono
    intro x hx
    exact ⟨hAT hx,(sup_le K.le_normalizer inf_le_right) x.property⟩
  have hDs : NormalizerAction.componentImage K ⊔ (S : Subgroup _) = ⊤ := by
    rw [hS]
    exact component_automizer_sylow_supplement T hK ho
  obtain ⟨F,hF,hfin,hcard,⟨e⟩⟩ := hm
  exact Structure.prime_inner_actor_odd_escape S hPs (NormalizerAction.componentImage K)
    hDs hop hcard hp (ek.symm.trans e)
    (NormalizerAction.centralizer_componentImage_eq_bot K (simple_component_center hK)) B hB hBS hinner
/-- The original elementary family consumes the same inner stabilizer actor;
no rank-drop or generic actor-transfer assertion is used. -/
theorem not_confined_of_prime_inner_stabilizer
    (hG : IsStronglyQuasithin G) (T : Sylow 2 G)
    (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    {K A : Subgroup G} (hK : IsComponent G K) [IsSimpleGroup K]
    (hgen : K ⊔ (T : Subgroup G) = ⊤)
    (hcore : pCore 2 G = ⊥)
    (hX : ChiefFactor.IsChief (pResidual 2 G) ⊥)
    (hna : ¬ IsMulCommutative (pResidual 2 G))
    (hKin : IsComponentIn K (pResidual 2 G))
    {p : ℕ} [Fact p.Prime] (hp : 9 < p) (hop : Odd p)
    (hm : ClassicalGroup.IsPSL K 2 p)
    {Ω : Set (Subgroup G)} (hΩ : IsElementaryFamily Ω)
    (hA : A ∈ Ω) (hAT : A ≤ (T : Subgroup G))
    (hfour : Nat.card ((A.subgroupOf (localGroup T K)).map
      (componentLocalQuotient (T : Subgroup G) K)) = 4)
    (hinner : ((A.subgroupOf (localGroup T K)).map
      (componentLocalQuotient (T : Subgroup G) K)) ≤ NormalizerAction.componentImage K) :
    ¬ generationTarget 1 T Ω ≤ ChapterB.minimalParabolicMax T hP := by
  let : IsElementaryAbelian 2 A := hΩ.1 A hA
  obtain ⟨P,hPm,ho,hPM⟩ := prime_inner_local_odd_escape hG T hP hK hgen hp hop hm
    A hAT hfour hinner
  exact fun h => hPM ((local_member_le_generationTarget_of_odd (by decide) T hΩ
    hcore hX hna hKin hA hAT hPm ho).trans h)
end CFSG.Quasithin.ChapterE.ChiefOrbit
