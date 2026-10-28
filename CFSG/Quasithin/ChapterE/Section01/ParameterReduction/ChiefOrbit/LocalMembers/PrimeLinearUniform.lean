module
public import CFSG.Quasithin.ChapterE.Section01.ParameterReduction.ChiefOrbit.LocalMembers.PrimeLinearEscape
public import CFSG.Quasithin.ChapterE.Section02.Structure.OddLinearTwo.SameActor.Uniform
/-!
# The full original rank-two stabilizer escape for paired odd PSL₂

The genuine prime-field theorem now covers both inner and outer actors,
including p=7. The component automizer source constructs its prescribed
Sylow and maximal subgroup. The same Star-to-core-action equivalence retains
the original actor, so cardinality four is measured in the actual
pCoreJoinAction image. The full preimage gives a literal local odd E-member;
its original component orbit escapes the proposed generation target.
Source: Aschbacher–Smith E.1.11 and paired E.2.2, pp.213–216.
-/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.ChiefOrbit
variable {G : Type*} [Group G] [Finite G]
theorem prime_local_odd_escape
    (hG : IsStronglyQuasithin G) (T : Sylow 2 G)
    (hP : ChapterB.IsMinimalParabolicOver T ⊤) {K : Subgroup G}
    (hK : IsComponent G K) [IsSimpleGroup K] (hgen : K ⊔ (T : Subgroup G) = ⊤)
    {p : ℕ} [Fact p.Prime] (hp : 7 ≤ p) (hop : Odd p)
    (hm : ClassicalGroup.IsPSL K 2 p)
    (A : Subgroup G) [IsElementaryAbelian 2 A] (hAT : A ≤ (T : Subgroup G))
    (hfour : Nat.card ((A.subgroupOf (localGroup T K)).map
      (pCoreJoinAction 2 (show stabilizer T K ≤ normalizer K from inf_le_right))) = 4) :
    ∃ P : Subgroup (localGroup T K),
      IsEMemberAt 1 ((stabilizer T K).subgroupOf (localGroup T K))
        (A.subgroupOf (localGroup T K)) P ∧
      ECaseOdd (A.subgroupOf (localGroup T K)) P ∧
      ¬ P.map (localGroup T K).subtype ≤ ChapterB.minimalParabolicMax T hP := by
  let := hK.2
  have hzc : center K = ⊥ := by
    rcases (inferInstance : (center K).Normal).eq_bot_or_eq_top with hh|hh
    · exact hh
    · exact (Group.IsPerfect.not_isMulCommutative K (center_eq_top_iff.mp hh)).elim
  have ho := Structure.generating_component_orbit_eq_residual hG T hK hgen
  have hc : pCore 2 K = ⊥ := bot_unique ((IsQuasisimple.pCore_le_center 2).trans hzc.le)
  let ek : K ≃* NormalizerAction.componentImage K :=
    NormalizerAction.componentEquivOfCenterEqBot K hzc
  have hz : center (K ⧸ pCore 2 K) = ⊥ := by
    let e : (K ⧸ pCore 2 K) ≃* K := (QuotientGroup.quotientMulEquivOfEq hc).trans QuotientGroup.quotientBot
    apply bot_unique
    intro x hx
    have he : e x ∈ center K := (centerCongr e ⟨x,hx⟩).property
    rw [hzc,mem_bot] at he
    exact mem_bot.mpr (e.injective (he.trans e.map_one.symm))
  have hStarFour : Nat.card ((A.subgroupOf (localGroup T K)).map
      (componentLocalQuotient (T : Subgroup G) K)) = 4 := by
    let e := componentCoreActionEquiv T hK ho hc
    let B := A.subgroupOf (localGroup T K)
    let ρ : localGroup T K →* MulAut (K ⧸ pCore 2 K) := pCoreJoinAction 2 (show stabilizer T K ≤ normalizer K from inf_le_right)
    calc
      Nat.card (B.map (componentLocalQuotient (T : Subgroup G) K)) =
          Nat.card ((B.map (componentLocalQuotient (T : Subgroup G) K)).map e.toMonoidHom) :=
        (card_map_of_injective e.injective).symm
      _ = Nat.card (B.map ρ.rangeRestrict) :=
        congrArg (fun X : Subgroup ρ.range => Nat.card X) (componentCoreActionEquiv_map T hK ho hc B)
      _ = Nat.card ((B.map ρ.rangeRestrict).map ρ.range.subtype) :=
        (card_map_of_injective ρ.range.subtype_injective).symm
      _ = Nat.card (B.map ρ) := by rw [map_map];rfl
      _ = 4 := hfour
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
  let : Nontrivial B := Finite.one_lt_card_iff_nontrivial.mp (by rw [hStarFour]; decide)
  have hB : IsKleinFour B := ⟨hStarFour,IsElementaryAbelian.exponent_eq_prime⟩
  have hBS : B ≤ (S : Subgroup _) := by
    rw [hS,componentLocalQuotient_stabilizer_image]
    apply map_mono
    intro x hx
    exact ⟨hAT hx,(sup_le K.le_normalizer inf_le_right) x.property⟩
  have hDs : NormalizerAction.componentImage K ⊔ (S : Subgroup _) = ⊤ := by
    rw [hS]
    exact component_automizer_sylow_supplement T hK ho
  obtain ⟨F,hF,hfin,hcard,⟨e⟩⟩ := hm
  exact Structure.prime_actor_odd_escape S hPs (NormalizerAction.componentImage K)
    hDs hop hcard hp (ek.symm.trans e)
    (NormalizerAction.centralizer_componentImage_eq_bot K hzc) B hB hBS
/-- The original elementary family consumes the same original stabilizer actor;
no rank-drop or generic actor-transfer assertion is used. -/
theorem not_confined_of_prime_stabilizer
    (hG : IsStronglyQuasithin G) (T : Sylow 2 G)
    (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    {K A : Subgroup G} (hK : IsComponent G K) [IsSimpleGroup K]
    (hgen : K ⊔ (T : Subgroup G) = ⊤)
    (hcore : pCore 2 G = ⊥)
    (hX : ChiefFactor.IsChief (pResidual 2 G) ⊥)
    (hna : ¬ IsMulCommutative (pResidual 2 G))
    (hKin : IsComponentIn K (pResidual 2 G))
    {p : ℕ} [Fact p.Prime] (hp : 7 ≤ p) (hop : Odd p)
    (hm : ClassicalGroup.IsPSL K 2 p)
    {Ω : Set (Subgroup G)} (hΩ : IsElementaryFamily Ω)
    (hA : A ∈ Ω) (hAT : A ≤ (T : Subgroup G))
    (hfour : Nat.card ((A.subgroupOf (localGroup T K)).map
      (pCoreJoinAction 2 (show stabilizer T K ≤ normalizer K from inf_le_right))) = 4) :
    ¬ generationTarget 1 T Ω ≤ ChapterB.minimalParabolicMax T hP := by
  let : IsElementaryAbelian 2 A := hΩ.1 A hA
  obtain ⟨P,hPm,ho,hPM⟩ := prime_local_odd_escape hG T hP hK hgen hp hop hm
    A hAT hfour
  exact fun h => hPM ((local_member_le_generationTarget_of_odd (by decide) T hΩ
    hcore hX hna hKin hA hAT hPm ho).trans h)
end CFSG.Quasithin.ChapterE.ChiefOrbit
