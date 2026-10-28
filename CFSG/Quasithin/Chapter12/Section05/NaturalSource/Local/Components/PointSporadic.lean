module
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.Local.Components.PointSmallModels
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.Local.Components.Seven
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.AutomorphismNormalizerIndex
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.AutomorphismPointStabilizers
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.ThreeRank
public import Theory.SpecificGroups.Rudvalis.ComponentFacts
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.RudvalisOddRank
public import Theory.SpecificGroups.Rudvalis.Model.Order
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.ThreeRank
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.OuterTwoGroup
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.OrdinaryLocal
public import Theory.Mathieu.M11.Properties.Order
public import Theory.Mathieu.M12.Properties.Order
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.SylowOvergroups.CubicOrder
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.SylowOvergroups.SevenOrder

/-!
# Five sporadic exclusions in the original point-component sieve

For HS, Ru and J2, cubic rank and the outer two-group put the actual
Y = O³′(P) inside the normal point component. The literal M₁* intersection
therefore has full-Sylow index 63. In HS and Ru every proper full-Sylow
overgroup has order indivisible by nine; in J2 its order is prime to seven.
The full groups are excluded by their factor five. Ru simplicity is inherited
from the original component after its order excludes the E₄₉ radical row.
The original seven-section also excludes both M11 and M12.

The final catalogue reduction retains actual quotient isomorphisms and
leaves M22, M23 and He explicit, alongside the permitted M24 and J4 rows.
PointCore.PointSporadic constructs LocalComponents and the literal point-core
and fusion consumers in the covered rows. The remaining sporadic, odd ternary
and central-cover cases, general normalizers and quasisimple escape remain
with qt-d-1251-local; final exterior assembly belongs to qt-d-1251-source.
Source: Aschbacher--Smith 12.5.3, pp.817--818, using A.3.12 and A.3.18.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter12.Section05.NaturalSource
open Section02

private theorem no_sixtyThree_index_of_proper_bound
    {A : Type*} [Group A] [Finite A] (hf : 5 ∣ Nat.card A)
    (hn : ∀ (S : Sylow 2 A) (J : Subgroup A), (S : Subgroup A) ≤ J → J ≠ ⊤ →
      ¬ 63 ∣ Nat.card J)
    (S : Sylow 2 A) (J : Subgroup A) (hSJ : (S : Subgroup A) ≤ J)
    (hi : (S : Subgroup A).relIndex J = 63) : False := by
  have hj : J ≠ ⊤ := by
    intro he
    have hsi : (S : Subgroup A).index = 63 := by simpa only [he,relIndex_top_right] using hi
    have hcop : Nat.Coprime 5 (Nat.card S) := by
      obtain ⟨n,hn⟩ := S.isPGroup'.exists_card_eq
      rw [hn]
      exact (by decide : Nat.Coprime 5 2).pow_right n
    have hd : 5 ∣ 63 := by
      rw [← (S : Subgroup A).card_mul_index] at hf
      exact hsi ▸ hcop.dvd_of_dvd_mul_left hf
    norm_num at hd
  apply hn S J hSJ hj
  exact hi ▸ relIndex_dvd_card (S : Subgroup A) J

private theorem ru_proper_overgroup_not_nine
    (hO : pCore 2 Rudvalis.Model = ⊥)
    (S : Sylow 2 Rudvalis.Model) (D : Subgroup Rudvalis.Model)
    (hSD : (S : Subgroup _) ≤ D) (hD : D ≠ ⊤) : ¬ 9 ∣ Nat.card D := by
  obtain ⟨M,hM,hDM⟩ := (eq_top_or_exists_le_coatom D).resolve_left hD
  have hodd : ¬ 2 ∣ M.index := fun hd =>
    S.not_dvd_index (hd.trans (index_dvd_of_le (hSD.trans hDM)))
  have hcover := Rudvalis.SylowOvergroups.oddIndexMaximalCover_of_twoCore_of_radicalCover hO
    Chapter1.XiEmbedding.InvariantThree.SporadicRemaining.rudvalis_oddIndexMaximalTwoCore
    Rudvalis.SylowOvergroups.oddIndexMaximalRadicalCover
  intro hd
  have hdM := hd.trans (card_dvd_of_le hDM)
  rcases hcover M hM hodd with he | he
  all_goals obtain ⟨e⟩ := he
  · rw [Nat.card_congr e.toEquiv] at hdM
    exact Rudvalis.SylowOvergroups.not_nine_dvd_max4_card hdM
  · rw [Nat.card_congr e.toEquiv] at hdM
    exact Rudvalis.SylowOvergroups.not_nine_dvd_max6_card hdM

universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {D : ChosenModule T L V}
namespace SylowExteriorMarking
variable (s : SylowExteriorMarking D)

/-- Cubic rank and a two-group outer action place the original first-node residual
in the normal point component, through its unchanged two-core quotient. -/
theorem Y_le_point_component_of_model
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) {K : Subgroup G}
    (hK : K ∈ Chapter1.cComponentsIn (s.marking.Gi 1))
    (hN : (K.subgroupOf (s.marking.Gi 1)).Normal)
    {X : Type*} [Group X] [Finite X] (e : (K ⧸ pCore 2 K) ≃* X)
    (hz : center X = ⊥) (hr : 2 ≤ primeRank 3 X) (ho : IsPGroup 2 (MulAut.Outer X)) :
    s.Y ≤ K := by
  let H := s.marking.Gi 1
  let C := K.subgroupOf H
  let a := subgroupOfEquivOfLe hK.1
  let b := (QuotientGroup.congr _ _ a (pCore_map_iso 2 a)).trans e
  have hzC : center (C ⧸ pCore 2 C) = ⊥ := by
    apply le_bot_iff.mp
    intro x hx
    have hh : b x = 1 := hz.le ((centerCongr b) ⟨x,hx⟩).property
    exact b.map_eq_one_iff.mp hh
  have hrC : 2 ≤ primeRank 3 (C ⧸ pCore 2 C) := by rwa [primeRank_congr 3 b]
  have hoC : IsPGroup 2 (MulAut.Outer (C ⧸ pCore 2 C)) :=
    ho.of_equiv (MulAut.outerCongr b).symm
  let : C.Normal := hN
  have hi : Nat.Coprime 3 C.index := by
    apply cComponent_index_coprime_three_of_quotient C hK.2 hzC hrC
      ((h.simpleQTKE.twoLocal_sqtk (s.marking.Gi_twoLocal 1 (.inl rfl))).stronglyQuasithin
        3 (by decide) (by decide))
    obtain ⟨k,hk⟩ := hoC.exists_card_dvd_pow
    exact ((show Nat.Coprime 3 2 by decide).pow_right k).coprime_dvd_right hk
  have hc : primeToResidual 3 H ≤ C := primeToResidual_le C hi
  rw [s.Y_eq_primeToThree]
  exact (embedded_primeToResidual_mono 3 (s.P_le_M₁.trans inf_le_right)).trans
    ((map_mono (f := H.subtype) hc).trans_eq (map_subgroupOf_eq_of_le hK.1))

private theorem point_component_impossible_of_sixtyThree_bound
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) {K : Subgroup G}
    (hK : K ∈ Chapter1.cComponentsIn (s.marking.Gi 1))
    (hLK : s.marking.Li 1 ≤ K) (hN : (K.subgroupOf (s.marking.Gi 1)).Normal)
    {X : Type*} [Group X] [Finite X] (e : (K ⧸ pCore 2 K) ≃* X)
    (hz : center X = ⊥) (hr : 2 ≤ primeRank 3 X) (ho : IsPGroup 2 (MulAut.Outer X))
    (hf : 5 ∣ Nat.card X)
    (hn : ∀ (S : Sylow 2 X) (J : Subgroup X), (S : Subgroup X) ≤ J → J ≠ ⊤ →
      ¬ 63 ∣ Nat.card J) : False := by
  have hY := s.Y_le_point_component_of_model h hK hN e hz hr ho
  obtain ⟨S,hS,hi⟩ := s.pointComponentParabolic_sylow_index hK.1 hN hLK hY
  let a := (s.pointComponentCoreEquivImage hK.1 hN).symm.trans e
  let R := S.mapSurjective (f := a.toMonoidHom) a.surjective
  let J := (s.pointComponentParabolic K).map a.toMonoidHom
  have hRJ : (R : Subgroup X) ≤ J := map_mono hS
  have hidx : (R : Subgroup X).relIndex J = 63 := by
    change ((S : Subgroup _).map a.toMonoidHom).relIndex
      ((s.pointComponentParabolic K).map a.toMonoidHom) = 63
    rw [relIndex_map_map_of_injective _ _ a.injective]
    exact hi
  exact no_sixtyThree_index_of_proper_bound hf hn R J hRJ hidx

/-- The actual Higman--Sims quotient is incompatible with the marked point parabolic. -/
theorem point_component_not_higmanSims
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) {K : Subgroup G}
    (hK : K ∈ Chapter1.cComponentsIn (s.marking.Gi 1))
    (hLK : s.marking.Li 1 ≤ K) (hN : (K.subgroupOf (s.marking.Gi 1)).Normal) :
    ¬ Nonempty ((K ⧸ pCore 2 K) ≃* Sporadic.LeechRelated.HS.Carrier) := by
  rintro ⟨e⟩
  exact s.point_component_impossible_of_sixtyThree_bound h hK hLK hN e
    Sporadic.LeechRelated.HS.BlockNormalizer.center_carrier_eq_bot
    Sporadic.LeechRelated.HS.ThreeRank.two_le_primeRank
    (Sporadic.LeechRelated.HS.outer_isPGroup_two_of_pointStabilizer_map
      Sporadic.LeechRelated.HS.pointStabilizer_map
      Sporadic.LeechRelated.HS.normalizer_relIndex_dvd_two_pow)
    (by rw [Sporadic.LeechRelated.HS.NormalizerIndex.card_carrier]; decide)
    (fun S J hSJ hn hd => Sporadic.LeechRelated.HS.SylowOvergroups.proper_overgroup_not_nine_dvd S J hSJ hn
      ((by decide : 9 ∣ 63).trans hd))

/-- A point component whose quotient order is not divisible by 49 is quasisimple. -/
theorem point_component_quasisimple_of_not_fortyNine
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) {K : Subgroup G}
    (hK : K ∈ Chapter1.cComponentsIn (s.marking.Gi 1)) (hLK : s.marking.Li 1 ≤ K)
    (hn : ¬ 49 ∣ Nat.card (K ⧸ pCore 2 K)) : IsQuasisimple (K ⧸ pCore 2 K) := by
  by_contra hq
  obtain ⟨⟨e⟩,_⟩ := s.local_component_nonquasisimple_seven_core h 1 (.inl rfl) hK hLK hq
  apply hn
  have hc : Nat.card (pCore 7 (K ⧸ pCore 2 K)) = 49 := by
    rw [Nat.card_congr e.toEquiv]
    simp
  exact hc ▸ (pCore 7 (K ⧸ pCore 2 K)).card_subgroup_dvd_card

/-- The Rudvalis quotient is excluded with simplicity inherited from the source component. -/
theorem point_component_not_rudvalis
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) {K : Subgroup G}
    (hK : K ∈ Chapter1.cComponentsIn (s.marking.Gi 1))
    (hLK : s.marking.Li 1 ≤ K) (hN : (K.subgroupOf (s.marking.Gi 1)).Normal) :
    ¬ Nonempty ((K ⧸ pCore 2 K) ≃* Rudvalis.Model) := by
  rintro ⟨e⟩
  let : IsQuasisimple (K ⧸ pCore 2 K) := s.point_component_quasisimple_of_not_fortyNine h hK hLK
    (by rw [Nat.card_congr e.toEquiv,Rudvalis.model_card]; decide)
  let : IsQuasisimple Rudvalis.Model := IsQuasisimple.of_mulEquiv e
  let : IsSimpleGroup (Rudvalis.Model ⧸ center Rudvalis.Model) := IsQuasisimple.simple
  let : IsSimpleGroup Rudvalis.Model :=
    ((QuotientGroup.quotientMulEquivOfEq Rudvalis.LowCentralizers.model_center_eq_bot).trans
      (QuotientGroup.quotientBot)).symm.isSimpleGroup
  have hO : pCore 2 Rudvalis.Model = ⊥ := bot_unique
    ((IsQuasisimple.pCore_le_center 2).trans_eq Rudvalis.LowCentralizers.model_center_eq_bot)
  exact s.point_component_impossible_of_sixtyThree_bound h hK hLK hN e
    Rudvalis.LowCentralizers.model_center_eq_bot Rudvalis.three_rank_ge_two
    Rudvalis.outer_isPGroup_two (by rw [Rudvalis.model_card]; decide)
    (fun S J hSJ hn hd => ru_proper_overgroup_not_nine hO S J hSJ hn
      ((by decide : 9 ∣ 63).trans hd))

/-- The Hall--Janko quotient cannot contain the original index-63 point parabolic. -/
theorem point_component_not_jankoTwo
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) {K : Subgroup G}
    (hK : K ∈ Chapter1.cComponentsIn (s.marking.Gi 1))
    (hLK : s.marking.Li 1 ≤ K) (hN : (K.subgroupOf (s.marking.Gi 1)).Normal) :
    ¬ Nonempty ((K ⧸ pCore 2 K) ≃* Sporadic.LeechRelated.J2.Carrier) := by
  rintro ⟨e⟩
  exact s.point_component_impossible_of_sixtyThree_bound h hK hLK hN e
    Sporadic.LeechRelated.J2.OrdinaryLocal.center_eq_bot
    Sporadic.LeechRelated.J2.three_rank_ge_two Sporadic.LeechRelated.J2.outer_isTwoGroup
    (by rw [Sporadic.LeechRelated.J2.ExceptionalParabolics.FirstParabolic.card_carrier]; decide)
    (fun S J hSJ hn hd => Sporadic.LeechRelated.J2.SylowOvergroups.proper_overgroup_not_seven_dvd S J hSJ hn
      ((by decide : 7 ∣ 63).trans hd))

private theorem seven_dvd_point_quotient {K : Subgroup G}
    (hLK : s.marking.Li 1 ≤ K) : 7 ∣ Nat.card (K ⧸ pCore 2 K) := by
  have hB : 7 ∣ Nat.card (s.marking.Li 1 ⧸ pCore 2 (s.marking.Li 1)) := by
    rw [Nat.card_congr (s.marking.LiCoreEquiv 1 (.inl rfl)).toEquiv]
    change 7 ∣ Nat.card SL(3,ZMod 2)
    rw [Atlas.Comparisons.Exceptional.sl3Two_card]
    decide
  have h7 : 7 ∣ Nat.card K := (hB.trans
    (pCore 2 (s.marking.Li 1)).card_quotient_dvd_card).trans (card_dvd_of_le hLK)
  have hc : Nat.Coprime 7 (Nat.card (pCore 2 K)) := by
    obtain ⟨k,hk⟩ := (pCore_isPGroup (p := 2) (G := K)).exists_card_dvd_pow
    exact ((show Nat.Coprime 7 2 by decide).pow_right k).coprime_dvd_right hk
  have he := (pCore 2 K).card_mul_index
  rw [index_eq_card] at he
  rw [←he] at h7
  exact hc.dvd_of_dvd_mul_left h7

/-- Both small Mathieu quotients are excluded by the original seven-section. -/
theorem point_component_not_small_mathieu {K : Subgroup G}
    (hLK : s.marking.Li 1 ≤ K) :
    ¬ (Nonempty ((K ⧸ pCore 2 K) ≃* Sporadic.Mathieu.M11) ∨
      Nonempty ((K ⧸ pCore 2 K) ≃* Sporadic.Mathieu.M12)) := by
  intro hm
  have hd := s.seven_dvd_point_quotient hLK
  rcases hm with hm | hm
  all_goals obtain ⟨e⟩ := hm
  · rw [Nat.card_congr e.toEquiv,Sporadic.Mathieu.m11_order] at hd
    norm_num at hd
  · rw [Nat.card_congr e.toEquiv,Sporadic.Mathieu.m12_order] at hd
    norm_num at hd

/-- Five forbidden sporadic rows are removed from the literal Theorem C catalogue. -/
theorem point_sporadic_model_remaining
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) {K : Subgroup G}
    (hK : K ∈ Chapter1.cComponentsIn (s.marking.Gi 1))
    (hLK : s.marking.Li 1 ≤ K) (hN : (K.subgroupOf (s.marking.Gi 1)).Normal)
    (name : ClassificationModels.SporadicName) (hj : name ≠ .j3)
    (hm : Nonempty ((K ⧸ pCore 2 K) ≃* name.Carrier)) :
    name = .m22 ∨ name = .m23 ∨ name = .m24 ∨ name = .j4 ∨ name = .he := by
  cases name with
  | m11 => exact (s.point_component_not_small_mathieu hLK (.inl hm)).elim
  | m12 => exact (s.point_component_not_small_mathieu hLK (.inr hm)).elim
  | m22 => exact .inl rfl
  | m23 => exact .inr (.inl rfl)
  | m24 => exact .inr (.inr (.inl rfl))
  | j2 => exact (s.point_component_not_jankoTwo h hK hLK hN hm).elim
  | j3 => exact (hj rfl).elim
  | j4 => exact .inr (.inr (.inr (.inl rfl)))
  | hs => exact (s.point_component_not_higmanSims h hK hLK hN hm).elim
  | he => exact .inr (.inr (.inr (.inr rfl)))
  | ru => exact (s.point_component_not_rudvalis h hK hLK hN hm).elim

/-- The covered sporadic point rows give the complete source alternative,
including containment of the original first-node residual. -/
theorem local_point_component_alternative_of_sporadic_sieve
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) {K : Subgroup G}
    (hK : K ∈ Chapter1.cComponentsIn (s.marking.Gi 1))
    (hLK : s.marking.Li 1 ≤ K) (hN : (K.subgroupOf (s.marking.Gi 1)).Normal)
    (name : ClassificationModels.SporadicName) (hj : name ≠ .j3)
    (h22 : name ≠ .m22) (h23 : name ≠ .m23) (hHe : name ≠ .he)
    (hm : Nonempty ((K ⧸ pCore 2 K) ≃* name.Carrier)) :
    LocalComponentAlternative s 1 K := by
  rcases s.point_sporadic_model_remaining h hK hLK hN name hj hm with he | he | he | he | he
  · exact (h22 he).elim
  · exact (h23 he).elim
  · subst name
    exact s.local_point_component_large_alternative h hK hN (.inr (.inl hm))
  · subst name
    exact s.local_point_component_large_alternative h hK hN (.inr (.inr hm))
  · exact (hHe he).elim

end SylowExteriorMarking
end CFSG.Quasithin.Chapter12.Section05.NaturalSource
