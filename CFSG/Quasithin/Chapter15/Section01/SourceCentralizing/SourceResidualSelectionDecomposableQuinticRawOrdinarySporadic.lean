module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticRawOrdinaryQuinticPair
public import Theory.Mathieu.SmallModuleRanks.M12
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.NormalElementaryBound
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.SylowNormalElementary
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.AutomorphismTwoRank
public import Theory.SpecificGroups.Held.SylowNormalSixteen
public import Theory.SpecificGroups.Held.TwoRank.Intrinsic
public import Theory.SpecificGroups.Rudvalis.Model.SylowElementarySixteen
public import Theory.SpecificGroups.Rudvalis.Model.TwoRankSix

/-!
# Five ordinary sporadic quotients excluded on the original raw component

The original quotient contains a Sylow-normal elementary subgroup of order
at least sixteen fully moved by an actual five-group. Native elementary
bounds exclude M₁₂, J₂ and HS. The Held and Rudvalis rank bounds force order
sixteen, and their intrinsic Sylow-normal sixteen normalizers are five-free.
The same ordinary component and its possible central two-cover are retained.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
open ChapterD.RatioDecomposition DecomposableMarker
variable {G : Type*} [Group G] [Finite G]

/-- The original full quintic source excludes M₁₂, J₂, HS, Held and Rudvalis
as quotients of its same prescribed ordinary component, without M-generation. -/
theorem PreparedChosenModule.decomposable_five_raw_ordinary_sporadic_exclusions
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (h : PreparedChosenModule T M V) (hfull : V = localModule T M) :
    letI := h.elementary
    ∀ {U : Submodule (ZMod 2) (Additive V)}
      (c : FactorData (imageRepresentation M V h.normalized)
        (Jhat (imageRepresentation M V h.normalized)) U)
      (d : Decomposition c.representation), d.FittingFull →
    ∀ (s : ThompsonPair (T := T) h.normalized c d)
      (π : internalActionImage M V h.normalized →* Equiv.Perm d.Index),
      (∀ g k, (c.ambientFactor d k).actor.map (MulAut.conj g).toMonoidHom =
        (c.ambientFactor d (π g k)).actor) →
      (∀ g k, (c.ambientFactor d k).space.map (imageRepresentation M V h.normalized g) =
        (c.ambientFactor d (π g k)).space) →
      SourceCases.Decomposable (imageRepresentation M V h.normalized) (T : Subgroup G) M
        (actionHom M V h.normalized).rangeRestrict c d π →
      cubicRatio (imageRepresentation M V h.normalized) = 2 → s.prime = 5 →
      let Z1 := thompsonPlane T V (c.ambientFactor d s.first).space
      let G1 := centralizer (Z1 : Set G)
      let C := M ⊓ G1
      let R := (pResidual 2 C).map C.subtype
      let S := (T : Subgroup G) ⊓ G1
      ∀ {L : Subgroup G}, L ≤ G1 → IsComponent G1 (L.subgroupOf G1) →
        center L = pCore 2 L → Chapter1.IsSylowIn 2 (S ⊓ L) L →
        R ⊔ ⁅V,R⁆ ≤ normalizer (L : Set G) → ⁅L,⁅V,R⁆⁆ ≠ ⊥ →
        ¬ Nonempty ((L ⧸ pCore 2 L) ≃* Sporadic.Mathieu.M12) ∧
        ¬ Nonempty ((L ⧸ pCore 2 L) ≃* Sporadic.LeechRelated.J2.Carrier) ∧
        ¬ Nonempty ((L ⧸ pCore 2 L) ≃* Sporadic.LeechRelated.HS.Carrier) ∧
        ¬ Nonempty ((L ⧸ pCore 2 L) ≃* Held.He) ∧
        ¬ Nonempty ((L ⧸ pCore 2 L) ≃* Rudvalis.Model) := by
  let := h.elementary
  intro U c d hd s π hp hs hdec hq hfive Z1 G1 C R S L hLG hLc hcenter hSyl hnL hmove
  have hpairs {X : Type} [Group X] (e : (L ⧸ pCore 2 L) ≃* X)
      (hz : center X = ⊥) (ho : IsPGroup 2 (MulAut.Outer X)) :
      ∃ (P : Sylow 2 X) (E D : Subgroup X), IsElementaryAbelian 2 E ∧
        E ≤ (P : Subgroup X) ∧ (P : Subgroup X) ≤ normalizer (E : Set X) ∧
        IsPGroup 5 D ∧ ⁅E,D⁆ = E ∧ E ≠ ⊥ ∧ 16 ≤ Nat.card E :=
    h.decomposable_five_raw_ordinary_quintic_pair
      hG T hempty hM hmany hJ hfull c d hd s π hp hs hdec hq hfive
      hLG hLc hcenter hSyl hnL hmove e hz ho
  refine ⟨?_,?_,?_,?_,?_⟩
  · rintro ⟨e⟩
    obtain ⟨P,E,D,hE,_,_,_,_,_,hc⟩ := hpairs e Sporadic.Mathieu.m12_center_eq_bot
      Sporadic.Mathieu.M12SmallPair.ValueBoundParabolics.outer_isPGroup_two
    have hb := (primeRank_le_iff_elementary_card_le Sporadic.Mathieu.M12).mp
      Sporadic.Mathieu.m12_twoRank_le_three E hE
    norm_num at hb
    omega
  · rintro ⟨e⟩
    obtain ⟨P,E,D,hE,hEP,hPE,_,_,_,hc⟩ := hpairs e
      Sporadic.LeechRelated.J2.OrdinaryLocal.center_eq_bot Sporadic.LeechRelated.J2.outer_isTwoGroup
    let := hE
    have hb := Sporadic.LeechRelated.J2.sylow_normal_elementary_card_le_four P
      (E.subgroupOf P) ((normal_subgroupOf_iff_le_normalizer hEP).mpr hPE)
      (IsElementaryAbelian.subgroupOf hEP)
    rw [Nat.card_congr (subgroupOfEquivOfLe hEP).toEquiv] at hb
    omega
  · rintro ⟨e⟩
    have ho : IsPGroup 2 (MulAut.Outer Sporadic.LeechRelated.HS.Carrier) :=
      IsPGroup.of_card_dvd_pow (n := 1) (by
        simpa only [pow_one] using Sporadic.LeechRelated.HS.outer_card_dvd_two)
    obtain ⟨P,E,D,hE,_,hPE,_,_,_,hc⟩ := hpairs e
      Sporadic.LeechRelated.HS.BlockNormalizer.center_carrier_eq_bot ho
    have hb := Sporadic.LeechRelated.HS.normal_elementary_card_le_eight P E hE hPE
    omega
  · rintro ⟨e⟩
    obtain ⟨P,E,D,hE,hEP,hPE,hD,hED,hEn,_⟩ := hpairs e
      Held.LocalPairs.center_eq_bot Held.outer_isPGroup_two
    let := hE
    have hb : Nat.card E ≤ 64 :=
      (primeRank_le_iff_elementary_card_le Held.He).mp Held.primeRank_two_le_six E hE
    have hc := card_eq_sixteen_of_quintic_movement E D hD hED hEn hb
    exact Held.sylow_normal_sixteen_normalizer_not_five P E hEP hE hc hPE
      (five_dvd_normalizer_of_quintic_movement E D hD hED hEn)
  · rintro ⟨e⟩
    let : IsQuasisimple (L.subgroupOf G1) := hLc.2
    let : IsQuasisimple L := IsQuasisimple.of_mulEquiv (subgroupOfEquivOfLe hLG)
    let : IsSimpleGroup (L ⧸ center L) := IsQuasisimple.simple
    let f := (QuotientGroup.quotientMulEquivOfEq hcenter).trans e
    let : IsSimpleGroup Rudvalis.Model := f.symm.isSimpleGroup
    obtain ⟨P,E,D,hE,_,hPE,hD,hED,hEn,_⟩ := hpairs e
      Rudvalis.LowCentralizers.model_center_eq_bot Rudvalis.outer_isPGroup_two
    let := hE
    have hb : Nat.card E ≤ 64 :=
      (primeRank_le_iff_elementary_card_le Rudvalis.Model).mp Rudvalis.primeRank_le_six E hE
    have hc := card_eq_sixteen_of_quintic_movement E D hD hED hEn hb
    exact Rudvalis.SylowElementarySixteen.normalizer_sixteen_not_five P E hE hc hPE
      (five_dvd_normalizer_of_quintic_movement E D hD hED hEn)

end CFSG.Quasithin.Chapter15.Section01
