module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.BlockCases.OriginalSource.AlternatingSix
public import Theory.GroupTheory.CComponent.HexacodeTheta
public import Theory.Alternating.OddCentralCovers
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.ExceptionalRestrictions.Ahat6
public import Theory.GroupTheory.CComponent.HexacodeTheta.InnerAction
public import Theory.Quasithin.CoprimeRank

/-!
# The original Â₆ containment and cubic fixed-space geometry

The actual quotient is the perfect triple cover of A₆. Its checked
order-three normalizer theorem puts every local theta generator in the
component, proving Y₊≤L in source15.3.17. In a group of three-rank at most
two, a rank-two subgroup contains the cubic center: otherwise adjoining a
central cubic to an elementary nine gives rank three. The proved quadratic
scalar relation then makes the Y₊-fixed subgroup of the actual U trivial.

The final consumer uses the literal ambient image of U and discharges its
containment and rank hypotheses from the original selected setup. These
are the scalar and containment inputs to the Â₆ branch. The marked-plane
Sylow-action contradiction is supplied by `ExceptionalSixFirstChoice`.
Source: Aschbacher–Smith15.3.17,15.3.21, printed pp.1126–1127, andC.1.22,p.129.
-/


public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.BlockCases.OriginalSource
variable {G : Type*} [Group G] [Finite G]

/-- The actual triple-cover quotient puts each local cubic generator into L,
using the ambient three-rank bound and its already known normalizer action. -/
theorem yplus_le_of_exceptionalSix_block
    (d : LocalData G) {I : Subgroup G} (c : ComponentWitness d I)
    (hθ : theta (d.MI I) = d.Yplus) (hrI : primeRank 3 I ≤ 2)
    (hm : ChapterC.IsExceptionalAhat6Block c.L) : d.Yplus ≤ c.L := by
  let := hm.2.1
  obtain ⟨e⟩ := hm.2.2.2.1
  obtain ⟨f⟩ := GLS3.Chapter5.OddCentralCovers.triple_six_equiv_hexacode e hm.2.2.1
  let K := c.L.subgroupOf I
  let a : K ≃* c.L := subgroupOfEquivOfLe (component_le c)
  let b : (K ⧸ pCore 2 K) ≃* Atlas.Codes.HexEvenAutomorphisms :=
    (QuotientGroup.congr _ _ a (pCore_map_iso 2 a)).trans f
  have hYN : d.Yplus ≤ normalizer (c.L : Set G) :=
    le_normalizer_iff_commutator_le_left.mpr c.commutator_eq.ge
  have hYNK : d.Yplus.subgroupOf I ≤ normalizer (K : Set I) := by
    rw [←subgroupOf_normalizer_eq (component_le c)]
    exact comap_mono hYN
  rw [←hθ]
  apply (closure_le _).mpr
  rintro x ⟨hx,hx3⟩
  let y : I := ⟨x,hx.2⟩
  have hy3 : orderOf y = 3 := by simpa only [←Subgroup.orderOf_coe] using hx3
  have hyN : y ∈ normalizer (K : Set I) :=
    hYNK (hθ ▸ subset_closure ⟨hx,hx3⟩)
  exact HexacodeTheta.order_three_mem K
    (LinearThree.Extension.SourceCases.component_in_overgroup d c) b hrI hy3 hyN

/-- Source15.3.17's required containment in the Â₆ branch, with all earlier
local inputs derived from the original selected setup. -/
theorem source_15_3_17_exceptionalSix_containment
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (d : LocalData G)
    (hempty : MainForward.faithfulLocalComponents d.T = ∅)
    (hM : ChapterA.Section05To06.IsOrderingMaximal d.T d.M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions d.T : Set G)) = {d.Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (d.T : Subgroup G)).ncard)
    {I : Subgroup G} (hI : I ∈ d.Hplus)
    (c : ComponentWitness d I) (hm : ChapterC.IsExceptionalAhat6Block c.L) :
    d.Yplus ≤ c.L := by
  have h11 := OutsideStructure.source_lemma_15_3_11_from_selection
    hG d hempty hM hu hmany I hI
  exact yplus_le_of_exceptionalSix_block d c h11.theta_eq.symm
    ((OutsideStructure.outside_sqtk hG d hI).stronglyQuasithin 3 (by decide) (by decide)) hm

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.BlockCases.OriginalSource

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.BlockCases.OriginalSource
open ChapterC ChapterC.ExceptionalRestrictions
variable {G : Type*} [Group G] [Finite G]

/-- A rank-two subgroup contains a cubic center when the whole group has three-rank at most two. -/
theorem cubic_center_le_of_rank_two (H : Subgroup G)
    (hrH : 2 ≤ primeRank 3 H) (hrG : primeRank 3 G ≤ 2)
    (hc : Nat.card (center G) = 3) : center G ≤ H := by
  let P : Sylow 3 H := Classical.choice inferInstance
  have hn : ¬ IsCyclic P := by
    intro hcyc
    have hr := P.primeRank_le_one_of_isCyclic hcyc
    omega
  obtain ⟨E,_,hEcard,hE⟩ := P.isPGroup'.exists_normal_elementary_prime_sq_of_odd_not_isCyclic
    (by decide) hn
  let := hE
  let : IsElementaryAbelian 3 (E.map (P : Subgroup H).subtype) := IsElementaryAbelian.map _
  let A := (E.map (P : Subgroup H).subtype).map H.subtype
  let : IsElementaryAbelian 3 A := IsElementaryAbelian.map H.subtype
  have hAc : Nat.card A = 3 ^ 2 := by
    rw [card_map_of_injective H.subtype_injective,
      card_map_of_injective (P : Subgroup H).subtype_injective]
    exact hEcard
  intro z hz
  by_contra hzH
  have hz1 : z ≠ 1 := fun he => hzH (he ▸ H.one_mem)
  have hz3 : orderOf z = 3 := orderOf_eq_prime (by
    have h := pow_card_eq_one' (x := (⟨z,hz⟩ : center G))
    rw [hc] at h
    exact congrArg Subtype.val h) hz1
  have hfix : A ≤ centralizer ({z} : Set G) := by
    intro a _
    exact mem_centralizer_singleton_iff.mpr (mem_center_iff.mp hz a)
  have hbad := IsElementaryAbelian.primeRank_ge_of_fixed_join A z hz3
    (fun h => hzH (map_subtype_le _ h)) hfix hAc
  omega

/-- The actual cubic center lies in every three-rank-two subgroup of the
exceptional Â₆ two-core quotient. Consequently such a subgroup fixes no
nonidentity element of U, by the proved central cubic quadratic relation. -/
theorem exceptionalSix_fixed_vector_eq_one
    (h : IsExceptionalAhat6Block G) (hrG : primeRank 3 G ≤ 2)
    (H : Subgroup G) (hrH : primeRank 3 H = 2)
    (u : blockU G) (hu : (u : G) ∈ centralizer (H : Set G)) : u = 1 := by
  let := h.1.elementary
  let q := QuotientGroup.mk' (pCore 2 G)
  let B := H.map q
  let f := q.subgroupMap H
  have hk : IsPGroup 2 f.ker := by
    let j : f.ker →* pCore 2 G := (H.subtype.comp f.ker.subtype).codRestrict _ (by
      intro x
      apply (QuotientGroup.eq_one_iff _).mp
      exact congrArg Subtype.val (show f x.val = 1 from x.property))
    exact pCore_isPGroup.of_injective j (by
      intro x y hh
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun x : pCore 2 G => (x : G)) hh)
  obtain ⟨n,hn⟩ := hk.exists_card_eq
  have hcop : Nat.Coprime 3 (Nat.card f.ker) := by
    rw [hn]
    exact (by decide : Nat.Coprime 3 2).pow_right n
  have hrB : 2 ≤ primeRank 3 B := by
    have hh := primeRank_le_of_coprime_ker 3 f hcop
    rw [hrH] at hh
    exact hh
  have hrQ : primeRank 3 (G ⧸ pCore 2 G) ≤ 2 := by
    rw [primeRank_quotient_eq_of_isTwoGroup 3 (by decide) _ pCore_isPGroup]
    exact hrG
  have hZB := cubic_center_le_of_rank_two B hrB hrQ h.2.2.1
  obtain ⟨z,hz⟩ := exists_prime_orderOf_dvd_card' (G := center (G ⧸ pCore 2 G)) 3
    (by rw [h.2.2.1])
  have hz1 : (z : G ⧸ pCore 2 G) ≠ 1 := by
    intro he
    have hh : z = 1 := Subtype.ext he
    rw [hh,orderOf_one] at hz
    contradiction
  have hz3 : (z : G ⧸ pCore 2 G) ^ 3 = 1 := congrArg Subtype.val (hz ▸ pow_orderOf_eq_one z)
  obtain ⟨y,hy,hyz⟩ := hZB z.property
  let ρ := uRepresentation h.1
  have hfix : ρ z (Additive.ofMul u) = Additive.ofMul u := by
    rw [←hyz]
    apply Additive.toMul.injective
    apply Subtype.ext
    rw [uRepresentation_apply]
    change y * (u : G) * y⁻¹ = (u : G)
    rw [hu y hy,mul_inv_cancel_right]
  have hzero := LinearMap.congr_fun (central_cubic_quadratic h z z.property hz1 hz3)
    (Additive.ofMul u)
  change ρ z (ρ z (Additive.ofMul u)) + ρ z (Additive.ofMul u) + Additive.ofMul u = 0 at hzero
  have hadd : Additive.ofMul u + Additive.ofMul u = 0 := by
    apply Additive.toMul.injective
    change u * u = 1
    rw [←pow_two]
    exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 (blockU G)) u
  rw [hfix,hfix,hadd,zero_add] at hzero
  exact hzero

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.BlockCases.OriginalSource

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.BlockCases.OriginalSource
variable {G : Type*} [Group G] [Finite G]

/-- In the original Â₆ branch, the literal ambient U-image has no nonidentity
Y₊-fixed element. Both the component containment and ambient rank are derived
from the preceding original context. -/
theorem source_15_3_21_exceptionalSix_fixedU
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (d : LocalData G)
    (hempty : MainForward.faithfulLocalComponents d.T = ∅)
    (hM : ChapterA.Section05To06.IsOrderingMaximal d.T d.M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions d.T : Set G)) = {d.Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (d.T : Subgroup G)).ncard)
    {I : Subgroup G} (hI : I ∈ d.Hplus) (hrank : primeRank 3 d.Yplus = 2)
    (c : ComponentWitness d I) (hm : ChapterC.IsExceptionalAhat6Block c.L) :
    (ChapterC.blockU c.L).map c.L.subtype ⊓ centralizer (d.Yplus : Set G) = ⊥ := by
  have hYL := source_15_3_17_exceptionalSix_containment hG d hempty hM hu hmany hI c hm
  have hrI : primeRank 3 I ≤ 2 :=
    (OutsideStructure.outside_sqtk hG d hI).stronglyQuasithin 3 (by decide) (by decide)
  have hrL : primeRank 3 c.L ≤ 2 :=
    (_root_.primeRank_le_of_injective 3 (inclusion (component_le c)) (inclusion_injective _)).trans hrI
  have hrH : primeRank 3 (d.Yplus.subgroupOf c.L) = 2 := by
    rw [primeRank_congr 3 (subgroupOfEquivOfLe hYL),hrank]
  apply le_bot_iff.mp
  rintro x ⟨⟨v,hv,rfl⟩,hx⟩
  have hfix : v ∈ centralizer (d.Yplus.subgroupOf c.L : Set c.L) := by
    intro y hy
    exact Subtype.ext (hx y hy)
  have he := exceptionalSix_fixed_vector_eq_one hm hrL (d.Yplus.subgroupOf c.L)
    hrH ⟨v,hv⟩ hfix
  exact congrArg (fun u : ChapterC.blockU c.L => ((u : c.L) : G)) he

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.BlockCases.OriginalSource
