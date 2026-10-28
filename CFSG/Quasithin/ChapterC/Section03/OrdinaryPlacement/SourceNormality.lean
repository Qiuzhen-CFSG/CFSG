module
public import CFSG.Quasithin.ChapterC.Section03.OrdinaryPlacement.BinaryRankOne
public import CFSG.Quasithin.ChapterC.Section03.OrdinaryPlacement.PrimePerfectCore
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.SourceModels
public import Theory.SpecificGroups.Janko1.PerfectSubgroupCore
public import Theory.SpecificGroups.SL2.FieldAutomorphismCore
public import Theory.GroupTheory.PerfectCentralCoverQuasisimple
public import Theory.GroupTheory.GeneralizedFitting.ComponentCenterPrimeCore
public import Theory.Quasithin.Rank

/-!
# Normality of the ordinary component in the original C.2.8 configuration

The actual perfect span projects into every ordinary component with noncentral
two-core. The four possible nonnormal component models exclude that projection:
binary rank-one and odd prime-field groups have trivial projected two-core,
while perfect subgroups of J₁ have central two-core. Central-cover rigidity
lifts the last assertion. Thus the original component is normal in H.

This proves C.3.3 before the placement step, avoiding any assumption that the
radical preserves two exchanged factors. The original C.2.8 data are unchanged.
Source: Aschbacher–Smith C.3.2–3, printed p.149.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC.HypothesisC28
variable {G : Type*} [Group G] [Finite G]
variable {H M L R V : Subgroup G}

/-- The J₁ central quotient is excluded on the original source data. -/
theorem no_ordinary_component_janko_central_quotient
    (h : HypothesisC28 KnownSimple.IsKnownSimple H M L R V)
    (K : Subgroup H) (hK : IsComponent H K)
    (e : K ⧸ center K ≃* Janko1.Model) : False := by
  apply h.no_ordinary_component_of_perfect_subgroup_core_central K hK
  intro P hPK hP
  let := hP
  let q : P →* Janko1.Model :=
    (e.toMonoidHom.comp (QuotientGroup.mk' (center K))).comp (inclusion hPK)
  have hk : q.ker ≤ center P := by
    intro p hp
    have he : e (QuotientGroup.mk (inclusion hPK p)) = 1 := hp
    have hz := (QuotientGroup.eq_one_iff (inclusion hPK p)).mp
      (e.injective (by simpa only [map_one] using he))
    exact mem_center_iff.mpr fun y => Subtype.ext
      (congrArg (fun z : K => (z : H)) (mem_center_iff.mp hz (inclusion hPK y)))
  let f : PerfectCentralCovering.Cover P q.range := {
    toMonoidHom := q.rangeRestrict
    surjective := q.rangeRestrict_surjective
    isPerfect := hP
    ker_le_center := by
      intro p hp
      exact hk (congrArg Subtype.val hp) }
  let : Group.IsPerfect q.range := Group.IsPerfect.range q
  have hm : (pCore 2 P).map q.rangeRestrict ≤ pCore 2 q.range :=
    le_sSup ⟨(inferInstance : (pCore 2 P).Normal).map q.rangeRestrict
      q.rangeRestrict_surjective, pCore_isPGroup.map q.rangeRestrict⟩
  have hc : pCore 2 P ≤ center P := by
    rw [←f.comap_center]
    exact map_le_iff_le_comap.mp
      (hm.trans (Janko1.perfect_subgroup_pCore_two_le_center q.range))
  apply commutator_eq_bot_iff_le_centralizer.mpr
  rintro x ⟨u,hu,rfl⟩ y hy
  exact congrArg Subtype.val (mem_center_iff.mp (hc hu) ⟨y,hy⟩)

/-- Every ordinary component of the original H is normal. -/
theorem ordinary_component_normal
    (h : HypothesisC28 KnownSimple.IsKnownSimple H M L R V)
    (K : Subgroup H) (hK : IsComponent H K) : K.Normal := by
  have hQ : IsSQTK KnownSimple.IsKnownSimple (H ⧸ pCore 2 H) := by
    refine ⟨?_,h.sqtk.isKGroup.quotient _⟩
    intro p hp ho
    let : Fact p.Prime := ⟨hp⟩
    exact (primeRank_quotient_le_of_isTwoGroup p ho _ pCore_isPGroup).trans
      (h.sqtk.stronglyQuasithin p hp ho)
  rcases Chapter1.Section02.proposition_1_2_1_three_index_knownSimple hQ hK.isCComponent
    with hn | ⟨_,hm⟩
  · exact hn
  let := hK.2
  have hz : center K = pCore 2 K :=
    IsQuasisimple.center_eq_pCore (hK.1.pPrimeCore_eq_bot h.oddCore_eq_bot K)
  have hc := hm.of_mulEquiv (QuotientGroup.quotientMulEquivOfEq hz)
  exfalso
  cases hc with
  | linear_even n hn hm =>
    obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
    let : Fintype F := Fintype.ofFinite F
    let : CharP F 2 := charP_of_card_eq_prime_pow
      (by simpa only [Nat.card_eq_fintype_card] using hF)
    exact h.no_ordinary_component_sl2_central_quotient K hK
      (e.trans Atlas.RankOneFieldAutomorphisms.slEquivPSL.symm)
  | suzuki m hm he =>
    exact h.no_ordinary_component_suzuki_central_quotient K hK hm he.some
  | linear_prime p hp ho hm =>
    exact h.no_ordinary_component_prime_psl2_model K hK hp ho hm
  | janko he => exact h.no_ordinary_component_janko_central_quotient K hK he.some
end CFSG.Quasithin.ChapterC.HypothesisC28
