module
public import Stellmacher.SectionTen.TenOneSmallResidualQuotientElementary
public import Stellmacher.SectionTen.TenOneSmallNeighborCore

/-!
# The middle core acts into the neighborhood subgroup

In the actual order-eight, SL2(2) branch of Section Ten, the commutator of
the middle core with the first residual two-core lies in the generated
middle neighborhood subgroup U. This is the sentence immediately following
the quaternion-product recognition in Stellmacher (10.1)(a), Journal of
Algebra 190 (1997), printed p.60.

The first core has index two in the edge stabilizer, while U lies in the
edge and escapes that core. Hence together they generate the edge. The
first residual core normalizes U and its commutator with the first core
lies in Vfirst, hence in U, by the proved residual quotient kernel. In the
literal conjugation action on Rfirst/(U intersect Rfirst), both generating
subgroups therefore act trivially. The entire edge acts trivially, giving
the required middle-core commutator containment.
-/
namespace Stellmacher.SectionTen
open Later SectionsFiveToSeven CosetGraphContext SevenSix SectionNine
open scoped commutatorElement
universe u
variable {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
  {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
  {embedding : G →* H} {T A B : Subgroup G}

public theorem ten_one_middle_core_residual_commutator
    (ctx : AmbientSectionTenContext H S0 S P1 P2 embedding T A B)
    (middle : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath 2 middle)
    (hsmall : Nat.card (VAt ctx.Γ ctx.criticalPath.firstStep) = 8)
    (hmodel : QuotientIsModel (GAt ctx.Γ ctx.criticalPath.firstStep)
      (QAt ctx.Γ ctx.criticalPath.firstStep) SL2Two) :
    ⁅QAt ctx.Γ middle,twoCoreIn (EAt ctx.Γ ctx.criticalPath.firstStep)⁆ ≤
      GeneratedNeighborhoodV ctx.Γ middle := by
  let P := GAt ctx.Γ ctx.criticalPath.firstStep
  let M := GAt ctx.Γ middle
  let Q := QAt ctx.Γ ctx.criticalPath.firstStep
  let R := twoCoreIn (EAt ctx.Γ ctx.criticalPath.firstStep)
  let V := VAt ctx.Γ ctx.criticalPath.firstStep
  let U := GeneratedNeighborhoodV ctx.Γ middle
  let edge := P ⊓ M
  obtain ⟨_,hfirst,_,_⟩ := sectionTenOpeningGeometry ctx middle hpath
  have hb : 2 < ctx.criticalPath.length := by rw [ctx.critical_length]; decide
  have hQself (v : ctx.Γ.Vertex) : QAt ctx.Γ v ≤ GAt ctx.Γ v := by
    change ctx.Γ.twoCoreAt v ≤ _
    rw [ctx.Γ.twoCoreAt_def]
    exact twoCoreIn_le _
  have hQneighbor {v w : ctx.Γ.Vertex} (hvw : ctx.Γ.adjacent v w) :
      QAt ctx.Γ v ≤ GAt ctx.Γ w :=
    ((lemma_seven_three ctx.sectionSeven ctx.Γ).sylow_and_core v w
      ((mem_neighborhood_iff_adjacent ctx.Γ).mpr hvw) default).2.2
  have hQedge : Q ≤ edge := le_inf (hQself _) (hQneighbor (ctx.Γ.adjacent_symm hfirst))
  have hQmiddle : QAt ctx.Γ middle ≤ edge := le_inf (hQneighbor hfirst) (hQself _)
  have hUQ : U ≤ QAt ctx.Γ middle :=
    nine_seven_neighborhood_le_own_core ctx.toLocalContext.toSectionNineLocalContext hb middle
  have hUedge : U ≤ edge := hUQ.trans hQmiddle
  have hVU : V ≤ U := le_sSup ⟨_,(mem_neighborhood_iff_adjacent ctx.Γ).mpr hfirst,rfl⟩
  have hMU : M ≤ Subgroup.normalizer (U : Set G) :=
    nine_seven_stabilizer_normalizes_neighborhood ctx.Γ middle
  have hRQ : R ≤ Q := by
    change twoCoreIn (ctx.Γ.twoResidualAt ctx.criticalPath.firstStep) ≤
      ctx.Γ.twoCoreAt ctx.criticalPath.firstStep
    rw [ctx.Γ.twoResidualAt_def,ctx.Γ.twoCoreAt_def,residual_core_eq_inter_core]
    exact inf_le_right
  have hRedge := hRQ.trans hQedge
  have hE : EAt ctx.Γ ctx.criticalPath.firstStep = twoResidualIn P := ctx.Γ.twoResidualAt_def _
  have hEP : EAt ctx.Γ ctx.criticalPath.firstStep ≤ P := hE ▸ twoResidualIn_le P
  have hPR : P ≤ Subgroup.normalizer (R : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (hRQ.trans (hQself _))).mp
      (twoCoreIn_normal_of_normal _ P hEP (hE ▸ twoResidualIn_normal P))
  have hindexU : Q.relIndex U = 2 :=
    ten_one_small_neighbor_core_index ctx middle hpath hmodel hfirst
  have hcardEdge : Nat.card edge = 2 * Nat.card Q :=
    (cubic_local_action_of_sl2Two_quotient ctx.Γ ctx.sectionSeven
      ctx.criticalPath.firstStep hmodel).edge_card middle (ctx.Γ.adjacent_symm hfirst)
  have hindexEdge : Q.relIndex edge = 2 := by
    have hcount := (Q.subgroupOf edge).index_mul_card
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQedge).toEquiv] at hcount
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos (hcount.trans hcardEdge)
  have hjoinLe : Q ⊔ U ≤ edge := sup_le hQedge hUedge
  have hindexJoin : Q.relIndex (Q ⊔ U) = 2 := by
    have hdiv : Q.relIndex (Q ⊔ U) ∣ 2 := by
      rw [← hindexEdge]
      exact dvd_of_mul_right_eq ((Q ⊔ U).relIndex edge)
        (Subgroup.relIndex_mul_relIndex Q (Q ⊔ U) edge le_sup_left hjoinLe)
    rcases (Nat.dvd_prime Nat.prime_two).mp hdiv with hone | htwo
    · have hUQ' : U ≤ Q := le_sup_right.trans (Subgroup.relIndex_eq_one.mp hone)
      have h := (Subgroup.relIndex_eq_one.mpr hUQ')
      rw [hindexU] at h
      contradiction
    · exact htwo
  have hjoin : Q ⊔ U = edge := by
    have hcount := (Q.subgroupOf (Q ⊔ U)).index_mul_card
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (show Q ≤ Q ⊔ U from le_sup_left)).toEquiv] at hcount
    change Q.relIndex (Q ⊔ U) * Nat.card Q = Nat.card (Q ⊔ U : Subgroup G) at hcount
    rw [hindexJoin] at hcount
    exact Subgroup.eq_of_le_of_card_ge hjoinLe (by rw [hcardEdge,← hcount])
  have hN : (U.subgroupOf R).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer (hRedge.trans (inf_le_right.trans hMU))
  let _ := hN
  have hedgeR : edge ≤ Subgroup.normalizer (R : Set G) := inf_le_left.trans hPR
  have hedgeU : edge ≤ Subgroup.normalizer (U : Set G) := inf_le_right.trans hMU
  obtain ⟨action,hact⟩ := Subgroup.exists_quotient_conjugation_action edge R U hedgeR hedgeU hN
  have hRQu : ⁅R,Q⁆ ≤ U :=
    (ten_one_small_residual_quotient_elementary ctx middle hpath hsmall hmodel).choose_spec.2.trans hVU
  have hRU : ⁅R,U⁆ ≤ U := Subgroup.le_normalizer_iff_commutator_le_right.mp
    (hRedge.trans hedgeU)
  have hQker := Subgroup.quotient_conjugation_action_kills_commutator_layer
    edge R U Q hN hedgeR hRQu action hact
  have hUker := Subgroup.quotient_conjugation_action_kills_commutator_layer
    edge R U U hN hedgeR hRU action hact
  have htopker : (⊤ : Subgroup edge) ≤ action.ker := by
    have hh := sup_le hQker hUker
    rw [← Subgroup.subgroupOf_sup hQedge hUedge,hjoin,Subgroup.subgroupOf_self] at hh
    exact hh
  apply Subgroup.commutator_le.mpr
  intro a ha r hr
  let aE : edge := ⟨a,hQmiddle ha⟩
  let rR : R := ⟨r,hr⟩
  have hfix : action aE (QuotientGroup.mk' (U.subgroupOf R) rR) =
      QuotientGroup.mk' (U.subgroupOf R) rR := by
    rw [show action aE = 1 from htopker (Subgroup.mem_top _)]; rfl
  rw [hact] at hfix
  have hh := QuotientGroup.eq_iff_div_mem.mp hfix
  change a * r * a⁻¹ / r ∈ U at hh
  simpa only [commutatorElement_def,div_eq_mul_inv] using hh
end Stellmacher.SectionTen

