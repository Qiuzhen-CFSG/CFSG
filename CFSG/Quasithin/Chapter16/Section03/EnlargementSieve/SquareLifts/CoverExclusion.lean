module

public import CFSG.Quasithin.Chapter16.Section03.EnlargementSieve.SquareLifts.Local
public import CFSG.Quasithin.Chapter16.Section03.EnlargementSieve.SquareLifts.Core
public import CFSG.Quasithin.Chapter16.Section03.EnlargementSieve.SquareLifts.CoverExclusion.Inner
public import CFSG.Quasithin.Chapter16.Section03.EnlargementSieve.SquareLifts.CoverExclusion.TableInputs
public import CFSG.Quasithin.Chapter16.Section03.EnlargementSieve.SquareLifts.CoverExclusion.InnerMark
public import CFSG.Quasithin.Chapter16.Section03.EnlargementSieve.SquareLifts.CoverExclusion.OuterResidual

/-!
# Sporadic-cover exclusion from the earlier source clauses

The center is the embedded subgroup ⟨t⟩. For inner action, the second Sylow
centralizer forces z into K. The non-2-central quotient mark then contradicts
the order of z via I.2.2(5b). For outer action, the same source clause supplies
an inverted order-four lift with non-2-central quotient image. Its image is
fixed by z. The quotient fixed subgroup's quasisimple two-residual is exactly
the image of L; reflection of perfect-subgroup normalizers makes the lift
normalize L. Its square is t, contradicting the local square obstruction.

`table_reduction_of_tables` discharges both intrinsic table deductions using
the literal M₁₂, J₂ and HS centralizer alternatives of 16.1.5.
`not_sporadicCover_of_tables` completes the conditional exclusion with only
those earlier tables and I.2.2(5b)'s literal lifting and outer-inversion
assertions as source premises. The latter are needed only in the sporadic
cover alternative. There is no assumption that quotient fixed points all
lift to fixed points. Proving the earlier source clauses remains with their
owners; this module proves their implication in the actual contrary setup.

Source: Aschbacher–Smith, 16.3.11(3), printed p.1181 / PDF p.1198,
using 16.1.2, 16.1.5, 16.1.7 and I.2.2(5b).
-/

public section
open Subgroup Theory.GroupTheory Theory.GroupTheory.DoubleCoverCentralizer
namespace CFSG.Quasithin.Chapter16.EnlargementSieve.CoverExclusion
open ComponentTransfer.Intrinsic
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {z t : G} {L : Subgroup G}

private theorem square_eq_original (h : TerminalCounterexample T z L t)
    (hZ : center (enlargement t L) = pCore 2 (enlargement t L))
    (he : (pCore 2 (enlargement t L)).map (enlargement t L).subtype = zpowers t)
    (u : enlargement t L) (hu4 : orderOf u = 4)
    (hu2 : orderOf (QuotientGroup.mk' (center (enlargement t L)) u) = 2) :
    (u : G) ^ 2 = t := by
  classical
  have hs : u ^ 2 ∈ center (enlargement t L) := by
    apply (QuotientGroup.eq_one_iff _).mp
    change QuotientGroup.mk' _ (u ^ 2) = 1
    rw [map_pow, ← hu2, pow_orderOf_eq_one]
  rw [center_eq_zpowers_of_twoCore_image hZ he,
    mem_zpowers_iff_mem_range_orderOf, ← orderOf_coe, h.involution] at hs
  obtain ⟨n, hn, heq⟩ := Finset.mem_image.mp hs
  have hn2 : n < 2 := Finset.mem_range.mp hn
  interval_cases n
  · have hu : u ^ 2 = 1 := by simpa only [pow_zero] using heq.symm
    have hd := orderOf_dvd_of_pow_eq_one hu
    rw [hu4] at hd
    norm_num at hd
  · have hu : u ^ 2 = ⟨t, mem_enlargement_of_twoCore_image he⟩ := by
      simpa only [pow_one] using heq.symm
    exact congrArg Subtype.val hu

/-- Assembly after the two separate table deductions. The construction of
`TableReduction` from literal source tables is `table_reduction_of_tables`. -/
theorem not_sporadicCover_of_table_reduction {𝒦 : GroupClass}
    (hG : Hypothesis1611 𝒦 G) (h : TerminalCounterexample T z L t)
    (hshape : ∀ a, TerminalCounterexample T z L a → NonterminalCentralizerShape T z L a)
    (hK : IsCentralizerComponent t (enlargement t L))
    (hcomm : ⁅enlargement t L, zpowers z⁆ = enlargement t L)
    (hL : ComponentTransfer.IsComponentIn L (ComponentTransfer.centralizerIn (enlargement t L) z))
    (hlt : L < enlargement t L)
    (htables : TableReduction (action (original_normalizes_enlargement h hK)))
    (hlift : NonTwoCentralInvolutionLifting (enlargement t L))
    (hinvert : OuterInvolutionInversion (enlargement t L)) :
    ¬ SporadicCoverAlternative (enlargement t L) L := by
  intro hcover
  let K := enlargement t L
  let hn := original_normalizes_enlargement h hK
  let a := action hn
  let := hK.quasisimple
  have ha : orderOf a = 2 := action_order h.localSetup.involution hn h.localSetup.component hlt
  have he := sporadic_twoCore_image_eq hG.evenType h hshape hK hcomm hcover
  have hZ := hG.evenType.component_center_eq_twoCore h.involution hK
  have hZcard : Nat.card (center K) = 2 := by
    rw [center_eq_zpowers_of_twoCore_image hZ he, Nat.card_zpowers, ← orderOf_coe]
    exact h.involution
  by_cases hinner : ∃ k : K, a = MulAut.conj k
  · have hzK := inner_action_mem_enlargement h hshape hK hcomm hZ he hn hinner
    let zK : K := ⟨z, hzK⟩
    have hzinner : a = MulAut.conj zK := by ext x; rfl
    have hq2 : orderOf (QuotientGroup.mk' (center K) zK) = 2 := by
      have hh := orderOf_injective (quotientConj (H := K)) quotientConj_injective
        (QuotientGroup.mk' (center K) zK)
      rw [quotientConj_mk, ← hzinner, ha] at hh
      exact hh.symm
    have hz4 := order_four_of_marked_coset hZcard hlift zK hq2 (htables.inner_mark zK hzinner)
    rw [← orderOf_coe, h.localSetup.involution] at hz4
    contradiction
  · let := htables.outer_residual hinner
    obtain ⟨u, hu4, hu2, _humark, hufix⟩ := hinvert a ha hinner
    have huq : QuotientGroup.mk' (center K) u ∈ ((center K).quotientAut a).fixedSubgroup := by
      rw [MulAut.mem_fixedSubgroup, quotientAut_apply_mk, hufix, map_inv]
      exact inv_eq_of_mul_eq_one_left (by
        have hp := pow_orderOf_eq_one (QuotientGroup.mk' (center K) u)
        rwa [hu2, pow_two] at hp)
    have huN := MulAut.mem_normalizer_of_quotient_fixed a (L.subgroupOf K)
      (componentInside_fixed hn hL) u huq
    have huNg : (u : G) ∈ normalizer (L : Set G) := by
      rw [← subgroupOf_normalizer_eq hlt.le] at huN
      exact huN
    exact not_normalizer_square h hshape ⟨u, (orderOf_coe u).trans hu4,
      huNg, square_eq_original h hZ he u hu4 hu2⟩

open OtherPreliminaries

/-- Both deductions from the literal earlier centralizer tables, for the
actual quotient action and the actual relative component. -/
theorem table_reduction_of_tables {𝒦 : GroupClass}
    (hG : Hypothesis1611 𝒦 G) (h : TerminalCounterexample T z L t)
    (hK : IsCentralizerComponent t (enlargement t L))
    (hL : ComponentTransfer.IsComponentIn L
      (ComponentTransfer.centralizerIn (enlargement t L) z))
    (hlt : L < enlargement t L)
    (hcover : SporadicCoverAlternative (enlargement t L) L)
    (hm12 : ∀ r : MulAut Sporadic.Mathieu.M12, orderOf r = 2 →
      Mathieu.M12InvolutionAlternative r)
    (hj2 : ∀ r : MulAut Sporadic.LeechRelated.J2.Carrier, orderOf r = 2 →
      JankoTwoHigmanSims.J2InvolutionAlternative r)
    (hhs : ∀ r : MulAut Sporadic.LeechRelated.HS.Carrier, orderOf r = 2 →
      JankoTwoHigmanSims.HSInvolutionAlternative r) :
    TableReduction (action (original_normalizes_enlargement h hK)) :=
  ⟨inner_mark_of_tables hm12 hhs hG h hK hL hlt hcover,
    outer_residual_of_tables hG h hK hL hlt hcover hm12 hj2 hhs⟩

/-- The sporadic-cover part of 16.3.11(3), conditional only on the literal
earlier 16.1.5(4),(8),(10) tables and I.2.2(5b) assertions. The latter source
clauses are invoked only for a sporadic cover; neither the quotient mark,
the residual identification, nor a normalizer-square witness is an input.
No `FourAlternatives` premise is required. -/
theorem not_sporadicCover_of_tables {𝒦 : GroupClass}
    (hG : Hypothesis1611 𝒦 G) (h : TerminalCounterexample T z L t)
    (hshape : ∀ a, TerminalCounterexample T z L a → NonterminalCentralizerShape T z L a)
    (hK : IsCentralizerComponent t (enlargement t L))
    (hcomm : ⁅enlargement t L, zpowers z⁆ = enlargement t L)
    (hL : ComponentTransfer.IsComponentIn L
      (ComponentTransfer.centralizerIn (enlargement t L) z))
    (hlt : L < enlargement t L)
    (hm12 : ∀ r : MulAut Sporadic.Mathieu.M12, orderOf r = 2 →
      Mathieu.M12InvolutionAlternative r)
    (hj2 : ∀ r : MulAut Sporadic.LeechRelated.J2.Carrier, orderOf r = 2 →
      JankoTwoHigmanSims.J2InvolutionAlternative r)
    (hhs : ∀ r : MulAut Sporadic.LeechRelated.HS.Carrier, orderOf r = 2 →
      JankoTwoHigmanSims.HSInvolutionAlternative r)
    (hlift : SporadicCoverAlternative (enlargement t L) L →
      NonTwoCentralInvolutionLifting (enlargement t L))
    (hinvert : SporadicCoverAlternative (enlargement t L) L →
      OuterInvolutionInversion (enlargement t L)) :
    ¬ SporadicCoverAlternative (enlargement t L) L := by
  intro hcover
  exact not_sporadicCover_of_table_reduction hG h hshape hK hcomm hL hlt
    (table_reduction_of_tables hG h hK hL hlt hcover hm12 hj2 hhs)
    (hlift hcover) (hinvert hcover) hcover

end CFSG.Quasithin.Chapter16.EnlargementSieve.CoverExclusion
