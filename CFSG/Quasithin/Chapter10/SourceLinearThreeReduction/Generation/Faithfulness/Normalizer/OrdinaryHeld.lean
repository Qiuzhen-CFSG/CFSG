module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.Faithfulness.Normalizer.SpanOrder
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.Faithfulness.Normalizer.HeldCenter
public import CFSG.Quasithin.ChapterC.Section03.OrdinaryPlacement.SourcePlacement
public import Theory.SpecificGroups.Held.SylowOrderBound
public import Theory.SpecificGroups.Held.OddOrderBound
public import Theory.SpecificGroups.Held.LocalPairs.SylowGeometry.ThreePrimeOvergroups.PairBound
public import Theory.SpecificGroups.Held.TwoRank.Intrinsic
/-!
# Excluding Held in the actual nonnormal covering configuration

The full component is centerless by the proved odd-center result and the
vanishing odd core of C.2.8. The original conjugate span therefore embeds in
the native Held carrier. Its paired quotient has seed order squared, and
its two-core has order divisible by 64. The actual elementary layer and
Held's two-rank bound exclude five from the seed order; the remaining
order bound forces eight to divide that order. Thus 4096 divides Held's
order, contradicting the native Sylow bound.

The proof uses the given central-quotient marking through its proved full
component lift and makes no full-Sylow containment assumption.
Source: Aschbacher--Smith C.3.5, 4.4.6--7 and 10.2.3(2), pp.150,620,745.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC.HypothesisC28
universe u
variable {G : Type u} [Group G] [Finite G] {H M L R V : Subgroup G}

/-- The remaining Held ordinary component forces normality of the original seed. -/
theorem normalizes_of_simple_ordinary_held
    (h : HypothesisC28 KnownSimple.IsKnownSimple H M L R V)
    [IsQuasisimple (L ⧸ pCore 2 L)] (hz : center (L ⧸ pCore 2 L) = ⊥)
    (K : Subgroup H) (hK : IsComponent H K)
    (e : K ⧸ center K ≃* Held.He) : M ≤ normalizer (L : Set G) := by
  by_contra hn
  let Q := L ⧸ pCore 2 L
  let X := conjugateSpanBy L M
  let : IsSimpleGroup (Q ⧸ center Q) := IsQuasisimple.simple
  let : IsSimpleGroup Q := ((QuotientGroup.quotientMulEquivOfEq hz).trans
    QuotientGroup.quotientBot).symm.isSimpleGroup
  have hXH : X ≤ H := (conjugateSpanBy_le_self h.component_le).trans h.local_le
  let j : X →* K := (inclusion (h.ordinary_span_le K hK)).comp
    (subgroupOfEquivOfLe hXH).symm.toMonoidHom
  have hj : Function.Injective j := by
    intro x y he
    exact Subtype.ext (congrArg (fun k : K => ((k : H) : G)) he)
  obtain ⟨a,_⟩ := h.ordinary_held_equiv K hK e
  have hXdvd : Nat.card X ∣ Nat.card Held.He :=
    (card_dvd_of_injective j hj).trans (Nat.card_congr a.toEquiv).dvd
  obtain ⟨aX⟩ := simple_nonnormal_span_product_equiv h hn
  have hcard : Nat.card X = Nat.card Q^2 * Nat.card (pCore 2 X) := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (pCore 2 X),
      Nat.card_congr aX.toEquiv,Nat.card_prod,pow_two]
  have hQdvd : Nat.card Q^2 ∣ Nat.card Held.He :=
    (show Nat.card Q^2 ∣ Nat.card X by rw [hcard]; exact dvd_mul_right _ _).trans hXdvd
  have h5 : ¬ 5 ∣ Nat.card Q := by
    intro hd
    let : Fact (Nat.Prime 5) := ⟨by decide⟩
    obtain ⟨W,hWe,_,hWC,_,hr⟩ := h.simple_nonnormal_elementary_layer_ranks hn
    let := hWe
    have hWX : W ≤ X := hWC.trans (pCoreIn_le 2 X)
    let f : W →* Held.He := a.toMonoidHom.comp (j.comp (inclusion hWX))
    have hf : Function.Injective f := a.injective.comp (hj.comp (inclusion_injective hWX))
    let : IsElementaryAbelian 2 f.range :=
      IsElementaryAbelian.of_surjective f.rangeRestrict f.rangeRestrict_surjective
    have hc : Nat.card W ≤ 2^6 := by
      rw [Nat.card_congr (MonoidHom.ofInjective hf).toEquiv]
      exact (primeRank_le_iff_elementary_card_le Held.He).mp
        Held.primeRank_two_le_six f.range inferInstance
    have hup : primeRank 5 (MulAut W) ≤ 1 := by
      apply primeRank_le_one_of_square_not_dvd
      obtain ⟨d,hd⟩ := (IsElementaryAbelian.isPGroup 2 W).exists_card_eq
      have hb : d ≤ 6 := by
        rw [hd] at hc
        exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hc
      rw [SmallNonabelianTwoGroup.card_mulAut_elementary_two_pow W d hd]
      interval_cases d <;> norm_num [Fin.prod_univ_succ]
    have hlo := hr 5 (by decide) (by decide)
    have hpos : 0 < primeRank 5 Q := Nat.pos_of_ne_zero
      (fun he => PrimeRank.eq_zero_iff_not_dvd_card.mp he hd)
    change 2 * primeRank 5 Q ≤ primeRank 5 (MulAut W) at hlo
    omega
  have h8 : 8 ∣ Nat.card Q := by
    by_contra hn8
    have hgraph := Held.NormalizerGraph.Orbital.held_le_preservingGroup
    have hHe := Held.OddOrderBound.card_dvd_of_graph_and_pair_bound hgraph
      (Held.LocalPairs.SylowGeometry.ThreePrimeOvergroups.pairStabilizer_card_dvd hgraph)
    have hsmall := held_square_order_bound Nat.card_pos.ne' (hQdvd.trans hHe)
    have hco : Nat.Coprime (Nat.card Q) 5 :=
      ((show Nat.Prime 5 by decide).coprime_iff_not_dvd.mpr h5).symm
    have h1344 : Nat.card Q ∣ 1344 := hco.dvd_mul_right.mp hsmall
    have h84 := dvd_eightyFour_of_dvd_thirteenFortyFour Nat.card_pos.ne' h1344 hn8
    exact no_simple_perfect_order_84 Q h84
  have hcore := simple_nonnormal_span_core_sixtyFour_dvd h hn
  have hlarge : 2^12 ∣ Nat.card X := by
    rw [hcard]
    have hh := Nat.mul_dvd_mul (pow_dvd_pow_of_dvd h8 2) hcore
    norm_num at hh ⊢
    exact hh
  exact Held.not_two_pow_twelve_dvd_card (hlarge.trans hXdvd)

end CFSG.Quasithin.ChapterC.HypothesisC28
