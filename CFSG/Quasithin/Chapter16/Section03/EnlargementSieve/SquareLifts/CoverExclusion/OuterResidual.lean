module

public import CFSG.Quasithin.Chapter16.Section03.EnlargementSieve.SquareLifts.CoverExclusion.TableInputs
public import CFSG.Quasithin.Chapter16.Section03.EnlargementSieve.SquareLifts.CoverExclusion.OuterResidual.Models
public import CFSG.Quasithin.Chapter16.Section03.EnlargementSieve.SquareLifts.CoverExclusion.OuterResidual.ExtensionExclusion

/-!
# The outer residual deduction for sporadic covers

Transport the genuine central-quotient action to the M₁₂, J₂, or HS
carrier supplied by the cover alternative. Perfectness preserves its
order and outer nature. The literal 16.1.5 table gives C₂×A₅,
Aut(PSL₃(2)), S₈, or the E₁₆ extension with quotient S₅. The first
three rows have quasisimple two-residual; the last is excluded by the
inherited A₆/A₈ component and its injective image in the central quotient.

The conclusion concerns O² of the full quotient fixed subgroup, embedded
in K/Z(K). The only table premises are the existing literal 16.1.5
alternatives. No residual identification or normalization witness is
assumed. The result supplies the `outer_residual` field of `TableReduction`;
the independent inner mark and source-table assertions remain with the
source assembly owner.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
16.1.5(4),(8),(10), printed pp.1171–1172 / PDF pp.1188–1189, and
16.3.11(3), printed p.1181 / PDF p.1198.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter16.EnlargementSieve.CoverExclusion
open ComponentTransfer.Intrinsic OtherPreliminaries OuterResidual

private theorem fixed_residual_of_model {H D : Type*} [Group H] [Group D]
    (b : MulAut H) (e : b.fixedSubgroup ≃* D) [IsQuasisimple (pResidual 2 D)] :
    IsQuasisimple (MulAut.fixedTwoResidual b) := by
  let d : pResidual 2 b.fixedSubgroup ≃* pResidual 2 D :=
    ((pResidual 2 b.fixedSubgroup).equivMapOfInjective e.toMonoidHom e.injective).trans
      (MulEquiv.subgroupCongr (map_pResidual 2 e))
  let := IsQuasisimple.of_mulEquiv d.symm
  exact IsQuasisimple.of_mulEquiv
    ((pResidual 2 b.fixedSubgroup).equivMapOfInjective
      b.fixedSubgroup.subtype b.fixedSubgroup.subtype_injective)

private theorem model_action_data {K M : Type*} [Group K] [Group M]
    [Group.IsPerfect K] (e : K ⧸ center K ≃* M) (a : MulAut K)
    (ha : orderOf a = 2) (ho : ¬ ∃ k : K, a = MulAut.conj k) :
    orderOf (MulAut.centralQuotientAction e a) = 2 ∧
      ¬ ∃ m : M, MulAut.centralQuotientAction e a = MulAut.conj m :=
  ⟨(orderOf_injective _ (MulAut.centralQuotientAction_injective e) a).trans ha,
    fun h => ho ((MulAut.centralQuotientAction_inner_iff e a).mp h)⟩

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {z t : G} {L : Subgroup G}

/-- The outer field of `TableReduction`, deduced from the literal sporadic
tables and the actual component. The uniform centralizer-shape and
commutator hypotheses of the full exclusion are unnecessary for this field. -/
theorem outer_residual_of_tables {𝒦 : GroupClass}
    (hG : Hypothesis1611 𝒦 G) (h : TerminalCounterexample T z L t)
    (hK : IsCentralizerComponent t (enlargement t L))
    (hL : ComponentTransfer.IsComponentIn L
      (ComponentTransfer.centralizerIn (enlargement t L) z))
    (hlt : L < enlargement t L)
    (hcover : SporadicCoverAlternative (enlargement t L) L)
    (ht12 : ∀ r : MulAut Sporadic.Mathieu.M12,
      orderOf r = 2 → Mathieu.M12InvolutionAlternative r)
    (htj2 : ∀ r : MulAut Sporadic.LeechRelated.J2.Carrier,
      orderOf r = 2 → JankoTwoHigmanSims.J2InvolutionAlternative r)
    (hths : ∀ r : MulAut Sporadic.LeechRelated.HS.Carrier,
      orderOf r = 2 → JankoTwoHigmanSims.HSInvolutionAlternative r)
    (ho : ¬ ∃ k : enlargement t L,
      action (original_normalizes_enlargement h hK) = MulAut.conj k) :
    IsQuasisimple (MulAut.fixedTwoResidual ((center (enlargement t L)).quotientAut
      (action (original_normalizes_enlargement h hK)))) := by
  let K := enlargement t L
  let hn := original_normalizes_enlargement h hK
  let a := action hn
  let b := (center K).quotientAut a
  let := hK.quasisimple
  have ha : orderOf a = 2 :=
    action_order h.localSetup.involution hn h.localSetup.component hlt
  have hZ : center K = pCore 2 K :=
    hG.evenType.component_center_eq_twoCore h.involution hK
  have hinside := componentInside_fixed hn hL
  have hc := MulAut.component_image_in_quotient_fixed a (L.subgroupOf K) hinside
  rcases hcover.2 with hm | hj | hh
  · obtain ⟨⟨e⟩, ⟨d⟩⟩ := hm
    let e' : K ⧸ center K ≃* Sporadic.Mathieu.M12 :=
      (QuotientGroup.quotientMulEquivOfEq hZ).trans e
    let r := MulAut.centralQuotientAction e' a
    obtain ⟨hr, hor⟩ := model_action_data e' a ha ho
    rcases ht12 r hr with ht | ht
    · exact (hor ht.1).elim
    · obtain ⟨c⟩ := ht.2
      let := h.localSetup.component.quasisimple
      let := IsQuasisimple.of_mulEquiv d
      let := m12_product_residual
      exact fixed_residual_of_model b ((MulAut.fixedSubgroupCongr e' b).trans c)
  · obtain ⟨⟨e⟩, _⟩ := hj
    let e' : K ⧸ center K ≃* Sporadic.LeechRelated.J2.Carrier :=
      (QuotientGroup.quotientMulEquivOfEq hZ).trans e
    let r := MulAut.centralQuotientAction e' a
    obtain ⟨hr, hor⟩ := model_action_data e' a ha ho
    rcases htj2 r hr with ht | ht
    · exact (hor ht.1).elim
    · obtain ⟨c⟩ := ht.2
      let f := (MulAut.fixedSubgroupCongr e' b).trans c
      let := j2_automorphism_residual _ (hc.2.map_equiv f)
      exact fixed_residual_of_model b f
  · obtain ⟨⟨e⟩, hd⟩ := hh
    let e' : K ⧸ center K ≃* Sporadic.LeechRelated.HS.Carrier :=
      (QuotientGroup.quotientMulEquivOfEq hZ).trans e
    let r := MulAut.centralQuotientAction e' a
    obtain ⟨hr, hor⟩ := model_action_data e' a ha ho
    rcases hths r hr with ht | ht
    · exact (hor ht.1).elim
    · rcases ht.2 with hs | hext
      · obtain ⟨c⟩ := hs
        let f := (MulAut.fixedSubgroupCongr e' b).trans c
        let := hs_symmetric_residual _ (hc.2.map_equiv f)
        exact fixed_residual_of_model b f
      · have hd' : Nonempty (L.subgroupOf K ≃* JankoTwoHigmanSims.A6) ∨
            Nonempty (L.subgroupOf K ≃* JankoTwoHigmanSims.A8) := by
          rcases hd with hd | hd
          · obtain ⟨d⟩ := hd
            exact Or.inl ⟨(subgroupOfEquivOfLe hlt.le).trans d⟩
          · obtain ⟨d⟩ := hd
            exact Or.inr ⟨(subgroupOfEquivOfLe hlt.le).trans d⟩
        exact (not_elementaryExtension_of_alternating a e' (L.subgroupOf K)
          hinside.1 hd' hext).elim

end CFSG.Quasithin.Chapter16.EnlargementSieve.CoverExclusion
