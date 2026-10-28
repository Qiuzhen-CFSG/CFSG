module

public import CFSG.Quasithin.Chapter16.Section03.EnlargementSieve.SquareLifts.CoverExclusion.TableInputs
public import CFSG.Quasithin.Chapter16.Section03.EnlargementSieve.SquareLifts.CoverExclusion.InnerMark.Models

/-!
# The inner sporadic-cover action is not two-central

The actual component maps to a component of the full fixed subgroup of the
central quotient. The center equals the two-core, so the supplied sporadic
carrier equivalence transports this action to the table's concrete carrier.
M₁₂ and J₂ then use their component-index deductions. In HS, the A₆ or A₈
component embeds through the central quotient because its center is trivial;
its order excludes the kernel row, and the product row has even index.

The only explicit source premises are the literal M₁₂ and HS rows of
16.1.5(4),(10). No mark, component exclusion, index bound, or kernel-action
condition is an input. The J₂ inner row and its action calculation are proved.
This establishes the `inner_mark` obligation of `TableReduction`; source-table
assembly and the separate outer branch remain with their owners.

Source: Aschbacher–Smith, 16.1.5(4),(8),(10), pp.1171–1172, and the inner
branch of 16.3.11(3), p.1181, combined manuscript of 1 March 2004.
-/

public section
namespace CFSG.Quasithin.Chapter16.EnlargementSieve.CoverExclusion
open Subgroup Theory.GroupTheory Theory.GroupTheory.DoubleCoverCentralizer
open ComponentTransfer.Intrinsic OtherPreliminaries

namespace InnerMark
variable {H M : Type*} [Group H] [Group M]

private theorem model_component (a : MulAut H) {J : Subgroup H}
    (hJ : IsComponentIn J a.fixedSubgroup) (e : (H ⧸ center H) ≃* M) :
    ∃ C : Subgroup (MulAut.centralQuotientAction e a).fixedSubgroup,
      IsComponent (MulAut.centralQuotientAction e a).fixedSubgroup C := by
  have hc := MulAut.component_image_in_quotient_fixed a J hJ
  let f := MulAut.fixedSubgroupCongr e ((center H).quotientAut a)
  exact ⟨_, hc.2.map_equiv f⟩

private def modelFixedHom (a : MulAut H) {J : Subgroup H}
    (hJ : IsComponentIn J a.fixedSubgroup) (e : (H ⧸ center H) ≃* M) :
    J →* (MulAut.centralQuotientAction e a).fixedSubgroup where
  toFun x := ⟨e (QuotientGroup.mk' (center H) x), by
    rw [MulAut.mem_fixedSubgroup, MulAut.centralQuotientAction_apply,
      (MulAut.mem_fixedSubgroup a x).mp (hJ.1 x.property)]⟩
  map_one' := Subtype.ext (by simp)
  map_mul' x y := Subtype.ext (by simp)

private theorem modelFixedHom_injective (a : MulAut H) {J : Subgroup H}
    (hJ : IsComponentIn J a.fixedSubgroup) (e : (H ⧸ center H) ≃* M)
    (hZ : center J = ⊥) : Function.Injective (modelFixedHom a hJ e) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply le_bot_iff.mp
  intro x hx
  have he : e (QuotientGroup.mk' (center H) (x : H)) = 1 :=
    congrArg Subtype.val (show modelFixedHom a hJ e x = 1 from hx)
  have hxZ : (x : H) ∈ center H := (QuotientGroup.eq_one_iff _).mp
    (e.injective (he.trans e.map_one.symm))
  have hxJ : x ∈ center J := mem_center_iff.mpr fun y =>
    Subtype.ext (mem_center_iff.mp hxZ (y : H))
  simpa only [hZ, mem_bot] using hxJ

private theorem hs_of_component_order [Finite H] [Group.IsPerfect H]
    (a : MulAut H) (ha : orderOf a = 2) {J : Subgroup H}
    (hJ : IsComponentIn J a.fixedSubgroup)
    (e : (H ⧸ center H) ≃* Sporadic.LeechRelated.HS.Carrier)
    (hZ : center J = ⊥) (h9 : 9 ∣ Nat.card J)
    (ht : ∀ r : MulAut Sporadic.LeechRelated.HS.Carrier, orderOf r = 2 →
      JankoTwoHigmanSims.HSInvolutionAlternative r)
    (k : H) (hk : a = MulAut.conj k) :
    ¬ TwoCentral (QuotientGroup.mk' (center H) k) := by
  let r := MulAut.centralQuotientAction e a
  have hr : orderOf r = 2 :=
    (orderOf_injective _ (MulAut.centralQuotientAction_injective e) a).trans ha
  have hi : r = MulAut.conj (e (QuotientGroup.mk' (center H) k)) := by
    change MulAut.centralQuotientAction e a = _
    rw [hk, MulAut.centralQuotientAction_conj]
  exact fun hu => hs_not_twoCentral r (ht r hr) (modelFixedHom a hJ e)
    (modelFixedHom_injective a hJ e hZ) h9 _ hi (hu.map e)

private theorem alternating_center_eq_bot {J : Type*} [Group J] {n : ℕ}
    (hn : 4 ≤ n) (e : J ≃* alternatingGroup (Fin n)) : center J = ⊥ := by
  apply (eq_bot_iff_card (center J)).mpr
  rw [Nat.card_congr (centerCongr e).toEquiv,
    alternatingGroup.center_eq_bot (by simpa using hn)]
  simp

end InnerMark

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {z t : G} {L : Subgroup G}

/-- The inner field of `TableReduction`, derived from the actual source setup
and the literal earlier M₁₂ and HS table rows. No lifting theorem is used. -/
theorem inner_mark_of_tables
    (hm12 : ∀ r : MulAut Sporadic.Mathieu.M12, orderOf r = 2 →
      Mathieu.M12InvolutionAlternative r)
    (hhs : ∀ r : MulAut Sporadic.LeechRelated.HS.Carrier, orderOf r = 2 →
      JankoTwoHigmanSims.HSInvolutionAlternative r)
    {𝒦 : GroupClass} (hG : Hypothesis1611 𝒦 G)
    (h : TerminalCounterexample T z L t)
    (hK : IsCentralizerComponent t (enlargement t L))
    (hL : ComponentTransfer.IsComponentIn L
      (ComponentTransfer.centralizerIn (enlargement t L) z))
    (hlt : L < enlargement t L)
    (hcover : SporadicCoverAlternative (enlargement t L) L) :
    ∀ k : enlargement t L, action (original_normalizes_enlargement h hK) = MulAut.conj k →
      ¬ TwoCentral (QuotientGroup.mk' (center (enlargement t L)) k) := by
  let H := enlargement t L
  let hn := original_normalizes_enlargement h hK
  let a := action hn
  let J := L.subgroupOf H
  let := hK.quasisimple
  have ha : orderOf a = 2 :=
    action_order h.localSetup.involution hn h.localSetup.component hlt
  have hJ : IsComponentIn J a.fixedSubgroup := componentInside_fixed hn hL
  let q := QuotientGroup.quotientMulEquivOfEq
    (hG.evenType.component_center_eq_twoCore h.involution hK)
  intro k hk
  change a = MulAut.conj k at hk
  rcases hcover.2 with ⟨⟨e⟩, _⟩ | ⟨⟨e⟩, _⟩ | ⟨⟨e⟩, hmodels⟩
  · let e' := q.trans e
    let r := MulAut.centralQuotientAction e' a
    have hr : orderOf r = 2 :=
      (orderOf_injective _ (MulAut.centralQuotientAction_injective e') a).trans ha
    obtain ⟨C, hC⟩ := InnerMark.model_component a hJ e'
    have hi : r = MulAut.conj (e' (QuotientGroup.mk' (center H) k)) := by
      change MulAut.centralQuotientAction e' a = _
      rw [hk, MulAut.centralQuotientAction_conj]
    exact fun hu => InnerMark.m12_not_twoCentral r (hm12 r hr) C hC _ hi (hu.map e')
  · let e' := q.trans e
    let r := MulAut.centralQuotientAction e' a
    have hr : orderOf r = 2 :=
      (orderOf_injective _ (MulAut.centralQuotientAction_injective e') a).trans ha
    obtain ⟨C, hC⟩ := InnerMark.model_component a hJ e'
    have hi : r = MulAut.conj (e' (QuotientGroup.mk' (center H) k)) := by
      change MulAut.centralQuotientAction e' a = _
      rw [hk, MulAut.centralQuotientAction_conj]
    exact fun hu => InnerMark.j2_not_twoCentral r hr C hC _ hi (hu.map e')
  · apply InnerMark.hs_of_component_order a ha hJ (q.trans e) _ _ hhs k hk
    · rcases hmodels with h6 | h8
      · obtain ⟨eL⟩ := h6
        exact InnerMark.alternating_center_eq_bot (by decide : 4 ≤ 6)
          ((subgroupOfEquivOfLe hlt.le).trans eL)
      · obtain ⟨eL⟩ := h8
        exact InnerMark.alternating_center_eq_bot (by decide : 4 ≤ 8)
          ((subgroupOfEquivOfLe hlt.le).trans eL)
    · rcases hmodels with h6 | h8
      · obtain ⟨eL⟩ := h6
        rw [Nat.card_congr ((subgroupOfEquivOfLe hlt.le).trans eL).toEquiv,
          nat_card_alternatingGroup, Nat.card_fin]
        decide
      · obtain ⟨eL⟩ := h8
        rw [Nat.card_congr ((subgroupOfEquivOfLe hlt.le).trans eL).toEquiv,
          nat_card_alternatingGroup, Nat.card_fin]
        decide

end CFSG.Quasithin.Chapter16.EnlargementSieve.CoverExclusion
