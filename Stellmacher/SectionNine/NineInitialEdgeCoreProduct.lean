module
public import Stellmacher.SectionNine.LemmaNineThree
public import Stellmacher.SectionNine.CubicLocalAction

/-!
# The product of the initial adjacent cores

At critical distance greater than one in the ambient Section Nine setting,
the two cores of the initial edge generate its edge stabilizer. The initial
vertex core has index two in this stabilizer.

The initial-orbit classification (9.3) identifies the local quotient with
SL₂(2), so its cubic local action gives the edge/core index two. The next
residual-core noncontainment from (7.6)(b) excludes containment of the next
vertex core in the initial core. Their join therefore exhausts the index-two
extension. This is the edge-product assertion in the remark after (9.3),
printed p.50 of `refs/files/stellmacher-n-group.pdf`, and is used in the
index-two exclusion of (9.4)(4).
-/

namespace Stellmacher.SectionNine
open Later SectionsFiveToSeven CosetGraphContext SevenSix
universe u

public theorem nine_initial_edge_core_product
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : 1 < ctx.criticalPath.length) :
    QAt ctx.Γ ctx.criticalPath.a ⊔ QAt ctx.Γ ctx.criticalPath.firstStep =
      GAt ctx.Γ ctx.criticalPath.a ⊓ GAt ctx.Γ ctx.criticalPath.firstStep ∧
    QuotientCardEq (GAt ctx.Γ ctx.criticalPath.a ⊓ GAt ctx.Γ ctx.criticalPath.firstStep)
      (QAt ctx.Γ ctx.criticalPath.a) 2 := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let Qa := QAt Γ cp.a
  let Qn := QAt Γ cp.firstStep
  let edge := GAt Γ cp.a ⊓ GAt Γ cp.firstStep
  let joined := Qa ⊔ Qn
  have hmodel := (lemma_nine_three_ambient ctx hb cp.a ⟨1, Γ.act_one _⟩).1
  have hcard : Nat.card edge = 2 * Nat.card Qa :=
    (cubic_local_action_of_sl2Two_quotient Γ ctx.sectionSeven cp.a hmodel).edge_card
      cp.firstStep cp.firstStep_adj
  have hQa : Qa ≤ edge := (local_cores_le_edge_sylow ctx.sectionSeven Γ cp).1.trans
    cp.S_le_edge_stabilizers
  have hQn : Qn ≤ edge := (local_cores_le_edge_sylow ctx.sectionSeven Γ cp).2.trans
    cp.S_le_edge_stabilizers
  have hjoin : joined ≤ edge := sup_le hQa hQn
  have hnot : ¬ Qn ≤ Qa := by
    intro hle
    apply (lemma_seven_six ctx.sectionSeven Γ cp).next_residual_core.1
    apply le_trans ?_ hle
    change twoCoreIn (Γ.twoResidualAt cp.firstStep) ≤ Γ.twoCoreAt cp.firstStep
    rw [Γ.twoResidualAt_def, Γ.twoCoreAt_def, residual_core_eq_inter_core]
    exact inf_le_right
  have hindex : Qa.relIndex edge = 2 := by
    have hcount := (Qa.subgroupOf edge).index_mul_card
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQa).toEquiv] at hcount
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos (hcount.trans hcard)
  have hdiv : Qa.relIndex joined ∣ 2 := by
    rw [← hindex]
    exact dvd_of_mul_right_eq (joined.relIndex edge)
      (Subgroup.relIndex_mul_relIndex Qa joined edge le_sup_left hjoin)
  have hjoinIndex : Qa.relIndex joined = 2 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp hdiv with hone | htwo
    · exact False.elim (hnot (le_sup_right.trans (Subgroup.relIndex_eq_one.mp hone)))
    · exact htwo
  have hjoinCard : Nat.card joined = 2 * Nat.card Qa := by
    have hcount := (Qa.subgroupOf joined).index_mul_card
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (show Qa ≤ joined from le_sup_left)).toEquiv] at hcount
    change Qa.relIndex joined * Nat.card Qa = Nat.card joined at hcount
    rw [hjoinIndex] at hcount
    exact hcount.symm
  exact ⟨Subgroup.eq_of_le_of_card_ge hjoin (by rw [hcard, hjoinCard]), hcard⟩

end Stellmacher.SectionNine
