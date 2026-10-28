module
public import Stellmacher.SectionNine.NineTenTransvectionCoatom
public import Theory.GroupAction.SmallQuotientCentralization
public import Stellmacher.SectionNine.NineSevenNormalityObstructions

/-!
# The initial-center commutator is the retained cyclic displacement

For a commuting critical path of length greater than one, any supplied
initial-center actor outside the terminal core has the same terminal-module
commutator as the entire initial center. No transvection or extraction data
are assumed in this identity.

The first center has order two, lies in the initial center of order four,
and is contained in the terminal core by critical minimality. The supplied
actor is outside that line, so the line and actor generate the initial
center. By (7.4), terminal V normalizes the first center and therefore
centralizes this order-two group. Expanding a generator of the initial
center as an actor power times a first-center element identifies the two
commutator subgroups.

This identifies the literal R=[Z_a,V_a′] of Stellmacher (9.10), printed
pp.57–58, with the displacement of its retained transvection. It prevents
a later centralizing-neighbor theorem from silently replacing the source R
with an unrelated cyclic displacement.
-/

namespace Stellmacher.SectionNine
open Later SectionsFiveToSeven CosetGraphContext SevenSix
open scoped Pointwise commutatorElement
universe u

public theorem nine_ten_initial_center_commutator_eq_cyclic
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : 1 < ctx.criticalPath.length)
    (actor : G) (hactor : actor ∈ ZAt ctx.Γ ctx.criticalPath.a)
    (hnot : actor ∉ QAt ctx.Γ ctx.criticalPath.a') :
    ⁅ZAt ctx.Γ ctx.criticalPath.a,VAt ctx.Γ ctx.criticalPath.a'⁆ =
      ⁅VAt ctx.Γ ctx.criticalPath.a',Subgroup.zpowers actor⁆ := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let Za := ZAt Γ cp.a
  let Zf := ZAt Γ cp.firstStep
  let U := VAt Γ cp.a'
  let C := Subgroup.zpowers actor
  have hZacard : Nat.card Za = 4 := (lemma_nine_three_ambient ctx hb cp.a ⟨1,Γ.act_one _⟩).2
  have hZfcard : Nat.card Zf = 2 :=
    (nine_next_center_commutator_and_kernel ctx hb cp.firstStep ⟨1,Γ.act_one _⟩).1
  have hZfZa : Zf ≤ Za := ((nine_seven_center_join ctx cp.a ⟨1,Γ.act_one _⟩).2
    cp.firstStep ((mem_neighborhood_iff_adjacent Γ).mpr cp.firstStep_adj)).2
  have hZfCore : Zf ≤ QAt Γ cp.a' := by
    have hlength : 1 < cp.length := hb
    apply critical_minimality Γ cp
    have hh := path_distance_le Γ cp 1 cp.length (by omega) le_rfl
    rw [cp.path_first,cp.path_end] at hh
    omega
  have hactorNotZf : actor ∉ Zf := fun hm => hnot (hZfCore hm)
  have hCZa : C ≤ Za := Subgroup.zpowers_le.mpr hactor
  have hindex : Zf.relIndex Za = 2 := by
    have hh := (Zf.subgroupOf Za).index_mul_card
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZfZa).toEquiv,hZfcard,hZacard] at hh
    change Zf.relIndex Za * 2 = 4 at hh
    omega
  have hgen : Za = C ⊔ Zf := by
    have hle : C ⊔ Zf ≤ Za := sup_le hCZa hZfZa
    have hh := Subgroup.relIndex_mul_relIndex Zf (C ⊔ Zf) Za le_sup_right hle
    rw [hindex] at hh
    have hpos : 0 < Zf.relIndex (C ⊔ Zf) :=
      Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
    have hne : Zf.relIndex (C ⊔ Zf) ≠ 1 := by
      intro hone
      exact hactorNotZf (Subgroup.relIndex_eq_one.mp hone
        (Subgroup.mem_sup_left (Subgroup.mem_zpowers actor)))
    have hjpos : 0 < (C ⊔ Zf).relIndex Za :=
      Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
    have htwo : 2 ≤ Zf.relIndex (C ⊔ Zf) := by omega
    have hone : (C ⊔ Zf).relIndex Za = 1 := by nlinarith
    exact le_antisymm (Subgroup.relIndex_eq_one.mp hone) hle
  have hUZf : U ≤ Subgroup.normalizer (Zf : Set G) :=
    (lemma_seven_four ctx.sectionSeven Γ cp).reverse_containment.2.trans
      (stabilizer_le_normalizer_z Γ cp.firstStep)
  let botG : Subgroup G := ⊥
  let hN : (botG.subgroupOf Zf).Normal := by dsimp [botG]; infer_instance
  let _ := hN
  have hquotient : Nat.card (Zf ⧸ botG.subgroupOf Zf) ≤ 2 := by
    have hh := Subgroup.card_eq_card_quotient_mul_card_subgroup (botG.subgroupOf Zf)
    have hbot : botG.subgroupOf Zf = ⊥ := Subgroup.bot_subgroupOf Zf
    rw [hbot,Subgroup.card_bot,mul_one,hZfcard] at hh
    rw [hbot]
    exact hh.symm.le
  have hZfU : ⁅Zf,U⁆ = ⊥ := le_bot_iff.mp
    (Subgroup.commutator_le_of_normalized_quotient_card_le_two U Zf botG hUZf
      (by exact Subgroup.le_normalizer_of_normal) hN hquotient)
  have hQfirstP : QAt Γ cp.firstStep ≤ GAt Γ cp.firstStep := by
    change Γ.twoCoreAt cp.firstStep ≤ Γ.vertexStabilizer cp.firstStep
    rw [Γ.twoCoreAt_def]
    exact twoCoreIn_le _
  have hCZf : C ≤ Subgroup.normalizer (Zf : Set G) :=
    (hCZa.trans (lemma_seven_four ctx.sectionSeven Γ cp).first_containment.1).trans
      ((nine_seven_module_le_own_core ctx.toLocalContext hb cp.firstStep).trans
        (hQfirstP.trans (stabilizer_le_normalizer_z Γ cp.firstStep)))
  apply le_antisymm
  · apply Subgroup.commutator_le.mpr
    intro z hz u hu
    change z ∈ Za at hz
    rw [hgen] at hz
    have hzprod : z ∈ (C:Set G)*(Zf:Set G) := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right C Zf hCZf]
      exact hz
    obtain ⟨c,hc,f,hf,rfl⟩ := hzprod
    have hfcomm : ⁅f,u⁆ = 1 := by
      have hh := Subgroup.commutator_mem_commutator hf hu
      rw [hZfU,Subgroup.mem_bot] at hh
      exact hh
    rw [commutatorElement_mul_left_eq_conj_mul,hfcomm,mul_one,mul_inv_cancel,one_mul]
    rw [Subgroup.commutator_comm]
    exact Subgroup.commutator_mem_commutator hc hu
  · rw [Subgroup.commutator_comm]
    exact Subgroup.commutator_mono hCZa le_rfl

end Stellmacher.SectionNine
