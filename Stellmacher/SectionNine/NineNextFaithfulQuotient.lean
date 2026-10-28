module
public import Stellmacher.SectionNine.LemmaNineThree
public import Stellmacher.SectionNine.NineNextCenterCommutator
public import Stellmacher.SectionNine.NineNextVModule

/-!
# The faithful next-orbit quotient module after (9.3)

For every vertex in the first-step orbit at critical distance greater than
one, the center has order two and is exactly the commutator of the neighbor
module with the local two-core. The literal conjugation action on V_d/Z_d
has kernel O₂(G_d), so it descends faithfully to the local core quotient.
Both the ambient Hypothesis Two carrier and the graph carrier are retained.

The proved initial-orbit classification supplies the center order needed
by the existing next-center and quotient-kernel reductions. We construct
the action with its exact formula. Its kernel criterion is checked in both
directions: the core commutator vanishes on the quotient, while a trivial
quotient actor centralizes modulo the center and hence belongs to the core.
The quotient module is elementary abelian as an image of V_d.

Source: Stellmacher, Journal of Algebra 190 (1997), the remark after (9.3),
printed p.50/PDF p.40 of `refs/files/stellmacher-n-group.pdf`. This action is
used by the transvection factor arguments beginning with (9.4).
-/

namespace Stellmacher.SectionNine
open Later SectionsFiveToSeven CosetGraphContext
open scoped commutatorElement IsMulCommutative
universe u

public theorem nine_next_center_commutator_and_kernel
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : 1 < ctx.criticalPath.length) (vertex : ctx.Γ.Vertex)
    (horbit : IsConjugateVertex ctx.Γ ctx.criticalPath.firstStep vertex) :
    Nat.card (ZAt ctx.Γ vertex) = 2 ∧
      ⁅VAt ctx.Γ vertex, QAt ctx.Γ vertex⁆ = ZAt ctx.Γ vertex ∧
      (∀ actor : G, actor ∈ GAt ctx.Γ vertex →
        (⁅VAt ctx.Γ vertex, Subgroup.zpowers actor⁆ ≤ ZAt ctx.Γ vertex ↔
          actor ∈ QAt ctx.Γ vertex)) := by
  obtain ⟨hcard, hcomm⟩ := nine_next_center_and_commutator_of_initial_model
    ctx hb (lemma_nine_three_ambient ctx hb) vertex horbit
  exact nine_next_v_module_kernel_of_center_and_commutator ctx hb vertex horbit hcard hcomm

public theorem nine_next_quotient_conjugation_action
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : 1 < ctx.criticalPath.length) (vertex : ctx.Γ.Vertex)
    (horbit : IsConjugateVertex ctx.Γ ctx.criticalPath.firstStep vertex) :
    ∃ hN : ((ZAt ctx.Γ vertex).subgroupOf (VAt ctx.Γ vertex)).Normal,
      let _ := hN
      let P := GAt ctx.Γ vertex
      let U := VAt ctx.Γ vertex
      let Z := ZAt ctx.Γ vertex
      IsElementaryAbelian 2 (U ⧸ Z.subgroupOf U) ∧
      ∃ action : P →* MulAut (U ⧸ Z.subgroupOf U),
        (∀ actor : P, ∀ point : U,
          action actor (QuotientGroup.mk' (Z.subgroupOf U) point) =
            QuotientGroup.mk' (Z.subgroupOf U)
              ⟨(actor : G) * (point : G) * (actor : G)⁻¹,
                (Subgroup.mem_normalizer_iff.mp
                  (stabilizer_le_normalizer_v ctx.Γ vertex actor.property) point).mp
                    point.property⟩) ∧
        action.ker = pCore 2 P := by
  classical
  let P := GAt ctx.Γ vertex
  let U := VAt ctx.Γ vertex
  let Z := ZAt ctx.Γ vertex
  have hU : IsElementaryAbelian 2 U := by
    obtain ⟨actor, rfl⟩ := horbit
    let _ := ((lemma_seven_five ctx.sectionSeven ctx.Γ ctx.criticalPath
      ctx.commutator_eq).longer_case hb).1
    change IsElementaryAbelian 2 (v ctx.Γ (ctx.Γ.act actor ctx.criticalPath.firstStep))
    rw [v_act]
    exact IsElementaryAbelian.map (MulAut.conj actor⁻¹).toMonoidHom
  let _ := hU
  let _ : IsMulCommutative U := inferInstance
  have hN : (Z.subgroupOf U).Normal := inferInstance
  let _ := hN
  let W := U ⧸ Z.subgroupOf U
  have hW : IsElementaryAbelian 2 W := {
    toIsMulCommutative := ⟨⟨fun first second => by
      obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective (Z.subgroupOf U) first
      obtain ⟨b, rfl⟩ := QuotientGroup.mk'_surjective (Z.subgroupOf U) second
      rw [← map_mul, ← map_mul, mul_comm]⟩⟩
    exponent_dvd_p := by
      apply Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
      intro point
      obtain ⟨representative, rfl⟩ := QuotientGroup.mk'_surjective (Z.subgroupOf U) point
      rw [← map_pow, Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p 2 U) representative, map_one] }
  have hPU : P ≤ Subgroup.normalizer (U : Set G) := stabilizer_le_normalizer_v ctx.Γ vertex
  obtain ⟨action, haction⟩ := Subgroup.exists_quotient_conjugation_action P U Z hPU
    (stabilizer_le_normalizer_z ctx.Γ vertex) hN
  have hdata := nine_next_center_commutator_and_kernel ctx hb vertex horbit
  have hcore : (QAt ctx.Γ vertex).subgroupOf P = pCore 2 P := by
    change (ctx.Γ.twoCoreAt vertex).subgroupOf P = _
    rw [ctx.Γ.twoCoreAt_def]
    exact Subgroup.comap_map_eq_self_of_injective P.subtype_injective _
  refine ⟨hN, hW, action, haction, le_antisymm ?_ ?_⟩
  · intro actor hactor
    rw [← hcore]
    apply (hdata.2.2 actor actor.property).mp
    apply Subgroup.commutator_le.mpr
    intro point hpoint other hother
    have hotherP : other ∈ P := (Subgroup.zpowers_le.mpr actor.property) hother
    let otherP : P := ⟨other, hotherP⟩
    have hotherKer : otherP ∈ action.ker := by
      obtain ⟨power, hpower⟩ := hother
      have heq : otherP = actor ^ power := Subtype.ext hpower.symm
      rw [heq]
      exact action.ker.zpow_mem hactor power
    have heq := congrArg (fun aut : MulAut W =>
      aut (QuotientGroup.mk' (Z.subgroupOf U) ⟨point, hpoint⟩))
      (MonoidHom.mem_ker.mp hotherKer)
    rw [haction] at heq
    have hdiv := QuotientGroup.eq_iff_div_mem.mp heq
    change other * point * other⁻¹ / point ∈ Z at hdiv
    simpa only [div_eq_mul_inv, mul_inv_rev, inv_inv, commutatorElement_def, mul_assoc]
      using Z.inv_mem hdiv
  · rw [← hcore]
    exact Subgroup.quotient_conjugation_action_kills_commutator_layer P U Z
      (QAt ctx.Γ vertex) hN hPU hdata.2.1.le action haction

end Stellmacher.SectionNine
