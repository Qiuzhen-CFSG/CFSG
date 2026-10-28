module
public import Stellmacher.SectionNine.NineNextTransvectionActor
public import Stellmacher.SectionNine.NineFiveRecognitionReduction
public import Theory.GroupTheory.PCoreKernelRange

/-!
# The order-eight terminal quotient in (9.5)

A next-orbit neighbor module of order eight has quotient of order four by
its central line. If a local actor has the prescribed index-two displacement,
its image in the literal faithful action is a nontrivial involution. The
action range therefore has even order, and its two-core is trivial because
the action kernel is exactly the local two-core. Faithful action on the
four-element module identifies the range with SL₂(2). Composing this
identification with the given action retains the required two-core kernel.

This proves the quotient-model part of Stellmacher (9.5)(a), printed
pp.52–53 of the Journal of Algebra 190 (1997) paper. The module order is an
explicit input here; its derivation and the order-thirty-two alternative
belong to the support construction in the numbered theorem.
-/

namespace Stellmacher.SectionNine
open Later SectionsFiveToSeven CosetGraphContext
universe u

public theorem nine_five_small_model
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : 1 < ctx.criticalPath.length) (vertex : ctx.Γ.Vertex)
    (horbit : IsConjugateVertex ctx.Γ ctx.criticalPath.firstStep vertex)
    (actor : GAt ctx.Γ vertex)
    (hindex : QuotientCardEq
      (⁅VAt ctx.Γ vertex, Subgroup.zpowers (actor : G)⁆ ⊔ ZAt ctx.Γ vertex)
      (ZAt ctx.Γ vertex) 2)
    (hcard : Nat.card (VAt ctx.Γ vertex) = 8) :
    QuotientIsModel (GAt ctx.Γ vertex) (QAt ctx.Γ vertex) SL2Two := by
  obtain ⟨hN, hW, action, _, hkernel, hinvolution, hactorCard, _⟩ :=
    nine_next_transvection_actor ctx hb vertex horbit actor hindex
  let _ := hN
  let _ := hW
  let P := GAt ctx.Γ vertex
  let U := VAt ctx.Γ vertex
  let Z := ZAt ctx.Γ vertex
  let W := U ⧸ Z.subgroupOf U
  have hdata := nine_next_center_commutator_and_kernel ctx hb vertex horbit
  have hQP : QAt ctx.Γ vertex ≤ P := by
    rw [QAt, q, ctx.Γ.twoCoreAt_def]
    exact Subgroup.map_subtype_le _
  have hZU : Z ≤ U := by
    rw [show Z = ZAt ctx.Γ vertex from rfl, ← hdata.2.1]
    exact Subgroup.le_normalizer_iff_commutator_le_left.mp
      (hQP.trans (stabilizer_le_normalizer_v ctx.Γ vertex))
  have hZcard : Nat.card (Z.subgroupOf U) = 2 :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZU).toEquiv).trans hdata.1
  have hWcard : Nat.card W = 4 := by
    have hprod := Subgroup.card_eq_card_quotient_mul_card_subgroup (Z.subgroupOf U)
    change Nat.card U = Nat.card W * Nat.card (Z.subgroupOf U) at hprod
    rw [hZcard] at hprod
    change Nat.card (VAt ctx.Γ vertex) = Nat.card W * 2 at hprod
    rw [hcard] at hprod
    omega
  have hfaithful : fixingSubgroup action.range (Set.univ : Set W) = ⊥ := by
    apply bot_unique
    intro mover hmover
    apply Subtype.ext
    ext point
    exact ((mem_fixingSubgroup_iff action.range).mp hmover) point (Set.mem_univ point)
  have hinvolutionRange : _root_.IsInvolution (action.rangeRestrict actor) :=
    ⟨fun heq => hinvolution.1 (congrArg Subtype.val heq), Subtype.ext hinvolution.2⟩
  have htwo : Nat.card (Subgroup.zpowers (action.rangeRestrict actor)) = 2 := by
    rw [Nat.card_zpowers, orderOf_eq_prime hinvolutionRange.2 hinvolutionRange.1]
  have heven : Even (Nat.card action.range) := by
    apply even_iff_two_dvd.mpr
    rw [← htwo]
    exact Subgroup.card_subgroup_dvd_card _
  obtain ⟨equiv⟩ := nine_five_sl2_of_faithful_card_four hfaithful hWcard heven
    (pCore_range_eq_bot_of_ker_eq_pCore 2 action hkernel)
  refine ⟨equiv.toMonoidHom.comp action.rangeRestrict,
    equiv.surjective.comp action.rangeRestrict_surjective, ?_⟩
  rw [MonoidHom.ker_comp_of_injective _ _ equiv.injective,
    MonoidHom.ker_rangeRestrict, hkernel]
  change pCore 2 P = (ctx.Γ.twoCoreAt vertex).subgroupOf P
  rw [ctx.Γ.twoCoreAt_def]
  exact (Subgroup.comap_map_eq_self_of_injective P.subtype_injective _).symm

end Stellmacher.SectionNine
