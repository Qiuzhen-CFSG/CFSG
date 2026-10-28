module

public import Stellmacher.SectionNine.NineThreeOrbitModuleCentralizer
public import Theory.GroupAction.SubgroupQuotientFullAction

/-!
# The faithful next-neighbor quotient-module reduction

The kernel of the literal quotient conjugation action is a normal two-group
when its discrepancies lie in a pointwise-fixed subgroup of exponent two and
the full module centralizer lies in the local two-core. Indeed, the square of
each kernel element centralizes the module. This proves the kernel bound,
rather than assuming faithfulness of the quotient action.

In the ambient Section Nine context, (7.5) supplies the fixed next center and
the elementary abelian neighbor module, and the genuine ambient (7.7)(b)
centralizer theorem supplies the core bound. The final wrapper is conditional
on the next-center order and commutator identity; it is not the unconditional
remark after (9.3). The geometric producer and (9.3) assembly remain separate.

Source: `refs/files/stellmacher-n-group.pdf`, printed p.50/PDF p.40, the
remark immediately following (9.3).
-/

namespace Stellmacher.SectionNine
open Later SectionsFiveToSeven CosetGraphContext
open scoped commutatorElement
universe u

public theorem quotient_layer_kernel_le_twoCore
    {G : Type u} [Group G] [Finite G]
    (P U Z : Subgroup G)
    (hPU : P ≤ Subgroup.normalizer (U : Set G))
    (hPZ : P ≤ Subgroup.normalizer (Z : Set G))
    (hN : (Z.subgroupOf U).Normal)
    (hfix : P ≤ Subgroup.centralizer (Z : Set G))
    (hpow : ∀ vector ∈ Z, vector ^ 2 = 1)
    (hcent : Subgroup.centralizer (U : Set G) ≤ twoCoreIn P)
    (actor : G) (hactor : actor ∈ P)
    (hcomm : ⁅U, Subgroup.zpowers actor⁆ ≤ Z) :
    actor ∈ twoCoreIn P := by
  let _ := hN
  obtain ⟨ρ, hρ⟩ := Subgroup.exists_quotient_conjugation_action P U Z hPU hPZ hN
  have hsquare (element : ρ.ker) : (element.val.val) ^ 2 ∈ twoCoreIn P := by
    apply hcent
    rw [Subgroup.mem_centralizer_iff]
    intro vector hvector
    let discrepancy := element.val.val * vector * element.val.val⁻¹ * vector⁻¹
    have hd : discrepancy ∈ Z := by
      have heq := congrArg (fun aut : MulAut (U ⧸ Z.subgroupOf U) =>
        aut (QuotientGroup.mk' (Z.subgroupOf U) ⟨vector, hvector⟩))
        (MonoidHom.mem_ker.mp element.property)
      rw [hρ] at heq
      have hh := QuotientGroup.eq_iff_div_mem.mp heq
      change element.val.val * vector * element.val.val⁻¹ / vector ∈ Z at hh
      simpa only [div_eq_mul_inv] using hh
    have hcommute := Subgroup.mem_centralizer_iff.mp (hfix element.val.property)
      discrepancy hd
    have htwo := hpow discrepancy hd
    have hconj : element.val.val * vector * element.val.val⁻¹ = discrepancy * vector := by
      dsimp [discrepancy]
      group
    have hdouble : element.val.val ^ 2 * vector * (element.val.val ^ 2)⁻¹ = vector := by
      calc
        _ = element.val.val * (element.val.val * vector * element.val.val⁻¹) *
            element.val.val⁻¹ := by simp only [pow_two]; group
        _ = element.val.val * (discrepancy * vector) * element.val.val⁻¹ := by rw [hconj]
        _ = discrepancy * (element.val.val * vector * element.val.val⁻¹) := by
          rw [← mul_assoc, ← hcommute]
          group
        _ = discrepancy ^ 2 * vector := by rw [hconj]; simp only [pow_two, mul_assoc]
        _ = vector := by rw [htwo, one_mul]
    exact (mul_inv_eq_iff_eq_mul.mp hdouble).symm
  have hkernel : IsPGroup 2 ρ.ker := by
    intro element
    obtain ⟨coreElement, hcoreElement, heq⟩ := hsquare element
    obtain ⟨power, hpower⟩ := (pCore_isPGroup (p := 2) (G := P))
      ⟨coreElement, hcoreElement⟩
    refine ⟨power + 1, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    have hp := congrArg (fun value : pCore 2 P => (value : G)) hpower
    change coreElement.val ^ (2 ^ power) = 1 at hp
    change coreElement.val = element.val.val ^ 2 at heq
    rw [heq] at hp
    change element.val.val ^ (2 ^ (power + 1)) = 1
    rw [pow_succ, Nat.mul_comm, pow_mul]
    exact hp
  have hle : ρ.ker ≤ pCore 2 P := le_sSup ⟨inferInstance, hkernel⟩
  have hmem : (⟨actor, hactor⟩ : P) ∈ ρ.ker :=
    Subgroup.quotient_conjugation_action_kills_commutator_layer P U Z
      (Subgroup.zpowers actor) hN hPU hcomm ρ hρ (Subgroup.mem_zpowers actor)
  exact Subgroup.mem_map_of_mem P.subtype (hle hmem)

public theorem nine_next_center_centralizes_stabilizer
    {G : Type u} [Group G] [Finite G] {T A B : Subgroup G}
    (ctx : SectionNineLocalContext G T A B)
    (vertex : ctx.Γ.Vertex)
    (horbit : IsConjugateVertex ctx.Γ ctx.criticalPath.firstStep vertex) :
    GAt ctx.Γ vertex ≤ Subgroup.centralizer (ZAt ctx.Γ vertex : Set G) := by
  apply Subgroup.le_centralizer_iff.mpr
  obtain ⟨actor, rfl⟩ := horbit
  change z ctx.Γ (ctx.Γ.act actor ctx.criticalPath.firstStep) ≤
    Subgroup.centralizer (stabilizer ctx.Γ (ctx.Γ.act actor ctx.criticalPath.firstStep) : Set G)
  rw [z_act, stabilizer_act]
  apply (Subgroup.map_mono (show z ctx.Γ ctx.criticalPath.firstStep ≤
    Subgroup.centralizer (stabilizer ctx.Γ ctx.criticalPath.firstStep : Set G) from ?_)).trans
    (Subgroup.map_centralizer_le_centralizer_image _ _)
  rw [(lemma_seven_five ctx.sectionSeven ctx.Γ ctx.criticalPath ctx.commutator_eq).next_center.2]
  exact (SevenSix.omegaOneCenter_le_centerAmbient _).trans
    (SevenSix.centerAmbient_le_centralizer _)

public theorem nine_next_v_module_kernel_of_center_and_commutator
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : 1 < ctx.criticalPath.length) (vertex : ctx.Γ.Vertex)
    (horbit : IsConjugateVertex ctx.Γ ctx.criticalPath.firstStep vertex)
    (hcard : Nat.card (ZAt ctx.Γ vertex) = 2)
    (hcomm : ⁅VAt ctx.Γ vertex, QAt ctx.Γ vertex⁆ = ZAt ctx.Γ vertex) :
    Nat.card (ZAt ctx.Γ vertex) = 2 ∧
      ⁅VAt ctx.Γ vertex, QAt ctx.Γ vertex⁆ = ZAt ctx.Γ vertex ∧
      (∀ actor : G, actor ∈ GAt ctx.Γ vertex →
        (⁅VAt ctx.Γ vertex, Subgroup.zpowers actor⁆ ≤ ZAt ctx.Γ vertex ↔
          actor ∈ QAt ctx.Γ vertex)) := by
  have helementary : IsElementaryAbelian 2 (VAt ctx.Γ vertex) := by
    obtain ⟨actor, rfl⟩ := horbit
    let _ := ((lemma_seven_five ctx.sectionSeven ctx.Γ ctx.criticalPath
      ctx.commutator_eq).longer_case hb).1
    change IsElementaryAbelian 2 (v ctx.Γ (ctx.Γ.act actor ctx.criticalPath.firstStep))
    rw [v_act]
    exact IsElementaryAbelian.map (MulAut.conj actor⁻¹).toMonoidHom
  let _ := helementary
  let _ : IsMulCommutative (VAt ctx.Γ vertex) := inferInstance
  have hnormal : ((ZAt ctx.Γ vertex).subgroupOf (VAt ctx.Γ vertex)).Normal := inferInstance
  refine ⟨hcard, hcomm, ?_⟩
  intro actor hactor
  constructor
  · have hcoreEq : QAt ctx.Γ vertex = twoCoreIn (GAt ctx.Γ vertex) :=
      ctx.Γ.twoCoreAt_def vertex
    rw [hcoreEq]
    apply quotient_layer_kernel_le_twoCore (GAt ctx.Γ vertex) (VAt ctx.Γ vertex)
      (ZAt ctx.Γ vertex) (stabilizer_le_normalizer_v ctx.Γ vertex)
      (stabilizer_le_normalizer_z ctx.Γ vertex) hnormal
      (nine_next_center_centralizes_stabilizer ctx.toLocalContext vertex horbit)
      (fun vector hvector => ?_)
      ((nine_three_module_centralizer_core_at_vertex ctx vertex horbit).trans_eq hcoreEq)
      actor hactor
    have hp := pow_card_eq_one' (x := (⟨vector, hvector⟩ : ZAt ctx.Γ vertex))
    rw [hcard] at hp
    exact congrArg Subtype.val hp
  · intro hcore
    rw [← hcomm]
    exact Subgroup.commutator_mono le_rfl (Subgroup.zpowers_le.mpr hcore)

end Stellmacher.SectionNine
