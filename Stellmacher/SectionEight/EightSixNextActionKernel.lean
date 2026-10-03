module
public import Stellmacher.SectionEight.EightSixNextQuotientModule
public import Theory.GroupTheory.PGroup.QuotientActionKernel
/-!
# The exact next quotient-action kernel when its core is V

In the actual Section Eight local graph, suppose the next two-core equals
its neighbor-generated subgroup V. The first commutator identity then
identifies the next central line with the derived subgroup of V. For the
supplied literal conjugation action on V/Z whose kernel contains the
next two-core, the kernel is exactly that core.

The derived subgroup lies in the Frattini subgroup of the finite two-group
V. Characteristic-two self-centralization puts the original conjugation
kernel inside the two-core. Burnside's Frattini kernel theorem, via the
quotient-action transfer, makes the quotient kernel a two-group. Its
normality then puts it inside the two-core, proving equality.

This gives the exact faithful quotient used in Stellmacher (8.6)(20)–(21),
printed p.45. The high-cost core-equality theorem supplies the equality
hypothesis in the source-(21) assembly; no independent faithfulness or
model assumption is made here.
-/

namespace Stellmacher.SectionEight
open Later SectionsFiveToSeven CosetGraphContext SevenSix
universe u
public theorem eight_six_next_quotient_action_kernel_of_core_eq_v
    {G : Type u} [Group G] [Finite G] {S P1 P2 : Subgroup G}
    (ctx : SectionEightLocalContext G S P1 P2)
    (hRV : QAt ctx.Γ ctx.criticalPath.firstStep = VAt ctx.Γ ctx.criticalPath.firstStep)
    (hcomm : ⁅VAt ctx.Γ ctx.criticalPath.firstStep,
      QAt ctx.Γ ctx.criticalPath.firstStep⁆ = ZAt ctx.Γ ctx.criticalPath.firstStep)
    (hN : ((ZAt ctx.Γ ctx.criticalPath.firstStep).subgroupOf
      (VAt ctx.Γ ctx.criticalPath.firstStep)).Normal) :
    let _ := hN
    let P := GAt ctx.Γ ctx.criticalPath.firstStep
    let V := VAt ctx.Γ ctx.criticalPath.firstStep
    let Z := ZAt ctx.Γ ctx.criticalPath.firstStep
    let W := V ⧸ Z.subgroupOf V
    ∀ action : P →* MulAut W,
      (∀ actor : P, ∀ point : V,
        action actor (QuotientGroup.mk' (Z.subgroupOf V) point) =
          QuotientGroup.mk' (Z.subgroupOf V)
            ⟨(actor:G)*(point:G)*(actor:G)⁻¹,
              (Subgroup.mem_normalizer_iff.mp
                (stabilizer_le_normalizer_v ctx.Γ ctx.criticalPath.firstStep
                  actor.property) point).mp point.property⟩) →
      pCore 2 P ≤ action.ker → action.ker = pCore 2 P := by
  let _ := hN
  dsimp only
  intro action haction hkernel
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let P := GAt Γ cp.firstStep
  let V := VAt Γ cp.firstStep
  let R := QAt Γ cp.firstStep
  let Z := ZAt Γ cp.firstStep
  have hRVlocal : R = V := hRV
  have htwo : IsPGroup 2 V := by
    rw [←hRVlocal]
    change IsPGroup 2 (Γ.twoCoreAt cp.firstStep)
    rw [Γ.twoCoreAt_def]
    exact (pCore_isPGroup (p := 2)).map _
  let _ : Fact (IsPGroup 2 V) := ⟨htwo⟩
  have hderived : (_root_.commutator V).map V.subtype = Z := by
    rw [_root_.commutator_def, Subgroup.map_commutator,
      ←MonoidHom.range_eq_map,Subgroup.range_subtype]
    exact (congrArg (fun X : Subgroup G => ⁅V,X⁆) hRV).symm.trans hcomm
  have hZfrattini : Z.subgroupOf V ≤ frattini V := by
    rw [←hderived, Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective V.subtype_injective]
    exact commutator_le_frattini_of_isPGroup (p := 2)
  have hPV : P ≤ Subgroup.normalizer (V : Set G) := stabilizer_le_normalizer_v Γ cp.firstStep
  let original : P →* MulAut V := V.normalizerMonoidHom.comp (Subgroup.inclusion hPV)
  have horiginalKernel : original.ker ≤ pCore 2 P := by
    intro a ha
    apply (edge_characteristic_data ctx.sectionSeven Γ cp).2
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    apply Subtype.ext
    have hqR : (q:G) ∈ R := by
      change (q:G) ∈ Γ.twoCoreAt cp.firstStep
      rw [Γ.twoCoreAt_def]
      exact Subgroup.mem_map_of_mem P.subtype hq
    have hqV : (q:G) ∈ V := hRVlocal ▸ hqR
    have hh := congrArg (fun f : MulAut V => (f ⟨q,hqV⟩ : G)) (MonoidHom.mem_ker.mp ha)
    change (a:G)*(q:G)*(a:G)⁻¹=(q:G) at hh
    exact (mul_inv_eq_iff_eq_mul.mp hh).symm
  have hquotientKernel : IsPGroup 2 action.ker :=
    MonoidHom.isPGroup_ker_quotient_action htwo original
      (pCore_isPGroup.to_le horiginalKernel) (Z.subgroupOf V) hZfrattini action haction
  exact le_antisymm (le_sSup ⟨inferInstance,hquotientKernel⟩) hkernel
end Stellmacher.SectionEight
