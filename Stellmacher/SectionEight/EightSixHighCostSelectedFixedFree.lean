module
public import Stellmacher.SectionEight.EightSixSelectedFixedCoreCollapse
public import Stellmacher.SectionEight.EightSixSelectedFixedCoreContainment
public import Stellmacher.SectionEight.EightSixResidualFixedDecomposition
/-!
# The selected residual has no fixed cosets in the high-cost quotient

In the original selected high-cost configuration, retain any supplied
literal action of the next stabilizer on Vnext/Znext that kills the next
two-core. The selected residual image has trivial fixed subgroup on that
same quotient. No elementary-D or rank-four hypothesis is needed.

The actual source14 containment and source18 collapse put the residual
centralizer in Qnext exactly at Znext. Since Vnext lies in Qnext, its
selected residual centralizer is contained in Znext as well. The existing
residual fixed-lift theorem identifies quotient fixed points with the
image of that actual centralizer, which is trivial. Passing between the
range-restricted actor and its literal image preserves the point action.

This is the selected fixed-free input for the quotient-action clause
(8.6)(c3), following (18) on printed p.45 of Stellmacher, Journal of Algebra
190 (1997). It concerns fixed cosets and does not use the full-preimage
centralizer shortcut excluded by the source audit.
-/

namespace Stellmacher.SectionEight
open Later SectionsFiveToSeven CosetGraphContext SevenSix
universe u
public theorem eight_six_high_cost_selected_residual_fixed_free
    {G : Type u} [Group G] [Finite G] {S P1 P2 : Subgroup G}
    (ctx : SectionEightLocalContext G S P1 P2)
    (hcenter : ZAt ctx.Γ ctx.criticalPath.firstStep ≤
      CenterAmbient (GAt ctx.Γ ctx.criticalPath.firstStep))
    (hquot : QuotientIsModel (GAt ctx.Γ ctx.criticalPath.a)
      (QAt ctx.Γ ctx.criticalPath.a) SL2Two)
    (hlength : ctx.criticalPath.length = 2)
    (hcard : Nat.card (ZAt ctx.Γ ctx.criticalPath.a) = 4)
    (previous : ctx.Γ.Vertex) (D L Q : Subgroup G)
    (hprev : previous ∈ Neighborhood ctx.Γ ctx.criticalPath.a ∧
      previous ≠ ctx.criticalPath.firstStep)
    (data : EightSixEquationOneData ctx.Γ ctx.criticalPath previous D L Q)
    (E A0 : Subgroup G) (actor : G)
    (geom : SectionNine.NineThreeGeometricData ctx.Γ
      ctx.criticalPath.firstStep ctx.criticalPath.a
      (VAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.a) E A0 actor)
    (hcore : conjugateClosure (ZAt ctx.Γ ctx.criticalPath.a) E ≤
      QAt ctx.Γ ctx.criticalPath.a)
    (hedge : E ⊔ (GAt ctx.Γ ctx.criticalPath.a ⊓ GAt ctx.Γ ctx.criticalPath.firstStep) =
      GAt ctx.Γ ctx.criticalPath.firstStep)
    (hD : D = QAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.firstStep)
    (hL : L = conjugateClosure (QAt ctx.Γ previous) (GAt ctx.Γ ctx.criticalPath.a))
    (ha : actor ∈ VAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.a)
    (hout : actor ∉ QAt ctx.Γ ctx.criticalPath.firstStep)
    (hlarge : 4 * Nat.card
      ((VAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.a) ⊓ D : Subgroup G) ≤
      Nat.card (VAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.a : Subgroup G))
    (hmin : ∀ other : G, other ∈ VAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.a →
      other ∉ QAt ctx.Γ ctx.criticalPath.firstStep →
        eightSixCommutatorCost ctx.Γ ctx.criticalPath actor ≤
          eightSixCommutatorCost ctx.Γ ctx.criticalPath other)
    (hQ : Q = twoCoreIn L)
    (hhigh : ∀ mover : G, mover ∈ VAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.a →
      mover ∉ QAt ctx.Γ ctx.criticalPath.firstStep →
        8 ≤ eightSixCommutatorCost ctx.Γ ctx.criticalPath mover)
    (hN : ((ZAt ctx.Γ ctx.criticalPath.firstStep).subgroupOf
      (VAt ctx.Γ ctx.criticalPath.firstStep)).Normal) :
    let _ := hN
    let P := GAt ctx.Γ ctx.criticalPath.firstStep
    let V := VAt ctx.Γ ctx.criticalPath.firstStep
    let Z := ZAt ctx.Γ ctx.criticalPath.firstStep
    let W := V ⧸ Z.subgroupOf V
    ∀ (_hW : IsElementaryAbelian 2 W) (action : P →* MulAut W),
      (∀ actor : P, ∀ point : V,
        action actor (QuotientGroup.mk' (Z.subgroupOf V) point) =
          QuotientGroup.mk' (Z.subgroupOf V)
            ⟨(actor:G)*(point:G)*(actor:G)⁻¹,
              (Subgroup.mem_normalizer_iff.mp
                (stabilizer_le_normalizer_v ctx.Γ ctx.criticalPath.firstStep
                  actor.property) point).mp point.property⟩) →
      pCore 2 P ≤ action.ker →
      FixedPoints.subgroup (((twoResidualIn E).subgroupOf P).map action) W = ⊥ := by
  classical
  let _ := hN
  dsimp only
  intro hW action hformula hkernel
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let P := GAt Γ cp.firstStep
  let V := VAt Γ cp.firstStep
  let Z := ZAt Γ cp.firstStep
  let W := V ⧸ Z.subgroupOf V
  let B := twoResidualIn E
  let Bbar := (B.subgroupOf P).map action.rangeRestrict
  let C := V ⊓ Subgroup.centralizer (B : Set G)
  have hselected := eight_six_selected_fixed_core_containment ctx hcenter hquot hlength
    hcard previous D L Q hprev hD hL hQ data E A0 actor geom hcore hedge ha hout hlarge hmin
  have hcollapse := eight_six_selected_fixed_core_eq_next_center ctx hcenter hquot hlength
    hcard previous D L Q hprev data E A0 actor geom hcore hedge hD hL hhigh hselected.1
  have hVR : V ≤ QAt Γ cp.firstStep :=
    neighbor_join_le_core_of_length_gt_one Γ cp (by exact hlength ▸ by decide) _
  have hCZ : C ≤ Z := (inf_le_inf hVR le_rfl).trans hcollapse.le
  have hdecomp := eight_six_residual_fixed_decomposition ctx hcenter hlength hcard
    E geom.group_le hN hW action hformula hkernel
  have hfixed : FixedPoints.subgroup Bbar W = ⊥ := by
    rw [←hdecomp.2.1]
    apply (Subgroup.map_eq_bot_iff _).mpr
    rw [QuotientGroup.ker_mk']
    exact Subgroup.subgroupOf_mono V hCZ
  apply bot_unique
  intro w hw
  have hwbar : w ∈ FixedPoints.subgroup Bbar W := by
    intro b
    obtain ⟨lift,hlift,heq⟩ := b.property
    have hh := hw ⟨action lift,Subgroup.mem_map_of_mem action hlift⟩
    change ((b:action.range):MulAut W) w = w
    rw [←heq]
    exact hh
  exact hfixed ▸ hwbar
end Stellmacher.SectionEight
