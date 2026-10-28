module
public import Stellmacher.SectionEight.EightSixHighCostResidualCard
public import Stellmacher.SectionEight.EightSixSelectedFixedCoreCollapse
/-!
# Fixed and displacement orders in the high-cost quotient

Retain the actual selected local high-cost configuration and the supplied
literal action of Gnext on Vnext/Znext, including its normality witness,
elementary structure, conjugation formula and two-core kernel. The quotient
has order 256, and every actual A actor outside Qnext has fixed subgroup
and cyclic displacement both of order sixteen.

The fixed-core collapse gives V0=Znext, so the actual residual/fixed
decomposition gives Vnext=Y. Assertion (17) supplies |Y|=512, and division
by the central line gives quotient order256. The exact uniform original
cost and native quotient commutator formula give displacement16. Restrict
the same action to the selected E; the real Frattini containment places
every A-square in its kernel. Elementary involution rank-nullity then gives
fixed order16. No equality Qnext=Vnext or raw selected-orbit model is used.

This is the full literal module count in Stellmacher (8.6), assertion (19),
printed p.45 of `refs/files/stellmacher-n-group.pdf`, for subsequent
centralizer-action and odd-quotient arguments.
-/

namespace Stellmacher.SectionEight
open Later SectionsFiveToSeven CosetGraphContext
universe u
public theorem eight_six_high_cost_fixed_displacement_card
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
      Nat.card W = 256 ∧ ∀ mover : P,
        (mover:G) ∈ VAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.a →
        (mover:G) ∉ QAt ctx.Γ ctx.criticalPath.firstStep →
        Nat.card (FixedPoints.subgroup (Subgroup.zpowers (action mover)) W) = 16 ∧
        Nat.card (commutatorAction (Subgroup.zpowers (action mover)) W) = 16 := by
  classical
  let _ := hN
  dsimp only
  intro hW action haction hkernel
  let _ := hW
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let P := GAt Γ cp.firstStep
  let V := VAt Γ cp.firstStep
  let R := QAt Γ cp.firstStep
  let Z := ZAt Γ cp.firstStep
  let W := V ⧸ Z.subgroupOf V
  let A := VAt Γ previous ⊓ QAt Γ cp.a
  let Y := ⁅R,twoResidualIn E⁆
  let C := V ⊓ Subgroup.centralizer (twoResidualIn E : Set G)
  have hselected := eight_six_selected_fixed_core_containment ctx hcenter hquot hlength
    hcard previous D L Q hprev hD hL hQ data E A0 actor geom hcore hedge ha hout hlarge hmin
  have hcollapse := eight_six_selected_fixed_core_eq_next_center ctx hcenter hquot hlength
    hcard previous D L Q hprev data E A0 actor geom hcore hedge hD hL hhigh hselected.1
  have hp := eight_six_selected_residual_decomposition ctx hcenter hquot hlength hcard
    previous D L Q hprev data E A0 actor geom hcore hedge hD hL
  have hi : Y ⊓ C = Z := hp.2.1
  have hZY : Z ≤ Y := hi ▸ inf_le_left
  have hZC : Z ≤ C := hi ▸ inf_le_right
  have hZV : Z ≤ V := hZC.trans inf_le_left
  have hVR : V ≤ R := SevenSix.neighbor_join_le_core_of_length_gt_one Γ cp
    (by exact hlength ▸ by decide) _
  have hCZ : C = Z := le_antisymm ((inf_le_inf hVR le_rfl).trans_eq hcollapse) hZC
  have hVY : V = Y := by
    have hs : V = Y ⊔ C := hp.2.2
    rwa [hCZ,sup_eq_left.mpr hZY] at hs
  have hnumeric := eight_six_high_cost_residual_card ctx hcenter hquot hlength hcard
    previous D L Q hprev data E A0 actor geom hcore hedge hD hL ha hout hlarge hmin hQ hhigh
  have hVcard : Nat.card V = 512 := hVY ▸ hnumeric.2
  have hZcard : Nat.card Z = 2 := (eight_six_first_step_fixed_line_local ctx hcenter hcard).1
  have hWcard : Nat.card W = 256 := by
    have hh := Subgroup.card_eq_card_quotient_mul_card_subgroup (Z.subgroupOf V)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZV).toEquiv,hZcard,hVcard] at hh
    change 512 = Nat.card W * 2 at hh
    omega
  have hAE : A ≤ E := geom.generated ▸ le_sup_left
  have hPV : P ≤ Subgroup.normalizer (V : Set G) := stabilizer_le_normalizer_v Γ cp.firstStep
  let restricted : E →* MulAut W := action.comp (Subgroup.inclusion geom.group_le)
  have hRnative : R.subgroupOf P = pCore 2 P := by
    change (Γ.twoCoreAt cp.firstStep).subgroupOf P = _
    rw [Γ.twoCoreAt_def]
    exact Subgroup.comap_map_eq_self_of_injective P.subtype_injective _
  have hrestrictedKernel : R.subgroupOf E ≤ restricted.ker := by
    intro b hb
    apply MonoidHom.mem_ker.mpr
    exact MonoidHom.mem_ker.mp (hkernel (hRnative ▸ hb))
  have hsquares := (eight_six_selected_coatom_action_data ctx previous D L Q hD hQ
    data E A0 actor geom ha restricted hrestrictedKernel).2.2.2.2
  refine ⟨hWcard,?_⟩
  intro mover hmover houtside
  let b : E := ⟨mover,hAE hmover⟩
  have hsquare : (action mover)^2 = 1 := hsquares b hmover
  have hcyclic : (Subgroup.zpowers (mover:G)).subgroupOf P = Subgroup.zpowers mover := by
    apply Subgroup.map_injective P.subtype_injective
    rw [Subgroup.map_subgroupOf_eq_of_le (Subgroup.zpowers_le.mpr mover.property),
      MonoidHom.map_zpowers]
    rfl
  have hJV : ⁅V,Subgroup.zpowers (mover:G)⁆ ≤ V := Subgroup.le_normalizer_iff_commutator_le_left.mp
    ((Subgroup.zpowers_le.mpr mover.property).trans hPV)
  have hrel := Subgroup.relIndex_sup_right ((⁅V,Subgroup.zpowers (mover:G)⁆).subgroupOf V)
    (Z.subgroupOf V)
  rw [←Subgroup.subgroupOf_sup hJV hZV,
    Subgroup.relIndex_subgroupOf (sup_le hJV hZV),
    Subgroup.relIndex_subgroupOf hJV] at hrel
  have hrank : Nat.card (commutatorAction (Subgroup.zpowers (action mover)) W) =
      eightSixCommutatorCost ctx.Γ ctx.criticalPath (mover:G) := by
    have hh := Subgroup.quotient_conjugation_commutatorAction_card P V Z
      (Subgroup.zpowers (mover:G)) hPV (Subgroup.zpowers_le.mpr mover.property) hN action haction
    rw [hcyclic,MonoidHom.map_zpowers] at hh
    exact hh.trans hrel.symm
  have hcost : eightSixCommutatorCost ctx.Γ ctx.criticalPath (mover:G) = 16 :=
    (eight_six_selected_all_actor_costs ctx hcenter hquot hlength hcard previous D L Q
      hprev data E A0 actor geom hcore hedge hD hL ha hout hlarge hmin hQ
      mover hmover houtside).trans hnumeric.1
  have hdisp : Nat.card (commutatorAction (Subgroup.zpowers (action mover)) W) = 16 :=
    hrank.trans hcost
  have hcount := (MulAut.involution_fixed_displacement_card_data (action mover) hsquare).1
  change Nat.card W = Nat.card (FixedPoints.subgroup (Subgroup.zpowers (action mover)) W) *
    Nat.card (commutatorAction (Subgroup.zpowers (action mover)) W) at hcount
  rw [hWcard,hdisp] at hcount
  have hfixed : Nat.card (FixedPoints.subgroup (Subgroup.zpowers (action mover)) W) = 16 := by
    omega
  exact ⟨hfixed,hdisp⟩
end Stellmacher.SectionEight
