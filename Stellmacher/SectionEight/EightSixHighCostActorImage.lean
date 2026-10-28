module
public import Stellmacher.SectionEight.EightSixHighCostActorRank
public import Stellmacher.SectionEight.EightSixHighCostResidualCentralizer
/-!
# The actual high-cost actor image and its residual centralizers

In the original selected high-cost configuration, retain elementary D and
a supplied literal next-stabilizer action on Vnext/Znext with exact two-core
kernel. The image of A=Vprev∩Qa is elementary binary of order eight. Every
nonidentity element of this actual image has centralizer of order at most
nine in the full next-residual image.

The action kernel on A is exactly A∩D: A lies in Qprev and the supplied
kernel is Qnext. The original graph actor-rank theorem then gives image
order eight. Actual equation-one Frattini containment puts all squares in
D, proving exponent two. Lift each nonidentity image element back to A;
exactness of the kernel puts the lift outside Qnext, so the proved
source-(20) centralizer bound applies to that same action.

This is the numeric actor packet for Stellmacher (8.6)(19)–(21), printed
p.45. It extracts the inputs needed by the independent fixed-factor count.
Faithfulness of this binary actor on the residual and Sylow transitivity
remain separate statements; they are not assumed implicitly here.
-/

namespace Stellmacher.SectionEight
open Later SectionsFiveToSeven CosetGraphContext SevenSix
open scoped IsMulCommutative
universe u
public theorem eight_six_high_cost_actor_image_data
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
    (helementary : IsElementaryAbelianSubgroup 2 D)
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
      action.ker = pCore 2 P →
      let Abar := ((VAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.a).subgroupOf P).map action
      let F := ((twoResidualIn P).subgroupOf P).map action
      IsElementaryAbelian 2 Abar ∧ Nat.card Abar = 8 ∧
        ∀ a : Abar, a ≠ 1 →
          Nat.card (F ⊓ Subgroup.centralizer (Subgroup.zpowers (a : MulAut W) : Set (MulAut W)) :
            Subgroup (MulAut W)) ≤ 9 := by
  classical
  let _ := hN
  dsimp only
  intro hW action haction hkernel
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let P := GAt Γ cp.firstStep
  let V := VAt Γ cp.firstStep
  let R := QAt Γ cp.firstStep
  let Z := ZAt Γ cp.firstStep
  let W := V ⧸ Z.subgroupOf V
  let A := VAt Γ previous ⊓ QAt Γ cp.a
  let Ai := A.subgroupOf P
  let Abar := Ai.map action
  let F := ((twoResidualIn P).subgroupOf P).map action
  have hindex := eight_six_high_cost_actor_rank ctx hcenter hquot hlength hcard
    previous D L Q hprev data E A0 actor geom hcore hedge hD hL
    ha hout hlarge hmin hQ hhigh helementary
  have hAP : A ≤ P := (geom.generated ▸ le_sup_left).trans geom.group_le
  have hAprev : A ≤ QAt Γ previous := inf_le_left.trans
    (SevenSix.neighbor_join_le_core_of_length_gt_one Γ cp (by exact hlength ▸ by decide) previous)
  have hRnative : R.subgroupOf P = pCore 2 P := by
    change (Γ.twoCoreAt cp.firstStep).subgroupOf P = _
    rw [Γ.twoCoreAt_def]
    exact Subgroup.comap_map_eq_self_of_injective P.subtype_injective _
  have hkerAi : Ai ⊓ action.ker = (A ⊓ D).subgroupOf P := by
    rw [hkernel,←hRnative]
    ext a
    change ((a:G) ∈ A ∧ (a:G) ∈ R) ↔ ((a:G) ∈ A ∧ (a:G) ∈ D)
    constructor
    · intro h
      exact ⟨h.1,hD ▸ ⟨hAprev h.1,h.2⟩⟩
    · intro h
      exact ⟨h.1,(hD ▸ h.2).2⟩
  have hindexEight : (A ⊓ D).relIndex A = 8 := by
    have hh := ((A ⊓ D).subgroupOf A).index_mul_card
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (show A ⊓ D ≤ A from inf_le_left)).toEquiv] at hh
    change (A ⊓ D).relIndex A * Nat.card (A ⊓ D : Subgroup G) = Nat.card A at hh
    change Nat.card A = 8 * Nat.card (A ⊓ D : Subgroup G) at hindex
    have hp : 0 < Nat.card (A ⊓ D : Subgroup G) := Nat.card_pos
    nlinarith
  have hAcard : Nat.card Abar = 8 := by
    change Nat.card (Ai.map action) = 8
    rw [←Subgroup.relIndex_ker,←Subgroup.inf_relIndex_left Ai action.ker,hkerAi,
      Subgroup.relIndex_subgroupOf hAP]
    exact hindexEight
  have hAQ : A ≤ Q := data.core_generation ▸ le_sup_of_le_left le_sup_left
  have hQtwo : IsPGroup 2 Q := by
    rw [hQ,twoCoreIn]
    exact (pCore_isPGroup (p := 2)).map _
  let _ : Fact (IsPGroup 2 Q) := ⟨hQtwo⟩
  have hsquare (a : P) (haA : a ∈ Ai) : (action a)^2=1 := by
    have haD : (a:G)^2 ∈ D := data.core_frattini_le
      (Subgroup.mem_map.mpr ⟨(⟨a,hAQ haA⟩:Q)^2,
        pth_power_mem_frattini_of_isPGroup (p := 2) (⟨a,hAQ haA⟩:Q),rfl⟩)
    rw [←map_pow]
    exact MonoidHom.mem_ker.mp (hkernel.ge (hRnative ▸ (hD ▸ haD).2))
  have hpow (a : Abar) : a^2=1 := by
    obtain ⟨lift,hlift,heq⟩ := a.property
    apply Subtype.ext
    change (a:MulAut W)^2=1
    rw [←heq]
    exact hsquare lift hlift
  have hAelementary : IsElementaryAbelian 2 Abar := {
    toIsMulCommutative := ⟨⟨fun a b => (Commute.of_orderOf_dvd_two
      (fun g => orderOf_dvd_of_pow_eq_one (hpow g)) a b).eq⟩⟩
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr hpow }
  refine ⟨hAelementary,hAcard,?_⟩
  intro a hane
  obtain ⟨lift,hlift,heq⟩ := a.property
  have hliftOut : (lift:G) ∉ R := by
    intro hR
    have hone : action lift=1 := MonoidHom.mem_ker.mp (hkernel.ge (hRnative ▸ hR))
    exact hane (Subtype.ext (heq.symm.trans hone))
  have hb := (eight_six_high_cost_residual_centralizer ctx hcenter hquot hlength hcard
    previous D L Q hprev data E A0 actor geom hcore hedge hD hL
    ha hout hlarge hmin hQ hhigh hN hW action haction hkernel.ge lift hlift hliftOut).2
  rw [heq] at hb
  exact hb
end Stellmacher.SectionEight
