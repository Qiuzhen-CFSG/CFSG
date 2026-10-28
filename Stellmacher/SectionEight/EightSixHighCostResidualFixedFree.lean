module
public import Stellmacher.SectionEight.EightSixHighCostActorFaithful
public import Stellmacher.SectionEight.EightSixHighCostResidualElementary
public import Stellmacher.SectionEight.EightSixActorImageNormalizer
public import Stellmacher.SectionThree.ResidualImageIrreducible
/-!
# The actual high-cost residual is irreducible and has no whole-actor fixed points

Retain the original high-cost graph configuration, elementary D, and the
supplied literal next quotient action with exact two-core kernel. Its full
residual image is irreducible under the actual edge-Sylow image. Its
intersection with the centralizer of the actual order-eight actor is trivial.

The prior elementary-image and actor-faithfulness theorems show that the
residual is nontrivial. The native PSet residual-image theorem then gives
irreducibility from (3.3). Equation-one core generation identifies the actor
image with a Sylow-normalized core image. Consequently the whole-actor fixed
subgroup is Sylow invariant. Irreducibility makes it trivial or all the
residual; the latter contradicts faithfulness of the nontrivial actor.

This supplies the whole-fixed-free input to Stellmacher (8.6)(21), printed
p.45. It uses neither a rank-four conclusion nor assumed factor transitivity.
-/

namespace Stellmacher.SectionEight
open Later SectionsFiveToSeven CosetGraphContext SevenSix
open scoped IsMulCommutative
universe u
public theorem eight_six_high_cost_residual_irreducible_fixed_free
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
      IsIrreducibleSection ((S.subgroupOf P).map action) ⊥ F ∧
        F ⊓ Subgroup.centralizer (Abar : Set (MulAut W)) = ⊥ := by
  classical
  let _ := hN
  dsimp only
  intro hW action haction hkernel
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let P := GAt Γ cp.firstStep
  let V := VAt Γ cp.firstStep
  let Z := ZAt Γ cp.firstStep
  let W := V ⧸ Z.subgroupOf V
  let A := VAt Γ previous ⊓ QAt Γ cp.a
  let Abar := (A.subgroupOf P).map action
  let R := (twoResidualIn P).subgroupOf P
  let F := R.map action
  let T := (S.subgroupOf P).map action
  have hindex := eight_six_high_cost_actor_rank ctx hcenter hquot hlength hcard
    previous D L Q hprev data E A0 actor geom hcore hedge hD hL
    ha hout hlarge hmin hQ hhigh helementary
  have hFe : IsElementaryAbelian 3 F := eight_six_high_cost_residual_action_is_elementary
    ctx hcenter hquot hlength hcard previous D L Q hprev data E A0 actor geom hcore hedge hD hL
    ha hout hlarge hmin hQ hhigh hindex hN hW action haction hkernel.ge
  have hfaith : Abar ⊓ Subgroup.centralizer (F : Set (MulAut W)) = ⊥ :=
    eight_six_high_cost_actor_residual_centralizer_trivial ctx hcenter hquot hlength hcard
      previous D L Q hprev data E A0 actor geom hcore hedge hD hL
      ha hout hlarge hmin hQ hhigh helementary hN hW action haction hkernel
  have hAdata := eight_six_high_cost_actor_image_data ctx hcenter hquot hlength hcard
    previous D L Q hprev data E A0 actor geom hcore hedge hD hL
    ha hout hlarge hmin hQ hhigh helementary hN hW action haction hkernel
  have hAne : Abar ≠ ⊥ := by
    intro hh
    have h1 : Nat.card Abar = 1 := (Subgroup.card_eq_one).mpr hh
    have h8 : Nat.card Abar = 8 := hAdata.2.1
    omega
  have hFne : F ≠ ⊥ := by
    intro hh
    apply hAne
    have hAC : Abar ≤ Subgroup.centralizer (F : Set (MulAut W)) := by
      intro a _ f hf
      have hf1 : f = 1 := (show f ∈ (⊥ : Subgroup (MulAut W)) from hh ▸ hf)
      simp only [hf1,one_mul,mul_one]
    simpa only [inf_eq_left.mpr hAC] using hfaith
  have hRnative : R = twoResidualSubgroup P :=
    Subgroup.comap_map_eq_self_of_injective P.subtype_injective _
  have hlocal := (edge_local_data ctx.sectionSeven Γ cp).2
  have hirred : IsIrreducibleSection T ⊥ F :=
    SectionThree.pSet_residual_image_irreducible S (sectionThreeHypotheses ctx.sectionSeven)
      P ((pFamily_iff_pSet _ _ _).mp hlocal.1) hlocal.2 action F
      (by rw [←hRnative]) hFne hFe
  have hTA : T ≤ Subgroup.normalizer (Abar : Set (MulAut W)) :=
    (eight_six_actor_image_eq_core_and_normalized ctx hlength previous D L Q hD hL hQ
      data action hkernel.ge).2.1
  let _ : R.Normal := twoResidualIn_normal P
  have hTF : T ≤ Subgroup.normalizer (F : Set (MulAut W)) :=
    (Subgroup.map_mono (show S.subgroupOf P ≤ Subgroup.normalizer (R : Set P) from
      Subgroup.le_normalizer_of_normal)).trans (Subgroup.le_normalizer_map action)
  have hNC : Subgroup.normalizer (Abar : Set (MulAut W)) ≤
      Subgroup.normalizer (Subgroup.centralizer (Abar : Set (MulAut W)) : Set (MulAut W)) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (Subgroup.centralizer_le_normalizer _)).mp
      (Subgroup.normal_subgroupOf_centralizer_normalizer _)
  let C := F ⊓ Subgroup.centralizer (Abar : Set (MulAut W))
  have hTC : T ≤ Subgroup.normalizer (C : Set (MulAut W)) :=
    (le_inf hTF (hTA.trans hNC)).trans Subgroup.inf_normalizer_le_normalizer_inf
  have hCinv : IsConjugateInvariantBy C T := by
    intro t c hc
    exact (Subgroup.mem_normalizer_iff.mp (hTC t.property) c).mp hc
  refine ⟨hirred,?_⟩
  rcases hirred.2.2 C bot_le inf_le_left hCinv with hbot | htop
  · exact hbot
  · exfalso
    have hFC : F ≤ Subgroup.centralizer (Abar : Set (MulAut W)) := htop ▸ inf_le_right
    have hAC : Abar ≤ Subgroup.centralizer (F : Set (MulAut W)) := Subgroup.le_centralizer_iff.mp hFC
    apply hAne
    simpa only [inf_eq_left.mpr hAC] using hfaith
end Stellmacher.SectionEight
