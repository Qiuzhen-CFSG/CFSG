module
public import Stellmacher.SectionEight.EightSixHighCostResidualCentralizer
public import Theory.GroupAction.RankThreeBinaryElementaryFixed
public import Theory.GroupAction.SubgroupConjugation
/-!
# Elementary structure of the high-cost residual action image

For the actual selected high-cost local configuration, retain the supplied
literal next-stabilizer action on Vnext/Znext and the earlier graph input
|A:(A intersect D)|=8. The image of the full next residual is elementary
abelian of exponent three. The rank input is explicit and is supplied by
the separate graph actor-rank producer; no global faithfulness, raw model
or full case-C conclusion is assumed.

Positive original costs identify the action kernel on A with A intersect D,
so its actual image has order eight. The true Frattini containment gives
exponent two. This image normalizes the residual three-group image. For
each nonidentity actor image, lift to the actual outside A actor: source
(20) makes its residual centralizer elementary cubic. With the same literal
conjugation action, the rank-three binary fixed-group theorem then makes
the full residual image elementary cubic.

This proves the elementary action-image assertion of Stellmacher (8.6)(21),
printed p.45 of `refs/files/stellmacher-n-group.pdf`. Individual coatom-fixed
orders, four-factor counting and the native E/O₂(E) identification remain
separate later conclusions.
-/

namespace Stellmacher.SectionEight
open Later SectionsFiveToSeven CosetGraphContext SevenSix
open scoped IsMulCommutative
universe u
public theorem eight_six_high_cost_residual_action_is_elementary
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
    (hindex : QuotientCardEq (VAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.a)
      ((VAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.a) ⊓ D) 8)
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
      IsElementaryAbelian 3 (((twoResidualIn P).subgroupOf P).map action) := by
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
  let Ai := A.subgroupOf P
  let Abar := Ai.map action
  let F := ((twoResidualIn P).subgroupOf P).map action
  have hAP : A ≤ P := (geom.generated ▸ le_sup_left).trans geom.group_le
  have hAprev : A ≤ QAt Γ previous := inf_le_left.trans
    (SevenSix.neighbor_join_le_core_of_length_gt_one Γ cp (by exact hlength ▸ by decide) previous)
  have hF : IsPGroup 3 F := eight_six_next_residual_action_is_three_group ctx hcenter hquot
    hlength hcard previous D L Q hprev data E A0 actor geom hcore hedge hD hL hN hW action haction hkernel
  have hcounts := (eight_six_high_cost_fixed_displacement_card ctx hcenter hquot hlength hcard
    previous D L Q hprev data E A0 actor geom hcore hedge hD hL ha hout hlarge hmin hQ hhigh
    hN hW action haction hkernel).2
  have hRnative : R.subgroupOf P = pCore 2 P := by
    change (Γ.twoCoreAt cp.firstStep).subgroupOf P = _
    rw [Γ.twoCoreAt_def]
    exact Subgroup.comap_map_eq_self_of_injective P.subtype_injective _
  have hkerAi : Ai ⊓ action.ker = (A ⊓ D).subgroupOf P := by
    ext a
    constructor
    · intro h
      have haR : (a:G) ∈ R := by
        by_contra houtside
        have hdisp := (hcounts a h.1 houtside).2
        have hbot : commutatorAction (⊥ : Subgroup (MulAut W)) W = ⊥ := by
          apply bot_unique
          rw [commutatorAction_eq_closure,Subgroup.closure_le]
          rintro _ ⟨g,w,rfl⟩
          have hg : (g:MulAut W)=1 := g.property
          change w⁻¹*(g:MulAut W) w=1
          rw [hg]
          exact inv_mul_cancel w
        rw [MonoidHom.mem_ker.mp h.2,Subgroup.zpowers_one_eq_bot,hbot,Subgroup.card_bot] at hdisp
        omega
      exact ⟨h.1,hD ▸ ⟨hAprev h.1,haR⟩⟩
    · intro h
      exact ⟨h.1,hkernel (hRnative ▸ (hD ▸ h.2).2)⟩
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
    exact MonoidHom.mem_ker.mp (hkernel (hRnative ▸ (hD ▸ haD).2))
  have hpow (a : Abar) : a^2=1 := by
    obtain ⟨lift,hlift,heq⟩ := a.property
    apply Subtype.ext
    change (a:MulAut W)^2=1
    rw [←heq]
    exact hsquare lift hlift
  let _ : IsElementaryAbelian 2 Abar := {
    toIsMulCommutative := ⟨⟨fun a b => (Commute.of_orderOf_dvd_two
      (fun g => orderOf_dvd_of_pow_eq_one (hpow g)) a b).eq⟩⟩
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr hpow }
  let _ : ((twoResidualIn P).subgroupOf P).Normal := twoResidualIn_normal P
  have hAF : Abar ≤ Subgroup.normalizer (F : Set (MulAut W)) :=
    (Subgroup.map_mono (show Ai ≤ Subgroup.normalizer
      ((twoResidualIn P).subgroupOf P : Set P) from Subgroup.le_normalizer_of_normal)).trans
        (Subgroup.le_normalizer_map action)
  let _ : MulDistribMulAction Abar F :=
    Subgroup.conjMulDistribMulActionOfLeNormalizer Abar F hAF
  apply elementary_three_of_rank_three_binary_fixed (A := Abar) hAcard hF
  intro a hane
  obtain ⟨lift,hlift,heq⟩ := a.property
  have hliftOut : (lift:G) ∉ R := by
    intro hR
    have hone : action lift=1 := MonoidHom.mem_ker.mp (hkernel (hRnative ▸ hR))
    exact hane (Subtype.ext (heq.symm.trans hone))
  let C := F ⊓ Subgroup.centralizer (Subgroup.zpowers (action lift) : Set (MulAut W))
  let _ : IsElementaryAbelian 3 C := (eight_six_high_cost_residual_centralizer ctx hcenter
    hquot hlength hcard previous D L Q hprev data E A0 actor geom hcore hedge hD hL
    ha hout hlarge hmin hQ hhigh hN hW action haction hkernel lift hlift hliftOut).1
  let J := FixedPoints.subgroup (Subgroup.zpowers a) F
  have hcent (x : J) : ((x:F):MulAut W) ∈ C := by
    refine ⟨(x:F).property,?_⟩
    rw [Subgroup.zpowers_eq_closure,Subgroup.centralizer_closure]
    apply Subgroup.mem_centralizer_singleton_iff.mpr
    have hh := congrArg Subtype.val (x.property ⟨a,Subgroup.mem_zpowers a⟩)
    change (a:MulAut W)*((x:F):MulAut W)*(a:MulAut W)⁻¹=((x:F):MulAut W) at hh
    rw [←heq] at hh
    exact (mul_inv_eq_iff_eq_mul.mp hh).symm
  have hcomm : IsMulCommutative J := ⟨⟨fun x y => by
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : C => (z:MulAut W))
      (mul_comm (⟨((x:F):MulAut W),hcent x⟩:C) ⟨((y:F):MulAut W),hcent y⟩)⟩⟩
  exact {
    toIsMulCommutative := hcomm
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr fun x => by
      apply Subtype.ext
      apply Subtype.ext
      exact elemPow_eq_one_of_isElementaryAbelian ((x:F):MulAut W) (hcent x) }
end Stellmacher.SectionEight
