module
public import Stellmacher.SectionEight.EightSixCostFourRelativeDoubleSL2
public import Stellmacher.SectionEight.EightSixRelativeImageNormality
public import Theory.GroupAction.NormalizingActor

/-!
# The full next quotient in the cost-four branch

The actual next quotient Vnext/Znext has order sixteen, and Vnext equals
the selected residual commutator Y=[Qnext,O²(E)]. The theorem preserves the
selected local telescope and the supplied quotient normality, elementary
structure, conjugation action, and Sylow-fixed-generation data.

The corrected relative bounded-(1.6) theorem supplies a commutator module
of order sixteen for F=[O₂′(X),Abar] in the full faithful image X. The
relative-image normality theorem makes this module invariant under X and
places the selected residual image inside F. Thus the module contains the
image of Y and hence the initial center seed. The next stabilizer's
conjugates of that seed generate Vnext, so the invariant module fills the
whole quotient. Since |Y|=32 and |Znext|=2 were already proved, comparison
of subgroup orders gives Vnext=Y.

This is the module-saturation step after bounded (1.6) in Stellmacher,
Journal of Algebra 190 (1997), proof of (8.6), printed p.44. No full module
order, ordinary quotient model, or residual equality is assumed.
-/

namespace Stellmacher.SectionEight
open Later SectionsFiveToSeven CosetGraphContext SevenSix
open scoped commutatorElement IsMulCommutative
universe u
public theorem eight_six_cost_four_full_module_card
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
    (hcost : eightSixCommutatorCost ctx.Γ ctx.criticalPath actor = 4)
    (hN : ((ZAt ctx.Γ ctx.criticalPath.firstStep).subgroupOf
      (VAt ctx.Γ ctx.criticalPath.firstStep)).Normal) :
    let _ := hN
    let P := GAt ctx.Γ ctx.criticalPath.firstStep
    let V := VAt ctx.Γ ctx.criticalPath.firstStep
    let Z := ZAt ctx.Γ ctx.criticalPath.firstStep
    ∀ (_hW : IsElementaryAbelian 2 (V ⧸ Z.subgroupOf V))
      (action : P →* MulAut (V ⧸ Z.subgroupOf V)),
      (∀ mover : P, ∀ point : V,
        action mover (QuotientGroup.mk' (Z.subgroupOf V) point) =
          QuotientGroup.mk' (Z.subgroupOf V)
            ⟨(mover:G)*(point:G)*(mover:G)⁻¹,
              (Subgroup.mem_normalizer_iff.mp
                (stabilizer_le_normalizer_v ctx.Γ ctx.criticalPath.firstStep
                  mover.property) point).mp point.property⟩) →
      pCore 2 P ≤ action.ker →
      (⊤ : Subgroup (V ⧸ Z.subgroupOf V)) =
        SectionOne.actionClosure action.range (V ⧸ Z.subgroupOf V)
          (FixedPoints.subgroup ((S.subgroupOf P).map action.rangeRestrict)
            (V ⧸ Z.subgroupOf V)) →
      Nat.card (V ⧸ Z.subgroupOf V) = 16 ∧
        V = ⁅QAt ctx.Γ ctx.criticalPath.firstStep,twoResidualIn E⁆ := by
  classical
  let _ := hN
  dsimp only
  intro hW action haction hkernel hgenerate
  let _ := hW
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let P := GAt Γ cp.firstStep
  let V := VAt Γ cp.firstStep
  let Z := ZAt Γ cp.firstStep
  let A := VAt Γ previous ⊓ QAt Γ cp.a
  let W := V ⧸ Z.subgroupOf V
  let X := action.range
  let B := (A.subgroupOf P).map action.rangeRestrict
  let F := ⁅SectionOne.oddCore X,B⁆
  let M := commutatorAction F W
  let R := twoResidualIn E
  let Y := ⁅QAt Γ cp.firstStep,R⁆
  let π : V →* W := QuotientGroup.mk' (Z.subgroupOf V)
  have hPV : P ≤ Subgroup.normalizer (V : Set G) := stabilizer_le_normalizer_v Γ _
  have hRP : R ≤ P := (twoResidualIn_le E).trans geom.group_le
  have hrelative := eight_six_cost_four_relative_double_sl2 ctx hcenter hquot hlength hcard
    previous D L Q hprev data E A0 actor geom hcore hedge hD hL ha hout hlarge hmin hQ hcost
      hN hW action haction hkernel hgenerate
  have hMcard : Nat.card M = 16 := hrelative.2
  have hnorm := eight_six_relative_image_normality ctx hlength previous D L Q hD hL hQ
    data E A0 actor geom hedge action.rangeRestrict action.rangeRestrict_surjective
      (by rw [MonoidHom.ker_rangeRestrict]; exact hkernel)
  have hFnormal : F.Normal := hnorm.1
  let _ := hFnormal
  have hRF : (R.subgroupOf P).map action.rangeRestrict ≤ F := hnorm.2.1
  let _ : IsInvariant (⊤ : Subgroup X) W M :=
    commutatorAction_isInvariant_of_normalizing_actor ⊤ F (by
      rw [Subgroup.normalizer_eq_top])
  have hpacket := eight_six_selected_residual_decomposition ctx hcenter hquot hlength hcard
    previous D L Q hprev data E A0 actor geom hcore hedge hD hL
  have hYeq : Y = ⁅V,R⁆ := hpacket.1
  have hYV : Y ≤ V := hpacket.2.2.ge.trans' le_sup_left
  have hYimage : (Y.subgroupOf V).map π =
      commutatorAction ((R.subgroupOf P).map action.rangeRestrict) W := by
    rw [hYeq,← commutatorAction_map_actor_subtype X ((R.subgroupOf P).map action.rangeRestrict),
      Subgroup.map_map]
    exact (Subgroup.quotient_conjugation_commutatorAction_eq_image P V Z R hPV hRP hN action haction).symm
  have hYM : (Y.subgroupOf V).map π ≤ M := by
    rw [hYimage]
    change commutatorAction ((R.subgroupOf P).map action.rangeRestrict) W ≤ commutatorAction F W
    rw [commutatorAction_eq_closure,commutatorAction_eq_closure]
    apply Subgroup.closure_mono
    rintro w ⟨r,v,rfl⟩
    exact ⟨⟨r,hRF r.property⟩,v,rfl⟩
  have hZaU : ZAt Γ cp.a ≤ conjugateClosure (ZAt Γ cp.a) E := by
    intro z hz
    exact Subgroup.subset_closure ⟨(1:E),⟨z,hz⟩,by simp⟩
  have hZaY : ZAt Γ cp.a ≤ Y := hZaU.trans
    (eight_six_selected_orbit_le_residual_commutator ctx hcenter hquot hlength hcard
      previous D L Q hprev data E A0 actor geom hcore hedge hD hL)
  let K := (M.comap π).map V.subtype
  have hZaK : ZAt Γ cp.a ≤ K := by
    intro z hz
    exact ⟨⟨z,hYV (hZaY hz)⟩,hYM (Subgroup.mem_map_of_mem π (hZaY hz)),rfl⟩
  have hPK : P ≤ Subgroup.normalizer (K : Set G) := by
    apply Subgroup.le_normalizer_iff.mpr
    rintro p hp k ⟨v,hv,rfl⟩
    let pP : P := ⟨p,hp⟩
    have hm : action pP (π v) ∈ M :=
      (IsInvariant.invariant (A := (⊤ : Subgroup X)) (G := W) (H := M)
        ⟨action.rangeRestrict pP,Subgroup.mem_top _⟩ (π v)).mp hv
    rw [haction] at hm
    exact ⟨⟨p*(v:G)*p⁻¹,(Subgroup.mem_normalizer_iff.mp (hPV hp) v).mp v.property⟩,hm,rfl⟩
  have hVK : V ≤ K := by
    change VAt Γ cp.firstStep ≤ K
    rw [eight_six_neighbor_join_eq_conjugate_closure ctx.sectionSeven Γ cp.firstStep cp.a
      ((mem_neighborhood_iff_adjacent Γ).mpr (Γ.adjacent_symm cp.firstStep_adj))]
    exact eight_six_conjugate_closure_le _ _ _ hZaK hPK
  have hMtop : M = ⊤ := by
    apply top_unique
    intro w _
    obtain ⟨v,rfl⟩ := QuotientGroup.mk'_surjective (Z.subgroupOf V) w
    obtain ⟨m,hm,heq⟩ := hVK v.property
    have heq' : m = v := Subtype.ext heq
    exact heq' ▸ hm
  have hWcard : Nat.card W = 16 := by
    rw [hMtop,Nat.card_congr Subgroup.topEquiv.toEquiv] at hMcard
    exact hMcard
  refine ⟨hWcard,?_⟩
  have hZV : Z ≤ V := (eight_six_first_step_fixed_line_local ctx hcenter hcard).2.trans
    (lemma_seven_four ctx.sectionSeven Γ cp).first_containment.1
  have hVcount := Subgroup.card_eq_card_quotient_mul_card_subgroup (Z.subgroupOf V)
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZV).toEquiv] at hVcount
  change Nat.card V = Nat.card W * Nat.card Z at hVcount
  rw [hWcard,(eight_six_first_step_fixed_line_local ctx hcenter hcard).1] at hVcount
  have hYcard := (eight_six_cost_four_residual_card ctx hcenter hquot hlength hcard
    previous D L Q hprev data E A0 actor geom hcore hedge hD hL ha hout hlarge hmin hQ hcost).1
  exact (Subgroup.eq_of_le_of_card_ge hYV (by
    change Nat.card Y = 32 at hYcard
    omega)).symm
end Stellmacher.SectionEight
