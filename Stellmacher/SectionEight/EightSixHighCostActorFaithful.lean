module
public import Stellmacher.SectionEight.EightSixHighCostActorImage
public import Theory.GroupTheory.NormalThreeHallCentralizer
public import Theory.GroupTheory.PCoreKernelRange
/-!
# Faithfulness of the actual high-cost binary actor on the residual

Keep the original high-cost local configuration and its supplied literal
Vnext/Znext action with exact two-core kernel. The image of A meets the
centralizer of the full residual image trivially. This is the faithfulness
criterion for the original conjugation action on that residual image.

Work in the literal range X of the supplied action. Residual functoriality
identifies the residual image F with O²(X), so X/F is a two-group. The
proved source-(20) input already makes F a three-group, and exactness of
the kernel gives O₂(X)=1. Solvability descends from the next stabilizer.
The normal Hall self-centralizer theorem gives C_X(F)≤F. The actor image
is a two-group by the actual Frattini calculation, so it meets F trivially.
Embedding X back in the original automorphism group proves the assertion.

This gives the faithful actor input to Stellmacher (8.6)(21), printed p.45.
It uses the prior three-group result and does not depend circularly on the
later elementary or rank-four residual conclusion. Whole fixed-point
triviality and Sylow transitivity of fixed factors are separate inputs.
-/

namespace Stellmacher.SectionEight
open Later SectionsFiveToSeven CosetGraphContext SevenSix
open scoped IsMulCommutative
universe u
public theorem eight_six_high_cost_actor_residual_centralizer_trivial
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
      Abar ⊓ Subgroup.centralizer (F : Set (MulAut W)) = ⊥ := by
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
  let Ai := A.subgroupOf P
  let Abar := Ai.map action
  let R := (twoResidualIn P).subgroupOf P
  let F := R.map action
  let X := action.range
  let Fi := R.map action.rangeRestrict
  let Aj := Ai.map action.rangeRestrict
  have hAdata := eight_six_high_cost_actor_image_data ctx hcenter hquot hlength hcard
    previous D L Q hprev data E A0 actor geom hcore hedge hD hL
    ha hout hlarge hmin hQ hhigh helementary hN hW action haction hkernel
  let _ : IsElementaryAbelian 2 Abar := hAdata.1
  have hF3 : IsPGroup 3 F := eight_six_next_residual_action_is_three_group ctx hcenter hquot
    hlength hcard previous D L Q hprev data E A0 actor geom hcore hedge hD hL
    hN hW action haction hkernel.ge
  have hmapF : Fi.map X.subtype = F := by rw [Subgroup.map_map]; rfl
  have hmapA : Aj.map X.subtype = Abar := by rw [Subgroup.map_map]; rfl
  have hFi3 : IsPGroup 3 Fi := by
    have hm : IsPGroup 3 (Fi.map X.subtype) := hmapF.symm ▸ hF3
    exact hm.of_equiv (Fi.equivMapOfInjective X.subtype X.subtype_injective).symm
  have hAj2 : IsPGroup 2 Aj := by
    have hm : IsPGroup 2 (Aj.map X.subtype) := hmapA.symm ▸ IsElementaryAbelian.isPGroup 2 Abar
    exact hm.of_equiv (Aj.equivMapOfInjective X.subtype X.subtype_injective).symm
  have hR : R = BenderSuzuki.External.hktPResidual 2 P := by
    change ((twoResidualSubgroup P).map P.subtype).subgroupOf P = _
    exact (Subgroup.comap_map_eq_self_of_injective P.subtype_injective _).trans
      (SectionThree.twoResidualSubgroup_eq_hktPResidual' P)
  have hFi : Fi = BenderSuzuki.External.hktPResidual 2 X := by
    change R.map action.rangeRestrict = _
    rw [hR]
    exact hktPResidual_map_of_surjective' action.rangeRestrict action.rangeRestrict_surjective
  let _ : Fi.Normal := by rw [hFi]; exact BenderSuzuki.External.hktPResidual_normal
  have hquot : IsPGroup 2 (X ⧸ Fi) := by
    let _ : (BenderSuzuki.External.hktPResidual 2 X).Normal := BenderSuzuki.External.hktPResidual_normal
    exact BenderSuzuki.External.hktPResidual_quotient_isPGroup.of_equiv
      (QuotientGroup.quotientMulEquivOfEq hFi).symm
  have hsolv : Group.IsSolvable P := (edge_local_data ctx.sectionSeven Γ cp).2.2
  let _ := hsolv
  have hself : Subgroup.centralizer (Fi : Set X) ≤ Fi :=
    Subgroup.centralizer_normal_three_le_of_two_quotient
      (Group.isSolvable_of_surjective action.rangeRestrict_surjective)
      (pCore_range_eq_bot_of_ker_eq_pCore 2 action hkernel) Fi hFi3 hquot
  have hdisjoint : Disjoint Aj Fi := IsPGroup.disjoint_of_ne 2 3 (by decide) Aj Fi hAj2 hFi3
  apply bot_unique
  intro a ha
  obtain ⟨lift,hlift,heq⟩ := ha.1
  let x : X := action.rangeRestrict lift
  have hxA : x ∈ Aj := Subgroup.mem_map_of_mem action.rangeRestrict hlift
  have hxC : x ∈ Subgroup.centralizer (Fi : Set X) := by
    rw [Subgroup.mem_centralizer_iff]
    intro f hf
    apply Subtype.ext
    have hfF : (f:MulAut W) ∈ F := hmapF ▸ Subgroup.mem_map_of_mem X.subtype hf
    have hh := Subgroup.mem_centralizer_iff.mp ha.2 f hfF
    change (f:MulAut W)*action lift = action lift*(f:MulAut W)
    rw [heq]
    exact hh
  have hx1 : x = 1 := hdisjoint.le_bot ⟨hxA,hself hxC⟩
  exact heq.symm.trans (congrArg Subtype.val hx1)
end Stellmacher.SectionEight
