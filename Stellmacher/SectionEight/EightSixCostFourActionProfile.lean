module
public import Stellmacher.SectionEight.EightSixCostFourActorIndices
public import Stellmacher.SectionEight.EightSixSelectedUniformCost
public import Theory.GroupAction.InvolutionDisplacementCard

/-!
# The literal cost-four actor image

Retain the selected telescope of Stellmacher (8.6), its actual next quotient
Vnext/Znext, and a supplied next-stabilizer conjugation action with its
original normality proof. In the cost-four branch the predecessor actor
image is elementary abelian of order four, and each nonidentity image
has fixed subgroup of index four.

The selected uniform-cost theorem identifies the action kernel on the
predecessor actor exactly with its intersection with D: an actor outside
the next core has displacement order four and cannot be in the kernel.
The proved actor index then gives image order four. Squares lie in the
Frattini subgroup of the actual Q and hence in D, so the image has
exponent two. The involution fixed/displacement cardinality identity turns
the uniform displacement order into the individual fixed indices.

Together with the separate full fixed-index-eight theorem, this supplies
the numerical premises for the bounded (1.6) application. It assumes no
faithful quotient model, action-kernel equality, or bounded classification
conclusion. Source: Stellmacher, Journal of Algebra 190 (1997), proof of
(8.6), printed p.44, the cost-four paragraph following relation (14).
-/

namespace Stellmacher.SectionEight
open Later SectionsFiveToSeven CosetGraphContext SevenSix
open scoped commutatorElement IsMulCommutative
universe u
public theorem eight_six_cost_four_action_profile
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
      let B := ((VAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.a).subgroupOf P).map action
      IsElementaryAbelian 2 B ∧ Nat.card B = 4 ∧
        ∀ t ∈ B, t ≠ 1 → (FixedPoints.subgroup (Subgroup.zpowers t)
          (V ⧸ Z.subgroupOf V)).index = 4 := by
  classical
  let _ := hN
  dsimp only
  intro hW action haction hkernel
  let _ := hW
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let P := GAt Γ cp.firstStep
  let V := VAt Γ cp.firstStep
  let Z := ZAt Γ cp.firstStep
  let A := VAt Γ previous ⊓ QAt Γ cp.a
  let R := QAt Γ cp.firstStep
  let W := V ⧸ Z.subgroupOf V
  let B := (A.subgroupOf P).map action
  have hAE : A ≤ E := geom.generated ▸ le_sup_left
  have hAP : A ≤ P := hAE.trans geom.group_le
  have hPV : P ≤ Subgroup.normalizer (V : Set G) := stabilizer_le_normalizer_v Γ _
  have hZV : Z ≤ V := (eight_six_first_step_fixed_line_local ctx hcenter hcard).2.trans
    (lemma_seven_four ctx.sectionSeven Γ cp).first_containment.1
  have hAQ : A ≤ Q := data.core_generation ▸ le_sup_of_le_left le_sup_left
  have hQtwo : IsPGroup 2 Q := by
    rw [hQ,twoCoreIn]
    exact (pCore_isPGroup (p := 2)).map _
  let _ : Fact (IsPGroup 2 Q) := ⟨hQtwo⟩
  have hRnative : R.subgroupOf P = pCore 2 P := by
    change (Γ.twoCoreAt _).subgroupOf P = _
    rw [Γ.twoCoreAt_def]
    exact Subgroup.comap_map_eq_self_of_injective P.subtype_injective _
  have hsquare (a : P) (ha : (a:G) ∈ A) : (action a)^2 = 1 := by
    have hpowD : (a:G)^2 ∈ D := data.core_frattini_le
      (Subgroup.mem_map.mpr ⟨(⟨a,hAQ ha⟩:Q)^2,
        pth_power_mem_frattini_of_isPGroup (p := 2) (⟨a,hAQ ha⟩:Q),rfl⟩)
    rw [← map_pow]
    apply MonoidHom.mem_ker.mp
    apply hkernel
    rw [← hRnative]
    exact (hD ▸ hpowD).2
  have hcostOf (a : P) : Nat.card (commutatorAction (Subgroup.zpowers (action a)) W) =
      eightSixCommutatorCost Γ cp (a:G) := by
    have hcyclic : (Subgroup.zpowers (a:G)).subgroupOf P = Subgroup.zpowers a := by
      apply Subgroup.map_injective P.subtype_injective
      rw [Subgroup.map_subgroupOf_eq_of_le (Subgroup.zpowers_le.mpr a.property),
        MonoidHom.map_zpowers]
      rfl
    have hh := Subgroup.quotient_conjugation_commutatorAction_card P V Z
      (Subgroup.zpowers (a:G)) hPV (Subgroup.zpowers_le.mpr a.property) hN action haction
    rw [hcyclic,MonoidHom.map_zpowers] at hh
    have hAV : ⁅V,Subgroup.zpowers (a:G)⁆ ≤ V :=
      Subgroup.le_normalizer_iff_commutator_le_left.mp
        ((Subgroup.zpowers_le.mpr a.property).trans hPV)
    have hrel := Subgroup.relIndex_sup_right
      ((⁅V,Subgroup.zpowers (a:G)⁆).subgroupOf V) (Z.subgroupOf V)
    rw [← Subgroup.subgroupOf_sup hAV hZV,
      Subgroup.relIndex_subgroupOf (sup_le hAV hZV),
      Subgroup.relIndex_subgroupOf hAV] at hrel
    exact hh.trans hrel.symm
  have huniform := eight_six_selected_all_actor_costs ctx hcenter hquot hlength hcard
    previous D L Q hprev data E A0 actor geom hcore hedge hD hL ha hout hlarge hmin hQ
  have hfix (a : P) (ha : (a:G) ∈ A) : action a = 1 ↔ (a:G) ∈ R := by
    constructor
    · intro htrivial
      by_contra houtside
      have hfour := (huniform a ha houtside).trans hcost
      rw [← hcostOf a,htrivial] at hfour
      have hone : commutatorAction (Subgroup.zpowers (1 : MulAut W)) W = ⊥ := by
        apply bot_unique
        rw [commutatorAction_eq_closure,Subgroup.closure_le]
        rintro w ⟨b,v,rfl⟩
        have hb : (b : MulAut W) = 1 := by
          obtain ⟨n,hn⟩ := b.property
          simpa only [one_zpow] using hn.symm
        change v⁻¹ * (b : MulAut W) v = 1
        rw [hb]
        exact inv_mul_cancel v
      rw [hone,Subgroup.card_bot] at hfour
      norm_num at hfour
    · intro haR
      apply MonoidHom.mem_ker.mp
      apply hkernel
      rw [← hRnative]
      exact haR
  have hBsquares : ∀ b : B, b^2=1 := by
    intro b
    obtain ⟨a,ha,heq⟩ := b.property
    apply Subtype.ext
    change (b : MulAut W)^2 = 1
    rw [← heq]
    exact hsquare a ha
  have helem : IsElementaryAbelian 2 B := {
    is_comm := ⟨fun b c =>
      (Commute.of_orderOf_dvd_two
        (fun e => orderOf_dvd_of_pow_eq_one (hBsquares e)) b c).eq⟩
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr hBsquares }
  have hBcard : Nat.card B = 4 := by
    let f : A →* MulAut W := action.comp (Subgroup.inclusion hAP)
    have hrange : f.range = B := by
      ext t
      constructor
      · rintro ⟨a,rfl⟩
        exact ⟨⟨a,hAP a.property⟩,a.property,rfl⟩
      · rintro ⟨a,ha,rfl⟩
        exact ⟨⟨a,ha⟩,rfl⟩
    have hAprev : A ≤ QAt Γ previous := inf_le_left.trans
      (neighbor_join_le_core_of_length_gt_one Γ cp (by exact hlength ▸ by decide) previous)
    have hker : f.ker = (A ⊓ D).subgroupOf A := by
      ext a
      change action (⟨a,hAP a.property⟩:P) = 1 ↔ (a:G) ∈ A ⊓ D
      rw [hfix _ a.property]
      constructor
      · intro haR
        exact ⟨a.property,hD ▸ ⟨hAprev a.property,haR⟩⟩
      · intro had
        exact (hD ▸ had.2).2
    rw [← hrange,← Subgroup.index_ker,hker]
    have hcount := ((A ⊓ D).subgroupOf A).index_mul_card
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (show A ⊓ D ≤ A from inf_le_left)).toEquiv] at hcount
    have hindices := (eight_six_cost_four_actor_indices ctx hcenter hquot hlength hcard
      previous D L Q hprev data E A0 actor geom hcore hedge hD hL ha hout hlarge hmin hQ hcost).1
    change Nat.card A = 4 * Nat.card (A ⊓ D : Subgroup G) at hindices
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos (hcount.trans hindices)
  refine ⟨helem,hBcard,?_⟩
  rintro t ⟨a,ha,rfl⟩ ht
  have haout : (a:G) ∉ R := fun hmem => ht ((hfix a ha).mpr hmem)
  have hdisp : Nat.card (commutatorAction (Subgroup.zpowers (action a)) W) = 4 :=
    (hcostOf a).trans ((huniform a ha haout).trans hcost)
  have hcount := (MulAut.involution_fixed_displacement_card_data (action a) (hsquare a ha)).1
  rw [hdisp] at hcount
  have hindex := (FixedPoints.subgroup (Subgroup.zpowers (action a)) W).card_mul_index
  exact Nat.eq_of_mul_eq_mul_left Nat.card_pos (hindex.trans hcount)
end Stellmacher.SectionEight
