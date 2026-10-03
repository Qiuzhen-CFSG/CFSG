module
public import Stellmacher.SectionEight.EightSixSelectedActorNontransvection
public import Stellmacher.SectionEight.EightSixActorCostPower

/-!
The actual minimum-cost actor in the large-index configuration has cost four,
or every predecessor actor outside the next core has cost at least eight.
The displacement index modulo the residual-fixed subgroup is at most the
original cost modulo the next center: both denominators are normal in Vnext,
and the center is contained in the fixed subgroup. The nontransvection theorem
therefore makes the original cost greater than two. Its power-of-two form
gives the two numerical alternatives, and the supplied minimum propagates
the second one to all actors.

This assembles the exact branch split preceding (15) in Stellmacher's proof
of (8.6), printed p.44. It preserves the actual selected subgroups and
minimum, and uses no raw small-action recognition or assumed case model.
-/

namespace Stellmacher.SectionEight
open Later SectionsFiveToSeven CosetGraphContext
universe u

public theorem eight_six_residual_fixed_cost_le_actor_cost
    {G : Type u} [Group G] [Finite G] {S P1 P2 : Subgroup G}
    (ctx : SectionEightLocalContext G S P1 P2)
    (hcenter : ZAt ctx.Γ ctx.criticalPath.firstStep ≤
      CenterAmbient (GAt ctx.Γ ctx.criticalPath.firstStep))
    (hlength : ctx.criticalPath.length = 2)
    (hcard : Nat.card (ZAt ctx.Γ ctx.criticalPath.a) = 4)
    (hcomm : ⁅VAt ctx.Γ ctx.criticalPath.firstStep,QAt ctx.Γ ctx.criticalPath.firstStep⁆ =
      ZAt ctx.Γ ctx.criticalPath.firstStep)
    (E : Subgroup G) (hE : E ≤ GAt ctx.Γ ctx.criticalPath.firstStep)
    (actor : G) (ha : actor ∈ GAt ctx.Γ ctx.criticalPath.firstStep) :
    (VAt ctx.Γ ctx.criticalPath.firstStep ⊓ Subgroup.centralizer (twoResidualIn E : Set G)).relIndex
      (⁅VAt ctx.Γ ctx.criticalPath.firstStep,Subgroup.zpowers actor⁆ ⊔
        (VAt ctx.Γ ctx.criticalPath.firstStep ⊓ Subgroup.centralizer (twoResidualIn E : Set G))) ≤
      eightSixCommutatorCost ctx.Γ ctx.criticalPath actor := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let V := VAt Γ cp.firstStep
  let Z := ZAt Γ cp.firstStep
  let C := V ⊓ Subgroup.centralizer (twoResidualIn E : Set G)
  let J := ⁅V,Subgroup.zpowers actor⁆
  have hVR : V ≤ QAt Γ cp.firstStep := eight_six_neighborhood_closure_le_core Γ cp
    (by exact hlength ▸ by decide) _
  have hZV : Z ≤ V := (eight_six_first_step_fixed_line_local ctx hcenter hcard).2.trans
    (lemma_seven_four ctx.sectionSeven Γ cp).first_containment.1
  have hZC : Z ≤ C := le_inf hZV
    ((hcenter.trans (SevenSix.centerAmbient_le_centralizer _)).trans
      (Subgroup.centralizer_le ((SevenSix.twoResidualIn_le E).trans hE)))
  have hJV : J ≤ V := Subgroup.le_normalizer_iff_commutator_le_left.mp
    ((Subgroup.zpowers_le.mpr ha).trans (stabilizer_le_normalizer_v Γ cp.firstStep))
  have hVNC : V ≤ Subgroup.normalizer (C : Set G) :=
    Subgroup.le_normalizer_iff_commutator_le_right.mpr
      (((Subgroup.commutator_mono le_rfl (inf_le_left.trans hVR)).trans_eq hcomm).trans hZC)
  have hVNZ : V ≤ Subgroup.normalizer (Z : Set G) :=
    (Subgroup.centralizer_le_normalizer _).trans'
      (Subgroup.le_centralizer_iff.mp ((hcenter.trans (SevenSix.centerAmbient_le_centralizer _)).trans
        (Subgroup.centralizer_le (hVR.trans (by
          change Γ.twoCoreAt _ ≤ Γ.vertexStabilizer _
          rw [Γ.twoCoreAt_def]
          exact Subgroup.map_subtype_le _)))))
  let _ : (C.subgroupOf V).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hVNC
  let _ : (Z.subgroupOf V).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hVNZ
  have hCindex := Subgroup.relIndex_sup_right (J.subgroupOf V) (C.subgroupOf V)
  rw [← Subgroup.subgroupOf_sup hJV (show C ≤ V from inf_le_left),
    Subgroup.relIndex_subgroupOf (sup_le hJV inf_le_left),
    Subgroup.relIndex_subgroupOf hJV] at hCindex
  have hZindex := Subgroup.relIndex_sup_right (J.subgroupOf V) (Z.subgroupOf V)
  rw [← Subgroup.subgroupOf_sup hJV hZV,
    Subgroup.relIndex_subgroupOf (sup_le hJV hZV),
    Subgroup.relIndex_subgroupOf hJV] at hZindex
  change C.relIndex (J ⊔ C) ≤ Z.relIndex (J ⊔ Z)
  rw [hCindex,hZindex]
  exact Subgroup.relIndex_le_of_le_left hZC (Z.subgroupOf J).index_ne_zero_of_finite


public theorem eight_six_selected_actor_cost_cases
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
          eightSixCommutatorCost ctx.Γ ctx.criticalPath other) :
    eightSixCommutatorCost ctx.Γ ctx.criticalPath actor = 4 ∨
      ∀ other : G, other ∈ VAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.a →
        other ∉ QAt ctx.Γ ctx.criticalPath.firstStep →
          8 ≤ eightSixCommutatorCost ctx.Γ ctx.criticalPath other := by
  have hAE : VAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.a ≤ E :=
    geom.generated ▸ le_sup_left
  have haP := geom.group_le (hAE ha)
  have hraw := eight_six_selected_actor_not_transvection ctx hcenter hquot hlength hcard
    previous D L Q hprev data E A0 actor geom hcore hedge hD hL ha hout hlarge hmin
  have hcompare := eight_six_residual_fixed_cost_le_actor_cost ctx hcenter hlength hcard
    data.first_commutator E geom.group_le actor haP
  have hcost := eight_six_actor_cost_eq_four_or_ge_eight ctx hlength actor haP
    (lt_of_lt_of_le hraw hcompare)
  rcases hcost with hfour | hlargeCost
  · exact Or.inl hfour
  · exact Or.inr (fun other hother houtside => hlargeCost.trans (hmin other hother houtside))

end Stellmacher.SectionEight
