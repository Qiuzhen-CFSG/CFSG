module
public import Stellmacher.SectionEight.EightSixSelectedFixedSupportObstruction
public import Stellmacher.SectionEight.EightSixTransvectionFixedSpan

/-!
# The selected actor is not a transvection in Stellmacher (8.6)(13)

For the actual selected minimizing actor in the large-index branch, its
displacement on the next module modulo the residual-fixed subgroup has
order strictly greater than two. The conclusion uses the literal subgroup
C=Vnext∩C_G(O²(E)) and the exact relative index of [Vnext,⟨actor⟩] joined
with C over C. All selected subgroups and the original cost minimum are
retained; no action model or transvection-exclusion premise is introduced.

First exclude index one. The selected actor's nonzero orbit-commutator
line spans the initial center modulo the next line. If the full
displacement lay in C, this orbit commutator would lie in V0∩D=Znext,
contradicting the two center orders. Index two would force the actual
supported/fixed decomposition by the proved two-conjugate transvection
argument. The minimizing-actor obstruction excludes that decomposition.
Positivity and these two exclusions give the strict bound.

Source: Stellmacher (8.6), printed pp.43–44, assertion (13),
`refs/files/stellmacher-n-group.pdf`. The strict numerical form also
supplies the nontriviality needed by the source-(14) fixed-core containment.
-/

namespace Stellmacher.SectionEight
open Later SectionsFiveToSeven CosetGraphContext
open scoped commutatorElement Pointwise
universe u

private theorem eight_six_selected_actor_fixed_quotient_index_gt_one
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
    (ha : actor ∈ VAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.a) :
    let C := VAt ctx.Γ ctx.criticalPath.firstStep ⊓
      Subgroup.centralizer (twoResidualIn E : Set G)
    1 < C.relIndex (⁅VAt ctx.Γ ctx.criticalPath.firstStep, Subgroup.zpowers actor⁆ ⊔ C) := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let V := VAt Γ cp.firstStep
  let Z := ZAt Γ cp.firstStep
  let U := conjugateClosure (ZAt Γ cp.a) E
  let C := V ⊓ Subgroup.centralizer (twoResidualIn E : Set G)
  let V0 := QAt Γ cp.firstStep ⊓ Subgroup.centralizer (twoResidualIn E : Set G)
  let J := ⁅V,Subgroup.zpowers actor⁆ ⊔ C
  change 1 < C.relIndex J
  apply Nat.one_lt_iff_ne_zero_and_ne_one.mpr
  refine ⟨show (C.subgroupOf J).index ≠ 0 from Subgroup.index_ne_zero_of_finite, ?_⟩
  intro hone
  have hJC : J ≤ C := Subgroup.relIndex_eq_one.mp hone
  have hUV : U ≤ V := eight_six_conjugate_closure_le _ _ _
    (lemma_seven_four ctx.sectionSeven Γ cp).first_containment.1
    (geom.group_le.trans (stabilizer_le_normalizer_v Γ cp.firstStep))
  have hactive := eight_six_selected_actor_active_line ctx hcenter hquot hlength hcard
    previous D L Q hprev data E A0 actor geom hcore hedge hD hL ha
  have hZaD : ZAt Γ cp.a ≤ D := by
    rw [←data.residual_commutator]
    exact Subgroup.le_normalizer_iff_commutator_le_left.mp
      ((SevenSix.twoResidualIn_le L).trans (data.closure_le.trans
        ((Subgroup.normal_subgroupOf_iff_le_normalizer data.intersection_normal.1).mp
          data.intersection_normal.2)))
  have hVR : V ≤ QAt Γ cp.firstStep := SevenSix.neighbor_join_le_core_of_length_gt_one
    Γ cp (by exact hlength ▸ by decide) _
  have hCV0 : C ≤ V0 := inf_le_inf_right _ hVR
  have hR0 : ⁅U,Subgroup.zpowers actor⁆ ≤ V0 :=
    (Subgroup.commutator_mono hUV le_rfl).trans ((le_sup_left.trans hJC).trans hCV0)
  have hRD : ⁅U,Subgroup.zpowers actor⁆ ≤ D :=
    (le_sup_left.trans_eq hactive).trans hZaD
  have hRZ : ⁅U,Subgroup.zpowers actor⁆ ≤ Z :=
    (le_inf hR0 hRD).trans_eq
      (eight_six_selected_fixed_core_intersection ctx hcenter hquot hlength hcard
        previous D L Q hprev hD hL data E A0 actor geom hedge)
  have heq : ZAt Γ cp.a = Z := hactive.symm.trans (sup_eq_right.mpr hRZ)
  have hline : Nat.card Z = 2 := (eight_six_first_step_fixed_line_local ctx hcenter hcard).1
  have hZa : Nat.card (ZAt Γ cp.a) = 2 := heq ▸ hline
  change Nat.card (ZAt Γ cp.a) = 4 at hcard
  omega

public theorem eight_six_selected_actor_not_transvection
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
    let C := VAt ctx.Γ ctx.criticalPath.firstStep ⊓
      Subgroup.centralizer (twoResidualIn E : Set G)
    2 < C.relIndex (⁅VAt ctx.Γ ctx.criticalPath.firstStep, Subgroup.zpowers actor⁆ ⊔ C) := by
  let C := VAt ctx.Γ ctx.criticalPath.firstStep ⊓
    Subgroup.centralizer (twoResidualIn E : Set G)
  let J := ⁅VAt ctx.Γ ctx.criticalPath.firstStep, Subgroup.zpowers actor⁆ ⊔ C
  change 2 < C.relIndex J
  have hpositive : 1 < C.relIndex J :=
    eight_six_selected_actor_fixed_quotient_index_gt_one ctx hcenter hquot hlength hcard
      previous D L Q hprev data E A0 actor geom hcore hedge hD hL ha
  have hnot : C.relIndex J ≠ 2 := by
    intro htwo
    have hsplit := eight_six_transvection_fixed_span ctx hcenter hlength hcard
      data.first_commutator previous E A0 actor geom hedge ha htwo
    exact eight_six_selected_no_fixed_support_split ctx hcenter hquot hlength hcard
      previous D L Q hprev data E A0 actor geom hcore hedge hD hL ha hout hlarge hmin hsplit
  omega

end Stellmacher.SectionEight

