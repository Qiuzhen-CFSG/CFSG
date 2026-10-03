module
public import Stellmacher.SectionEight.EightSixSelectedOrbitIntersection
public import Stellmacher.SectionEight.EightSixSelectedOrbitCardEight
public import Stellmacher.SectionEight.GeneratedEightSixSmallIndexInverterSelection
public import Stellmacher.SectionEight.GeneratedEightSixNeighborGeneration
public import Theory.GroupTheory.ElementaryEightPlaneFullRestriction

/-!
The selected elementary eight in Stellmacher (8.6) has a conjugation image
of order twenty-four under the actual closure L. This image preserves the
initial center plane. The complete selected telescope is retained, including
the high-cost hypothesis and the definition of Q as the two-core of L;
these give the required normality of the eight in L.

The equation-one Sylow identity and neighbor generation give Ga = Qa L.
Since Qa centralizes the initial plane, the full action of Ga on that plane
is already induced by L. Restricting the literal conjugation image to the
plane therefore has image of order six. Its kernel cannot be trivial:
the selected subgroup A lies in Qa and L, and the nonzero commutator
[U,A], together with the next center line, spans the initial plane.
The elementary-eight full-restriction theorem then gives image order
twenty-four. The restriction uses explicit subgroup equivalences, so its
pointwise formula agrees with the original conjugation map.

Source: Stellmacher, Journal of Algebra 190 (1997), Lemma (8.6), printed
p.44, the normalizer argument following assertion (16). This result supplies
the initial plane stabilizer used in the neighboring-plane normalizer proof.
-/

namespace Stellmacher.SectionEight
open Later SectionsFiveToSeven CosetGraphContext
open scoped Pointwise
universe u

public theorem eight_six_selected_plane_image_card
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
    (hhigh : ∀ mover : G, mover ∈ VAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.a →
      mover ∉ QAt ctx.Γ ctx.criticalPath.firstStep →
        8 ≤ eightSixCommutatorCost ctx.Γ ctx.criticalPath mover)
    (hQ : Q = twoCoreIn L) :
    let U := conjugateClosure (ZAt ctx.Γ ctx.criticalPath.a) E
    ∃ hLN : L ≤ Subgroup.normalizer (U : Set G),
      let f : L →* MulAut U := U.normalizerMonoidHom.comp (Subgroup.inclusion hLN)
      Nat.card f.range = 24 ∧
      ∀ j ∈ f.range, ((ZAt ctx.Γ ctx.criticalPath.a).subgroupOf U).map
        j.toMonoidHom = (ZAt ctx.Γ ctx.criticalPath.a).subgroupOf U := by
  classical
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let U := conjugateClosure (ZAt Γ cp.a) E
  let Z := ZAt Γ cp.a
  let A := VAt Γ previous ⊓ QAt Γ cp.a
  have hnorm := eight_six_selected_orbit_normal_in_closure ctx hcenter hquot hlength
    hcard previous D L Q hprev data E A0 actor geom hcore hedge hD hL hhigh hQ
  have hLN : L ≤ Subgroup.normalizer (U : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hnorm.1).mp hnorm.2
  refine ⟨hLN, ?_⟩
  let f : L →* MulAut U := U.normalizerMonoidHom.comp (Subgroup.inclusion hLN)
  let W := Z.subgroupOf U
  have hZaU : Z ≤ U := by
    intro z hz
    exact Subgroup.subset_closure ⟨(1:E),⟨z,hz⟩,by simp⟩
  have hLZ : L ≤ Subgroup.normalizer (Z : Set G) :=
    data.closure_le.trans (stabilizer_le_normalizer_z Γ cp.a)
  have hformula (l : L) (u : U) : (f l u : G) = (l:G)*(u:G)*(l:G)⁻¹ := by
    rfl
  have hstable (j : MulAut U) (hj : j∈f.range) (u : U) : u∈W ↔ j u∈W := by
    obtain ⟨l,rfl⟩ := hj
    change (u:G)∈Z ↔ (f l u:G)∈Z
    rw [hformula]
    exact Subgroup.mem_normalizer_iff.mp (hLZ l.property) u
  have hmap (j : MulAut U) (hj : j∈f.range) : W.map j.toMonoidHom=W := by
    apply le_antisymm
    · rintro _ ⟨w,hw,rfl⟩
      exact (hstable j hj w).mp hw
    · intro w hw
      refine ⟨j.symm w, ?_, j.apply_symm_apply w⟩
      apply (hstable j hj _).mpr
      simpa using hw
  let restriction : f.range →* MulAut W := {
    toFun := fun j => (j.val.subgroupMap W).trans (MulEquiv.subgroupCongr (hmap j j.property))
    map_one' := by ext w; rfl
    map_mul' := by intro j k; ext w; rfl }
  have hrestriction (j : f.range) (w : W) : (restriction j w : U)=(j:MulAut U) w := rfl
  have hfirst : cp.firstStep ∈ Neighborhood Γ cp.a :=
    (SevenSix.mem_neighborhood_iff_adjacent Γ).mpr cp.firstStep_adj
  have hZQ : Z ≤ Subgroup.centralizer (QAt Γ cp.a : Set G) :=
    ((lemma_seven_three ctx.sectionSeven Γ).center_core _ _ hfirst).trans
      ((SevenSix.omegaOneCenter_le_centerAmbient _).trans
        (SevenSix.centerAmbient_le_centralizer _))
  have hQaZ : QAt Γ cp.a ≤ Subgroup.centralizer (Z : Set G) :=
    Subgroup.le_centralizer_iff.mp hZQ
  have hprevL : VAt Γ previous ≤ L := by
    intro v hv
    rw [hL]
    exact Subgroup.subset_closure ⟨(1:GAt Γ cp.a),
      ⟨v, SevenSix.neighbor_join_le_core_of_length_gt_one Γ cp (by change 1 < ctx.criticalPath.length; omega) previous hv⟩,
      by simp⟩
  have hnextL : VAt Γ cp.firstStep ≤ L :=
    ((le_sup_left : VAt Γ cp.firstStep ≤ VAt Γ cp.firstStep ⊔ Q).trans_eq
      data.sylow_intersection.symm).trans inf_le_left
  have hQaGa : QAt Γ cp.a ≤ GAt Γ cp.a := by
    rw [QAt, q, Γ.twoCoreAt_def]
    exact SevenSix.twoCoreIn_le _
  have hgen : QAt Γ cp.a ⊔ L = GAt Γ cp.a := by
    apply le_antisymm (sup_le hQaGa data.closure_le)
    rw [←eight_six_neighbor_generation_local ctx hquot hlength previous hprev]
    exact sup_le (sup_le le_sup_left (hnextL.trans le_sup_right))
      (hprevL.trans le_sup_right)
  have hfull (symmetry : MulAut Z) : ∃ l : L, ∀ z : Z,
      (l:G)*(z:G)*(l:G)⁻¹ = (symmetry z:G) := by
    obtain ⟨g,hg,hact⟩ := eight_six_initial_center_full_action_local ctx hcard symmetry
    have hgprod : g ∈ (QAt Γ cp.a : Set G)*(L : Set G) := by
      rw [←Subgroup.coe_mul_of_right_le_normalizer_left _ _
        (data.closure_le.trans (SevenSix.stabilizer_le_normalizer_q Γ cp.a)),hgen]
      exact hg
    obtain ⟨q,hq,l,hl,rfl⟩ := hgprod
    refine ⟨⟨l,hl⟩, fun z => ?_⟩
    have hz : l*(z:G)*l⁻¹∈Z := (Subgroup.mem_normalizer_iff.mp (hLZ hl) z).mp z.property
    have hqfix : q*(l*(z:G)*l⁻¹)*q⁻¹=l*(z:G)*l⁻¹ := by
      exact mul_inv_eq_iff_eq_mul.mpr (Subgroup.mem_centralizer_iff.mp (hQaZ hq) _ hz).symm
    calc
      l*(z:G)*l⁻¹ = q*(l*(z:G)*l⁻¹)*q⁻¹ := hqfix.symm
      _ = (q*l)*(z:G)*(q*l)⁻¹ := by group
      _ = (symmetry z:G) := hact z
  let e : W ≃* Z := Subgroup.subgroupOfEquivOfLe hZaU
  have hsurjective : Function.Surjective restriction := by
    intro symmetry
    obtain ⟨l,hl⟩ := hfull ((e.symm.trans symmetry).trans e)
    refine ⟨f.rangeRestrict l, ?_⟩
    ext w
    have hh := hl (e w)
    simp only [MulEquiv.trans_apply,MulEquiv.symm_apply_apply] at hh
    exact (hformula l w).trans hh
  have hW : Nat.card W=4 := by
    rw [Nat.card_congr e.toEquiv]
    exact hcard
  let _ : IsElementaryAbelian 2 U := eight_six_selected_orbit_elementary ctx E hcore
  let _ : IsElementaryAbelian 2 Z :=
    SevenSix.z_isElementaryAbelian_of_neighbor ctx.sectionSeven Γ hfirst
  let _ : IsElementaryAbelian 2 W := IsElementaryAbelian.subgroupOf hZaU
  let _ : Nontrivial W := not_subsingleton_iff_nontrivial.mp (by
    intro hs
    have hh : Nat.card W=1 := Nat.card_eq_one_iff_unique.mpr ⟨hs,inferInstance⟩
    omega)
  let _ : IsKleinFour W := ⟨hW,IsElementaryAbelian.exponent_eq_prime⟩
  have hrange : Nat.card restriction.range=6 := by
    rw [restriction.range_eq_top_of_surjective hsurjective,Subgroup.card_top]
    exact IsKleinFour.card_mulAut W
  have hAL : A≤L := inf_le_left.trans hprevL
  have hker : restriction.ker≠⊥ := by
    intro hk
    have hcentral : U ≤ Subgroup.centralizer (A : Set G) := by
      intro u hu
      apply Subgroup.mem_centralizer_iff.mpr
      intro a ha
      let l : L := ⟨a,hAL ha⟩
      have hr : restriction (f.rangeRestrict l)=1 := by
        ext w
        change a*(w.val:G)*a⁻¹=(w.val:G)
        exact mul_inv_eq_iff_eq_mul.mpr
          (Subgroup.mem_centralizer_iff.mp (hQaZ ha.2) _ w.property).symm
      have hmem : f.rangeRestrict l∈restriction.ker := MonoidHom.mem_ker.mpr hr
      rw [hk,Subgroup.mem_bot] at hmem
      have heq : f l=1 := congrArg Subtype.val hmem
      have hh := congrArg (fun j : MulAut U => (j ⟨u,hu⟩:G)) heq
      change a*u*a⁻¹=u at hh
      exact mul_inv_eq_iff_eq_mul.mp hh
    have hspan := eight_six_selected_orbit_commutator_sup_line ctx hcenter hquot hlength
      hcard previous D L Q hprev data E A0 actor geom hcore hedge hD hL
    have hz := (eight_six_first_step_fixed_line_local ctx hcenter hcard).1
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hcentral,bot_sup_eq] at hspan
    rw [hspan] at hz
    omega
  have hU : Nat.card U=8 := eight_six_selected_orbit_card_eight ctx hcenter hquot
    hlength hcard previous D L Q hprev data E A0 actor geom hcore hedge hD hL
  exact ⟨elementaryEight_plane_card_twentyfour_of_full_restriction hU W hW f.range
    restriction hrestriction hrange hker,hmap⟩

end Stellmacher.SectionEight
