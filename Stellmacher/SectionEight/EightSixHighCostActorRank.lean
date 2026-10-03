module
public import Stellmacher.SectionEight.EightSixHighCostIntersectionLower
public import Theory.ElementaryAbelian.ExtraspecialCardBound
public import Stellmacher.SectionEight.EightSixHighCostExtraspecial

/-!
# The high-cost actor quotient has order eight

For the actual selected high-cost configuration of Stellmacher (8.6), let
A=Vprevious∩Qa and D=Qprevious∩Qnext. Then |A:(A∩D)|=8. The original common
structure, geometric selector and elementary D are retained. No actor rank,
cardinality or extraspecial recognition is assumed.

The proved next core is extraspecial of order512 and equals Vnext. The
next line lies in its center and has the same order two, so the native
center lies in D. The extraspecial elementary-subgroup bound gives |D|≤32;
the two-conjugate selected-orbit calculation gives the reverse inequality.
Local transitivity transports Qnext=Vnext and its cardinality to the
predecessor. Thus D lies in A. The initial SL2(2) quotient bounds the index
of A in Vprevious by two; the actual selected residual escape excludes
index one. Consequently |A|256 and |D|32 give the desired quotient order.

Source: Stellmacher, Journal of Algebra 190 (1997), (8.6), the calculation
between (18) and (19), printed p.45, refs/files/stellmacher-n-group.pdf.
This is the rank-three actor input for the separate source-(21) argument.
-/

namespace Stellmacher.SectionEight
open Later SectionsFiveToSeven CosetGraphContext SevenSix
universe u
public theorem eight_six_high_cost_actor_rank
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
    (helementary : IsElementaryAbelianSubgroup 2 D) :
    let A := VAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.a
    QuotientCardEq A (A ⊓ D) 8 := by
  classical
  obtain ⟨hextra,hRcard⟩ := eight_six_high_cost_next_core_extraspecial ctx hcenter hquot hlength hcard
    previous D L Q hprev data E A0 actor geom hcore hedge hD hL ha hout hlarge hmin hQ hhigh helementary
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let V := VAt Γ cp.firstStep
  let R := QAt Γ cp.firstStep
  let Qa := QAt Γ cp.a
  let A := VAt Γ previous ⊓ Qa
  have hlen : cp.length = 2 := hlength
  have hselected := eight_six_selected_fixed_core_containment ctx hcenter hquot hlength
    hcard previous D L Q hprev hD hL hQ data E A0 actor geom hcore hedge ha hout hlarge hmin
  have hRV : R = V := eight_six_high_cost_next_core_eq_v ctx hcenter hquot hlength hcard
    previous D L Q hprev data E A0 actor geom hcore hedge hD hL hhigh hselected.1 helementary
  have hVcard : Nat.card V = 512 := hRV ▸ hRcard
  let _ : IsExtraspecial 2 R := hextra
  let _ : IsElementaryAbelian 2 D := helementary
  have hDR : D ≤ R := hD ▸ inf_le_right
  have hcoreData := eight_six_rigidity_core_containments ctx.sectionSeven Γ cp previous D L Q hD data
  have hZD : ZAt Γ cp.firstStep ≤ D :=
    (eight_six_first_step_fixed_line_local ctx hcenter hcard).2.trans hcoreData.2.2.1
  have hZR : ZAt Γ cp.firstStep ≤ R := hZD.trans hDR
  have hRP : R ≤ GAt Γ cp.firstStep := by
    change Γ.twoCoreAt cp.firstStep ≤ Γ.vertexStabilizer cp.firstStep
    rw [Γ.twoCoreAt_def]
    exact Subgroup.map_subtype_le _
  have hZcentral : ZAt Γ cp.firstStep ≤ Subgroup.centralizer (R : Set G) :=
    (hcenter.trans (centerAmbient_le_centralizer _)).trans (Subgroup.centralizer_le hRP)
  have hZnative : (ZAt Γ cp.firstStep).subgroupOf R ≤ Subgroup.center R := by
    intro z hz
    rw [Subgroup.mem_center_iff]
    intro r
    apply Subtype.ext
    exact Subgroup.mem_centralizer_iff.mp (hZcentral hz) r r.property
  have hZcardNative : Nat.card ((ZAt Γ cp.firstStep).subgroupOf R) = 2 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZR).toEquiv]
    exact (eight_six_first_step_fixed_line_local ctx hcenter hcard).1
  have hcenterEq : (ZAt Γ cp.firstStep).subgroupOf R = Subgroup.center R :=
    Subgroup.eq_of_le_of_card_ge hZnative (by rw [hZcardNative,IsExtraspecial.center_order_p 2 R])
  have hcenterD : Subgroup.center R ≤ D.subgroupOf R := by
    rw [←hcenterEq]
    exact Subgroup.subgroupOf_mono R hZD
  let _ := IsElementaryAbelian.subgroupOf (p := 2) hDR
  have hupper := extraspecial_two_elementary_card_sq_le (D.subgroupOf R) hcenterD
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDR).toEquiv] at hupper
  have hRcard' : Nat.card R = 512 := hRcard
  rw [hRcard'] at hupper
  have hlower := eight_six_high_cost_intersection_card_lower ctx hcenter hquot hlength hcard
    previous D L Q hprev data E A0 actor geom hcore hedge hD hL ha hout hlarge hmin hQ hhigh helementary
  have hDcard : Nat.card D = 32 := by nlinarith
  have hYV : ⁅R,twoResidualIn E⁆ ≤ V :=
    (eight_six_selected_residual_decomposition ctx hcenter hquot hlength hcard
      previous D L Q hprev data E A0 actor geom hcore hedge hD hL).2.2.ge.trans' le_sup_left
  have hVnot : ¬ V ≤ Qa := fun h => hselected.2 (hYV.trans h)
  have hfirst : cp.firstStep ∈ Neighborhood Γ cp.a :=
    (mem_neighborhood_iff_adjacent Γ).mpr cp.firstStep_adj
  obtain ⟨g,hg⟩ := (lemma_seven_one ctx.sectionSeven Γ).local_transitivity cp.a hfirst hprev.1
  let f := (MulAut.conj (g:G)⁻¹).toMonoidHom
  have hVmap : V.map f = VAt Γ previous := by
    rw [←hg]
    exact (v_act Γ g cp.firstStep).symm
  have hRmap : R.map f = QAt Γ previous := by
    rw [←hg]
    exact (q_act Γ g cp.firstStep).symm
  have hprevRV : QAt Γ previous = VAt Γ previous := by
    rw [←hRmap,hRV,hVmap]
  have hprevCard : Nat.card (VAt Γ previous) = 512 := by
    rw [←hVmap,Subgroup.card_map_of_injective (MulAut.conj (g:G)⁻¹).injective]
    exact hVcard
  have hQamap : Qa.map f = Qa := Subgroup.mem_normalizer_iff_map_conj_eq.mp
    ((Subgroup.normalizer (Qa : Set G)).inv_mem (stabilizer_le_normalizer_q Γ cp.a g.property))
  have hprevNot : ¬ VAt Γ previous ≤ Qa := by
    intro h
    apply hVnot
    have hm : V.map f ≤ Qa.map f := by rw [hVmap,hQamap]; exact h
    have hh := Subgroup.comap_mono (f := f) hm
    have hfinj : Function.Injective f := (MulAut.conj (g:G)⁻¹).injective
    simpa only [Subgroup.comap_map_eq_self_of_injective hfinj] using hh
  have hDp : D ≤ VAt Γ previous := (hD ▸ inf_le_left).trans hprevRV.le
  have hcores := eight_six_rigidity_core_containments ctx.sectionSeven Γ cp previous D L Q hD data
  have hDA : D ≤ A := le_inf hDp (hcores.1.trans hcores.2.1)
  have hVR : VAt Γ previous ≤ QAt Γ previous := hprevRV.ge
  have hVtwo : IsPGroup 2 (VAt Γ previous) := by
    rw [←hprevRV]
    change IsPGroup 2 (Γ.twoCoreAt previous)
    rw [Γ.twoCoreAt_def]
    exact (pCore_isPGroup (p := 2)).map _
  have hback : cp.a ∈ Neighborhood Γ previous :=
    (mem_neighborhood_iff_adjacent Γ).mpr (Γ.adjacent_symm ((mem_neighborhood_iff_adjacent Γ).mp hprev.1))
  have hVGa : VAt Γ previous ≤ GAt Γ cp.a := hVR.trans
    (((lemma_seven_three ctx.sectionSeven Γ).sylow_and_core previous cp.a hback default).2.2)
  have hdiv : A.relIndex (VAt Γ previous) ∣ 2 :=
    eight_six_two_subgroup_core_part_index_dvd_two _ _ _ hVGa hVtwo hquot
  have hindex : A.relIndex (VAt Γ previous) = 2 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp hdiv with h | h
    · exact (hprevNot ((Subgroup.relIndex_eq_one.mp h).trans inf_le_right)).elim
    · exact h
  have hcount := (A.subgroupOf (VAt Γ previous)).index_mul_card
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (show A ≤ VAt Γ previous from inf_le_left)).toEquiv,
    hprevCard] at hcount
  change A.relIndex (VAt Γ previous) * Nat.card A = 512 at hcount
  rw [hindex] at hcount
  change Nat.card A = 8 * Nat.card (A ⊓ D : Subgroup G)
  rw [inf_eq_right.mpr hDA,hDcard]
  omega

end Stellmacher.SectionEight
