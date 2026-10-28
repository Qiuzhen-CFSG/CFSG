module
public import Stellmacher.SectionEight.EightSixSelectedActorCostCases
public import Stellmacher.SectionEight.EightSixResidualFixedQuotient
public import Stellmacher.SectionThree.CentralCoatomInvolutionCard
/-!
The cost-four branch of Stellmacher (8.6) has |Vnext/C|=16, where C is
the actual residual-fixed subgroup Vnext intersect C_G(O²(E)). The theorem
retains the selected local geometry, minimizing actor, equation-one data,
large actor index, actual definition of Q, and cost-four branch premise.

Use the literal conjugation action on the elementary quotient Vnext/C.
The selected coatom has central image, two conjugate actor subgroups
generate E, and the residual image has no fixed vectors. The actor's square
lies in the Frattini subgroup of Q and hence in D, which acts trivially on
this quotient. The raw displacement order is even, greater than two by
source (13), and at most the original cost four. Thus it is four. The exact
square-cardinality theorem for two conjugate involutions gives order sixteen.
No unproved action model for E on the selected orbit is used.

Source: Stellmacher, Journal of Algebra 190 (1997), proof of (8.6), printed
p.44, the cost-four paragraph after assertion (14).
-/

namespace Stellmacher.SectionEight
open Later SectionsFiveToSeven CosetGraphContext SevenSix
open scoped commutatorElement IsMulCommutative
universe u
public theorem eight_six_cost_four_fixed_quotient_card
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
    (hcost : eightSixCommutatorCost ctx.Γ ctx.criticalPath actor = 4) :
    QuotientCardEq (VAt ctx.Γ ctx.criticalPath.firstStep)
      (VAt ctx.Γ ctx.criticalPath.firstStep ⊓
        Subgroup.centralizer (twoResidualIn E : Set G)) 16 := by
  classical
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let V := VAt Γ cp.firstStep
  let C := V ⊓ Subgroup.centralizer (twoResidualIn E : Set G)
  let A := VAt Γ previous ⊓ QAt Γ cp.a
  have hAE : A ≤ E := geom.generated ▸ le_sup_left
  have hA0A : A0 ≤ A := geom.coatom_eq ▸ inf_le_left
  have hA0E : A0 ≤ E := hA0A.trans hAE
  have hxE : geom.x ∈ E := twoResidualIn_le E geom.residual_mem
  let a : E := ⟨actor,hAE ha⟩
  let x : E := ⟨geom.x,hxE⟩
  let Ai := A.subgroupOf E
  let A0i := A0.subgroupOf E
  have ha0 : actor ∉ A0 := by
    intro hh
    apply geom.actor_outside
    exact (geom.coatom_eq ▸ hh).2
  have hindex : A0.relIndex A = 2 := by
    have hh := (A0.subgroupOf A).index_mul_card
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hA0A).toEquiv] at hh
    change A0.relIndex A * Nat.card A0 = Nat.card A at hh
    have hcount : Nat.card A = 2 * Nat.card A0 := geom.coatom_card
    have hp : 0 < Nat.card A0 := Nat.card_pos
    nlinarith
  have hAsp : A = Subgroup.zpowers actor ⊔ A0 := by
    apply le_antisymm ?_ (sup_le (Subgroup.zpowers_le.mpr ha) hA0A)
    intro g hg
    by_cases hg0 : g ∈ A0
    · exact Subgroup.mem_sup_right hg0
    have hk : actor⁻¹ * g ∈ A0 := by
      have hh := (A0.subgroupOf A).mul_mem_iff_of_index_two hindex
        (a := ⟨actor⁻¹,A.inv_mem ha⟩) (b := ⟨g,hg⟩)
      exact hh.mpr (by simp only [Subgroup.mem_subgroupOf,Subgroup.inv_mem_iff,ha0,hg0])
    have hm := (Subgroup.zpowers actor ⊔ A0).mul_mem
      (Subgroup.mem_sup_left (Subgroup.mem_zpowers actor)) (Subgroup.mem_sup_right hk)
    simpa only [mul_inv_cancel_left] using hm
  have hAi : Ai = Subgroup.zpowers a ⊔ A0i := by
    apply Subgroup.map_injective E.subtype_injective
    rw [Subgroup.map_sup,MonoidHom.map_zpowers,
      Subgroup.map_subgroupOf_eq_of_le hA0E,Subgroup.map_subgroupOf_eq_of_le hAE]
    exact hAsp
  have hconj : (Ai.conjBy x).map E.subtype = A.conjBy geom.x := by
    calc
      (Ai.conjBy x).map E.subtype = (Ai.map E.subtype).conjBy geom.x := by
        simp only [Subgroup.conjBy,Subgroup.map_map]
        rfl
      _ = A.conjBy geom.x := by rw [Subgroup.map_subgroupOf_eq_of_le hAE]
  have hgen : (⊤ : Subgroup E) = Ai ⊔ Ai.conjBy x := by
    apply Subgroup.map_injective E.subtype_injective
    rw [Subgroup.map_sup,hconj,Subgroup.map_subgroupOf_eq_of_le hAE,
      ←MonoidHom.range_eq_map,Subgroup.range_subtype]
    exact geom.generated
  have hA0two : IsPGroup 2 A0i := by
    have hQtwo : IsPGroup 2 (QAt Γ cp.a) := by
      change IsPGroup 2 (Γ.twoCoreAt cp.a)
      rw [Γ.twoCoreAt_def]
      exact (pCore_isPGroup (p := 2)).map _
    exact (hQtwo.to_le (hA0A.trans inf_le_right)).of_equiv
      (Subgroup.subgroupOfEquivOfLe hA0E).symm
  obtain ⟨hN,hW,action,haction,hkernel,hfixed⟩ := eight_six_residual_fixed_quotient_module
    ctx hcenter hlength hcard data.first_commutator E geom.group_le
  let _ := hN
  let _ := hW
  have hEV : E ≤ Subgroup.normalizer (V : Set G) :=
    geom.group_le.trans (stabilizer_le_normalizer_v Γ cp.firstStep)
  have hcentral : A0i.map action ≤ Subgroup.centralizer (action.range : Set _) := by
    rintro mover ⟨b,hb,rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro image ⟨e,rfl⟩
    have hk : ⁅e,b⁆ ∈ action.ker := hkernel
      (geom.coatom_commutator (Subgroup.commutator_mem_commutator e.property hb))
    have hone : ⁅action e,action b⁆ = 1 := by
      rw [←map_commutatorElement]
      exact MonoidHom.mem_ker.mp hk
    exact commutatorElement_eq_one_iff_mul_comm.mp hone
  have hcyclic : (Subgroup.zpowers actor).subgroupOf E = Subgroup.zpowers a := by
    apply Subgroup.map_injective E.subtype_injective
    rw [Subgroup.map_subgroupOf_eq_of_le (Subgroup.zpowers_le.mpr (hAE ha)),
      MonoidHom.map_zpowers]
    rfl
  have hAV : ⁅V,Subgroup.zpowers actor⁆ ≤ V :=
    Subgroup.le_normalizer_iff_commutator_le_left.mp
      ((Subgroup.zpowers_le.mpr (hAE ha)).trans hEV)
  have hrel := Subgroup.relIndex_sup_right
    ((⁅V,Subgroup.zpowers actor⁆).subgroupOf V) (C.subgroupOf V)
  rw [←Subgroup.subgroupOf_sup hAV inf_le_left,
    Subgroup.relIndex_subgroupOf (sup_le hAV inf_le_left),
    Subgroup.relIndex_subgroupOf hAV] at hrel
  have hrank : Nat.card (commutatorAction (Subgroup.zpowers (action a))
      (V ⧸ C.subgroupOf V)) = C.relIndex (⁅V,Subgroup.zpowers actor⁆ ⊔ C) := by
    have hh := Subgroup.quotient_conjugation_commutatorAction_card E V C
      (Subgroup.zpowers actor) hEV (Subgroup.zpowers_le.mpr (hAE ha)) hN action haction
    rw [hcyclic,MonoidHom.map_zpowers] at hh
    exact hh.trans hrel.symm
  have hlower := eight_six_selected_actor_not_transvection ctx hcenter hquot hlength hcard
    previous D L Q hprev data E A0 actor geom hcore hedge hD hL ha hout hlarge hmin
  have hupper := eight_six_residual_fixed_cost_le_actor_cost ctx hcenter hlength hcard
    data.first_commutator E geom.group_le actor (geom.group_le (hAE ha))
  rw [hcost] at hupper
  change 2 < C.relIndex (⁅V,Subgroup.zpowers actor⁆ ⊔ C) at hlower
  change C.relIndex (⁅V,Subgroup.zpowers actor⁆ ⊔ C) ≤ 4 at hupper
  have hfour : Nat.card (commutatorAction (Subgroup.zpowers (action a))
      (V ⧸ C.subgroupOf V)) = 4 := by
    have htwo := (IsElementaryAbelian.isPGroup 2 (V ⧸ C.subgroupOf V)).to_subgroup
      (commutatorAction (Subgroup.zpowers (action a)) (V ⧸ C.subgroupOf V))
    have hdvd := htwo.card_eq_or_dvd
    rw [hrank] at hdvd ⊢
    rcases hdvd with hone | hdiv
    · omega
    · obtain ⟨n,hn⟩ := hdiv
      omega
  have hAQ : A ≤ Q := data.core_generation ▸ le_sup_of_le_left le_sup_left
  have hQtwo : IsPGroup 2 Q := by
    rw [hQ,twoCoreIn]
    exact (pCore_isPGroup (p := 2)).map _
  let _ : Fact (IsPGroup 2 Q) := ⟨hQtwo⟩
  have hsquareD : actor^2 ∈ D := data.core_frattini_le
    (Subgroup.mem_map.mpr ⟨(⟨actor,hAQ ha⟩:Q)^2,
      pth_power_mem_frattini_of_isPGroup (p := 2) (⟨actor,hAQ ha⟩:Q),rfl⟩)
  have hsquare : (action a)^2 = 1 := by
    rw [←map_pow]
    apply MonoidHom.mem_ker.mp
    apply hkernel
    exact (hD ▸ hsquareD).2
  have hbound := SectionThree.central_coatom_involution_module_card_eq_square
    action Ai A0i a x hgen hAi hA0two hcentral hfixed hsquare
  rw [hfour] at hbound
  have hcount := (C.subgroupOf V).index_mul_card
  rw [Subgroup.index_eq_card, hbound,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (show C ≤ V from inf_le_left)).toEquiv] at hcount
  exact hcount.symm

end Stellmacher.SectionEight
