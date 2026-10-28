module
public import Stellmacher.SectionEight.EightSixHighCostActorRank

/-!
# Orders of the high-cost core quotient and intersection

For the actual selected high-cost configuration of Stellmacher (8.6), the
local core quotient Q/D has order64 and D has order32. The selected graph,
actor and elementary-intersection hypotheses are retained; no quotient
order or final case-C alternative is assumed.

The next core equals its neighbor join and has order512. Its intersection
B with the initial core has index two: the initial SL2(2) quotient bounds
the index, and the selected residual escape excludes index one. Local
transitivity carries B to the predecessor actor A, so both have order256.
The proved actor quotient |A/D|=8 gives |D|=32. Their intersection is D,
and equation-one generation gives Q=A join B. The common Frattini bound
forces their commutators into D, so they normalize each other and the
product-cardinality formula yields |Q/D|=64.

Source: Stellmacher, Journal of Algebra 190 (1997), (8.6)(c), printed pp.41
and 45, the count immediately after (18). This supplies the two numerical
core conclusions of the existing public case-C alternative.
-/

namespace Stellmacher.SectionEight
open Later SectionsFiveToSeven CosetGraphContext SevenSix
universe u
public theorem eight_six_high_cost_core_orders
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
    QuotientCardEq Q D 64 ∧ Nat.card D = 32 := by
  classical
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let V := VAt Γ cp.firstStep
  let R := QAt Γ cp.firstStep
  let Qa := QAt Γ cp.a
  let A := VAt Γ previous ⊓ Qa
  let B := V ⊓ Qa
  have hlen : cp.length = 2 := hlength
  have hselected := eight_six_selected_fixed_core_containment ctx hcenter hquot hlength
    hcard previous D L Q hprev hD hL hQ data E A0 actor geom hcore hedge ha hout hlarge hmin
  have hRV : R = V := eight_six_high_cost_next_core_eq_v ctx hcenter hquot hlength hcard
    previous D L Q hprev data E A0 actor geom hcore hedge hD hL hhigh hselected.1 helementary
  have hRcard : Nat.card R = 512 := (eight_six_high_cost_next_core_extraspecial
    ctx hcenter hquot hlength hcard previous D L Q hprev data E A0 actor geom hcore hedge
    hD hL ha hout hlarge hmin hQ hhigh helementary).2
  have hVcard : Nat.card V = 512 := hRV ▸ hRcard
  have hcores := eight_six_rigidity_core_containments ctx.sectionSeven Γ cp previous D L Q hD data
  have hDQa : D ≤ Qa := hcores.1.trans hcores.2.1
  have hDB : D ≤ B := le_inf ((hD ▸ inf_le_right).trans hRV.le) hDQa
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
  have hDA : D ≤ A := le_inf ((hD ▸ inf_le_left).trans hprevRV.le) hDQa
  have hQamap : Qa.map f = Qa := Subgroup.mem_normalizer_iff_map_conj_eq.mp
    ((Subgroup.normalizer (Qa : Set G)).inv_mem (stabilizer_le_normalizer_q Γ cp.a g.property))
  have hBmap : B.map f = A := by
    change (V ⊓ Qa).map f = A
    rw [Subgroup.map_inf V Qa f (MulAut.conj (g:G)⁻¹).injective,hVmap,hQamap]
  have hVtwo : IsPGroup 2 V := by
    rw [←hRV]
    change IsPGroup 2 (Γ.twoCoreAt cp.firstStep)
    rw [Γ.twoCoreAt_def]
    exact (pCore_isPGroup (p := 2)).map _
  have hback : cp.a ∈ Neighborhood Γ cp.firstStep :=
    (mem_neighborhood_iff_adjacent Γ).mpr (Γ.adjacent_symm cp.firstStep_adj)
  have hVGa : V ≤ GAt Γ cp.a := hRV.ge.trans
    (((lemma_seven_three ctx.sectionSeven Γ).sylow_and_core cp.firstStep cp.a hback default).2.2)
  have hdiv : B.relIndex V ∣ 2 :=
    eight_six_two_subgroup_core_part_index_dvd_two _ _ _ hVGa hVtwo hquot
  have hindex : B.relIndex V = 2 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp hdiv with h | h
    · exact (hVnot ((Subgroup.relIndex_eq_one.mp h).trans inf_le_right)).elim
    · exact h
  have hcount := (B.subgroupOf V).index_mul_card
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (show B ≤ V from inf_le_left)).toEquiv,
    hVcard] at hcount
  change B.relIndex V * Nat.card B = 512 at hcount
  rw [hindex] at hcount
  have hBcard : Nat.card B = 256 := by omega
  have hAcard : Nat.card A = 256 := by
    rw [←hBmap,Subgroup.card_map_of_injective (MulAut.conj (g:G)⁻¹).injective]
    exact hBcard
  have harank := eight_six_high_cost_actor_rank ctx hcenter hquot hlength hcard
    previous D L Q hprev data E A0 actor geom hcore hedge hD hL ha hout hlarge hmin hQ hhigh helementary
  change Nat.card A = 8 * Nat.card (A ⊓ D : Subgroup G) at harank
  rw [inf_eq_right.mpr hDA,hAcard] at harank
  have hDcard : Nat.card D = 32 := by omega
  have hAB : A ⊓ B = D := by
    apply le_antisymm
    · intro a haAB
      rw [hD]
      exact ⟨hprevRV.ge haAB.1.1,hRV.ge haAB.2.1⟩
    · exact le_inf hDA hDB
  have hQAB : Q = A ⊔ B := by
    have hh : Q = A ⊔ B ⊔ D := data.core_generation
    rwa [sup_eq_left.mpr (hDA.trans le_sup_left)] at hh
  have hAQ : A ≤ Q := hQAB ▸ le_sup_left
  have hBQ : B ≤ Q := hQAB ▸ le_sup_right
  have hQtwo : IsPGroup 2 Q := by
    rw [hQ,twoCoreIn]
    exact (pCore_isPGroup (p := 2)).map _
  let _ : Fact (IsPGroup 2 Q) := ⟨hQtwo⟩
  have hcommQ : ⁅Q,Q⁆ ≤ D := by
    have hm : (_root_.commutator Q).map Q.subtype = ⁅Q,Q⁆ := by
      rw [_root_.commutator_def,Subgroup.map_commutator]
      rw [←MonoidHom.range_eq_map,Subgroup.range_subtype]
    rw [←hm]
    exact (Subgroup.map_mono (commutator_le_frattini_of_isPGroup (p := 2))).trans data.core_frattini_le
  have hBA : B ≤ Subgroup.normalizer (A : Set G) :=
    Subgroup.le_normalizer_iff_commutator_le_left.mpr
      (((Subgroup.commutator_mono hAQ hBQ).trans hcommQ).trans hDA)
  have hprod := Subgroup.card_mul_eq_card_inf_mul_card_sup_of_normalizes A B hBA
  rw [hAcard,hBcard,hAB,hDcard,←hQAB] at hprod
  have hQcard : Nat.card Q = 2048 := by omega
  exact ⟨by change Nat.card Q = 64 * Nat.card D; rw [hQcard,hDcard],hDcard⟩
end Stellmacher.SectionEight
