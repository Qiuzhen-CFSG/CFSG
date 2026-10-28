module
public import Stellmacher.SectionEight.EightSixCostFourInitialPairCard

/-!
# The cost-four core quotient and initial-pair intersection

In the original selected cost-four configuration, the prescribed core Q
has quotient of order sixteen by D. The join of the two neighboring
module/core intersections meets D in exactly the initial center Za.
All graph, core and selection data are retained.

Both neighboring intersections have order sixteen and meet in Za of order
four. Normality of D transports its intersection with one neighbor to the
other. The first intersection meets the product of the second with D only
in Za, since that product lies in the next core. The three normalized
subgroup-product cardinal formulas give |Q|=16|D| and then |(A join B)
intersect D|=4. Its known containment of Za proves equality.

This supplies the initial residual support count in Stellmacher (8.6)(b1),
printed p.44. No identification with the initial residual core or fixed-point
property of a cubic subgroup is assumed.
-/

namespace Stellmacher.SectionEight
open Later SectionsFiveToSeven CosetGraphContext SevenSix
universe u
public theorem eight_six_cost_four_core_quotient_card
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
    QuotientCardEq Q D 16 ∧
      ((VAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.a) ⊔
        (VAt ctx.Γ ctx.criticalPath.firstStep ⊓ QAt ctx.Γ ctx.criticalPath.a)) ⊓ D =
          ZAt ctx.Γ ctx.criticalPath.a := by
  classical
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let P := GAt Γ cp.a
  let Qa := QAt Γ cp.a
  let R := QAt Γ cp.firstStep
  let A := VAt Γ previous ⊓ Qa
  let B := VAt Γ cp.firstStep ⊓ Qa
  let pair := A ⊔ B
  have hlen : cp.length = 2 := hlength
  obtain ⟨hAcard,hBcard,hAD,hAB,hpair⟩ := eight_six_cost_four_initial_pair_card
    ctx hcenter hquot hlength hcard previous D L Q hprev data E A0 actor geom
    hcore hedge hD hL ha hout hlarge hmin hQ hcost
  change Nat.card A = 16 at hAcard
  change Nat.card B = 16 at hBcard
  change A ⊓ D = ZAt Γ cp.a at hAD
  change Nat.card pair = 64 at hpair
  have hDN : P ≤ Subgroup.normalizer (D : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer data.intersection_normal.1).mp
      data.intersection_normal.2
  have hcores := eight_six_rigidity_core_containments ctx.sectionSeven Γ cp previous D L Q hD data
  have hDQa : D ≤ Qa := hcores.1.trans hcores.2.1
  have hQaP : Qa ≤ P := by
    change Γ.twoCoreAt cp.a ≤ Γ.stabilizer cp.a
    rw [Γ.twoCoreAt_def]
    exact twoCoreIn_le _
  have hfirst : cp.firstStep ∈ Neighborhood Γ cp.a :=
    (mem_neighborhood_iff_adjacent Γ).mpr cp.firstStep_adj
  obtain ⟨g,hg⟩ := (lemma_seven_one ctx.sectionSeven Γ).local_transitivity cp.a hfirst hprev.1
  let f := (MulAut.conj (g:G)⁻¹).toMonoidHom
  have hf : Function.Injective f := (MulAut.conj (g:G)⁻¹).injective
  have hVmap : (VAt Γ cp.firstStep).map f = VAt Γ previous := by
    rw [←hg]
    exact (v_act Γ g cp.firstStep).symm
  have hQamap : Qa.map f = Qa := Subgroup.mem_normalizer_iff_map_conj_eq.mp
    ((Subgroup.normalizer (Qa : Set G)).inv_mem (stabilizer_le_normalizer_q Γ cp.a g.property))
  have hDmap : D.map f = D := Subgroup.mem_normalizer_iff_map_conj_eq.mp
    ((Subgroup.normalizer (D : Set G)).inv_mem (hDN g.property))
  have hZmap : (ZAt Γ cp.a).map f = ZAt Γ cp.a := Subgroup.mem_normalizer_iff_map_conj_eq.mp
    ((Subgroup.normalizer (ZAt Γ cp.a : Set G)).inv_mem
      (stabilizer_le_normalizer_z Γ cp.a g.property))
  have hBmap : B.map f = A := by
    change (VAt Γ cp.firstStep ⊓ Qa).map f = _
    rw [Subgroup.map_inf _ _ _ hf,hVmap,hQamap]
  have hBD : B ⊓ D = ZAt Γ cp.a := by
    apply Subgroup.map_injective hf
    rw [Subgroup.map_inf _ _ _ hf,hBmap,hDmap,hAD,hZmap]
  have hVR : VAt Γ cp.firstStep ≤ R :=
    neighbor_join_le_core_of_length_gt_one Γ cp (by omega) _
  have hBDR : B ⊔ D ≤ R := sup_le (inf_le_left.trans hVR) (hD.le.trans inf_le_right)
  have hABD : A ⊓ (B ⊔ D) = ZAt Γ cp.a := by
    apply le_antisymm
    · apply hAD.le.trans'
      refine le_inf inf_le_left ?_
      intro x hx
      rw [hD]
      exact ⟨(neighbor_join_le_core_of_length_gt_one Γ cp (by omega) previous) hx.1.1,
        hBDR hx.2⟩
    · exact le_inf (hAD.ge.trans inf_le_left)
        ((hAD.ge.trans inf_le_right).trans le_sup_right)
  have hBdnorm : B ≤ Subgroup.normalizer (D : Set G) :=
    inf_le_right.trans (hQaP.trans hDN)
  have hprodBD := Subgroup.card_mul_eq_card_inf_mul_card_sup_of_normalizes D B hBdnorm
  rw [inf_comm D B,hBD,hcard,hBcard] at hprodBD
  have hBDcard : Nat.card (B ⊔ D : Subgroup G) = 4 * Nat.card D := by
    rw [sup_comm D B] at hprodBD
    omega
  have hAN := (eight_six_generation_neighbor_action ctx.sectionSeven Γ cp
    (by omega) previous hprev.1).1
  have hBDnormA : B ⊔ D ≤ Subgroup.normalizer (A : Set G) :=
    (sup_le inf_le_right hDQa).trans hAN
  have hgen : Q = A ⊔ (B ⊔ D) := by
    simpa only [sup_assoc] using data.core_generation
  have hprodQ := Subgroup.card_mul_eq_card_inf_mul_card_sup_of_normalizes A (B ⊔ D) hBDnormA
  rw [hAcard,hBDcard,hABD,hcard,←hgen] at hprodQ
  have hQcard : Nat.card Q = 16 * Nat.card D := by omega
  have hpairDN : pair ≤ Subgroup.normalizer (D : Set G) :=
    (sup_le inf_le_right inf_le_right).trans (hQaP.trans hDN)
  have hprodPair := Subgroup.card_mul_eq_card_inf_mul_card_sup_of_normalizes D pair hpairDN
  have hgenPair : Q = pair ⊔ D := data.core_generation
  rw [hpair,inf_comm D pair,sup_comm D pair,←hgenPair,hQcard] at hprodPair
  have hinterCard : Nat.card (pair ⊓ D : Subgroup G) = 4 := by
    apply Nat.eq_of_mul_eq_mul_right (m := Nat.card D) Nat.card_pos
    nlinarith [hprodPair]
  have hZaPair : ZAt Γ cp.a ≤ pair ⊓ D :=
    le_inf ((hAD.ge.trans inf_le_left).trans le_sup_left) (hAD.ge.trans inf_le_right)
  refine ⟨hQcard,?_⟩
  exact (Subgroup.eq_of_le_of_card_ge hZaPair (by rw [hinterCard]; exact hcard.ge)).symm

end Stellmacher.SectionEight
