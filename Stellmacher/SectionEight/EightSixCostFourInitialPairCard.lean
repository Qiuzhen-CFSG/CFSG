module
public import Stellmacher.SectionEight.EightSixCostFourFullModuleCard
public import Stellmacher.SectionEight.GeneratedEightSixSmallIndexInitialCoreTransport
public import Stellmacher.SectionEight.GeneratedEightSixCoreGenerationTools

/-!
# The actual cost-four initial pair has order sixty-four

For the selected cost-four graph configuration, both neighboring V/core
intersections A and Atilde have order sixteen. Their intersection, and
A intersected with the prescribed D, equal the initial center Za of order
four. Their product therefore has order sixty-four. The exact local graph,
selection and cost hypotheses are retained; no initial residual-core
identification or special-group structure is assumed.

The full next quotient has order sixteen and its central denominator has
order two, giving |Vnext|=32. It escapes Qa, and its image under the actual
initial S3 quotient has order two, so |Atilde|=16. Local transitivity transports
this order to A. The proved actor index four gives |A intersect D|=4;
containment of Za identifies that intersection. The two neighbor intersections
meet inside D, so they also meet in Za. Their normalization and the subgroup
product formula then give order64.

Source: Stellmacher, Journal of Algebra190 (1997), proof of (8.6)(b1),
printed p.44. Normality of the product in Ga is supplied independently by
`EightSixInitialPairNormality` without any cost-branch assumption.
-/

namespace Stellmacher.SectionEight
open Later SectionsFiveToSeven CosetGraphContext SevenSix
universe u
public theorem eight_six_cost_four_initial_pair_card
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
    let A := VAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.a
    let B := VAt ctx.Γ ctx.criticalPath.firstStep ⊓ QAt ctx.Γ ctx.criticalPath.a
    Nat.card A = 16 ∧ Nat.card B = 16 ∧ A ⊓ D = ZAt ctx.Γ ctx.criticalPath.a ∧
      A ⊓ B = ZAt ctx.Γ ctx.criticalPath.a ∧ Nat.card (A ⊔ B : Subgroup G) = 64 := by
  classical
  dsimp only
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let P := GAt Γ cp.a
  let R := QAt Γ cp.firstStep
  let V := VAt Γ cp.firstStep
  let Z := ZAt Γ cp.firstStep
  let Za := ZAt Γ cp.a
  let A := VAt Γ previous ⊓ QAt Γ cp.a
  let B := V ⊓ QAt Γ cp.a
  have hlen : cp.length = 2 := hlength
  have hVR : V ≤ R := neighbor_join_le_core_of_length_gt_one Γ cp (by omega) _
  have hVS : V ≤ S := (le_sup_left.trans data.sylow_intersection.symm.le).trans inf_le_right
  have hVP : V ≤ P := hVS.trans (edge_sylow_data ctx.sectionSeven Γ cp).1.1
  have hVtwo : IsPGroup 2 V := by
    have hRtwo : IsPGroup 2 R := by
      change IsPGroup 2 (Γ.twoCoreAt cp.firstStep)
      rw [Γ.twoCoreAt_def]
      exact pCore_isPGroup.map _
    exact hRtwo.to_le hVR
  obtain ⟨hN,hW,action,hformula,hkernel,hgenerate⟩ :=
    eight_six_next_quotient_module_data_local ctx hcenter hlength hcard data.first_commutator
  obtain ⟨hWcard,hVY⟩ := eight_six_cost_four_full_module_card ctx hcenter hquot hlength hcard
    previous D L Q hprev data E A0 actor geom hcore hedge hD hL ha hout hlarge hmin hQ hcost
    hN hW action hformula hkernel hgenerate
  have hZV : Z ≤ V := (eight_six_first_step_fixed_line_local ctx hcenter hcard).2.trans
    (lemma_seven_four ctx.sectionSeven Γ cp).first_containment.1
  have hVcard : Nat.card V = 32 := by
    have hh := Subgroup.card_eq_card_quotient_mul_card_subgroup (Z.subgroupOf V)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZV).toEquiv,
      (eight_six_first_step_fixed_line_local ctx hcenter hcard).1,hWcard] at hh
    exact hh
  have hselected := eight_six_selected_fixed_core_containment ctx hcenter hquot hlength
    hcard previous D L Q hprev hD hL hQ data E A0 actor geom hcore hedge ha hout hlarge hmin
  have hnot : ¬ V ≤ QAt Γ cp.a := by
    change ¬ VAt ctx.Γ ctx.criticalPath.firstStep ≤ QAt ctx.Γ ctx.criticalPath.a
    rw [hVY]
    exact hselected.2
  have hidxdvd : B.relIndex V ∣ 2 :=
    eight_six_two_subgroup_core_part_index_dvd_two P (QAt Γ cp.a) V hVP hVtwo hquot
  have hidx : B.relIndex V = 2 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp hidxdvd with h | h
    · have heq : B.subgroupOf V = ⊤ := Subgroup.index_eq_one.mp h
      have hVB : V ≤ B := by
        intro v hv
        exact heq.ge (Subgroup.mem_top (⟨v,hv⟩:V))
      exact False.elim (hnot (hVB.trans inf_le_right))
    · exact h
  have hBcard : Nat.card B = 16 := by
    have hh := (B.subgroupOf V).card_mul_index
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (show B≤V from inf_le_left)).toEquiv] at hh
    change Nat.card B * B.relIndex V = Nat.card V at hh
    rw [hidx,hVcard] at hh
    omega
  obtain ⟨transport⟩ := eight_six_neighbor_core_intersection_equiv ctx.sectionSeven Γ cp previous hprev.1
  have hAcard : Nat.card A = 16 := (Nat.card_congr transport.toEquiv).trans hBcard
  have hAindex := (eight_six_cost_four_actor_indices ctx hcenter hquot hlength hcard previous
    D L Q hprev data E A0 actor geom hcore hedge hD hL ha hout hlarge hmin hQ hcost).1
  change Nat.card A = 4 * Nat.card (A ⊓ D : Subgroup G) at hAindex
  have hADcard : Nat.card (A ⊓ D : Subgroup G) = 4 := by omega
  have hZaD : Za ≤ D := eight_six_initial_center_le_intersection_of_length_two Γ cp hlength
    previous hprev.1 D hD
  have hZaPrevious : Za ≤ VAt Γ previous := by
    change z Γ cp.a ≤ v Γ previous
    rw [v,Γ.vAt_def]
    exact le_sSup ⟨cp.a,(mem_neighborhood_iff_adjacent Γ).mpr
      (Γ.adjacent_symm ((mem_neighborhood_iff_adjacent Γ).mp hprev.1)),rfl⟩
  have hZaCore : Za ≤ QAt Γ cp.a :=
    (lemma_seven_three ctx.sectionSeven Γ).center_core cp.a cp.firstStep
      ((mem_neighborhood_iff_adjacent Γ).mpr cp.firstStep_adj) |>.trans
      (Subgroup.map_subtype_le _)
  have hZaA : Za ≤ A := le_inf hZaPrevious hZaCore
  have hZaB : Za ≤ B := le_inf (lemma_seven_four ctx.sectionSeven Γ cp).first_containment.1 hZaCore
  have hAD : A ⊓ D = Za :=
    (Subgroup.eq_of_le_of_card_ge (le_inf hZaA hZaD) (by rw [hADcard]; exact hcard.ge)).symm
  have hAB : A ⊓ B = Za := by
    apply le_antisymm
    · apply le_trans (le_inf inf_le_left ?_) hAD.le
      rw [hD]
      exact le_inf
        ((inf_le_left.trans inf_le_left).trans
          (neighbor_join_le_core_of_length_gt_one Γ cp (by omega) previous))
        ((inf_le_right.trans inf_le_left).trans hVR)
    · exact le_inf hZaA hZaB
  have hpreviousAction := eight_six_generation_neighbor_action ctx.sectionSeven Γ cp
    (by omega) previous hprev.1
  have hprod := Subgroup.card_mul_eq_card_inf_mul_card_sup_of_normalizes A B
    (inf_le_right.trans hpreviousAction.1)
  rw [hAcard,hBcard,hAB,hcard] at hprod
  have hpaircard : Nat.card (A ⊔ B : Subgroup G) = 64 := by omega
  exact ⟨hAcard,hBcard,hAD,hAB,hpaircard⟩
end Stellmacher.SectionEight
