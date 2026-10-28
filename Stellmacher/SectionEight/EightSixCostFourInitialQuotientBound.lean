module
public import Stellmacher.SectionEight.EightSixCostFourSylowOrders
public import Stellmacher.SectionEight.EightSixCostFourInitialResidualCore

/-!
# The cost-four initial core has residual-core index at most four

In the full selected cost-four configuration of (8.6), the prescribed Q has
order at most four times the order of the actual initial residual two-core.
This is the remaining index bound in (b1), with the same local context,
geometric data, actor and actual graph subgroups as the other cost-four
conclusions.

The prescribed edge Sylow maps onto a genuine Sylow of the proved next
wreath quotient. Its image has order eight and its kernel is exactly Qnext.
The proved Sylow upper bound therefore gives |Qnext|≤128. The source product
Qnext=Vnext·D has intersection Vnext∩D=Za of order four, and Vnext has order
thirty-two, so |D|≤16. The initial product count gives |Q|=16|D|≤256.
Finally, the actual initial residual two-core equals the proved pair of order
sixty-four, giving the required bound. No unrelated quotient or substitute
Sylow subgroup is introduced.

Source: Stellmacher, Journal of Algebra 190 (1997), proof of (8.6)(b1),
printed p.44, using the source (1) generation formula and the cost-four
Sylow bound.
-/

namespace Stellmacher.SectionEight
open Later SectionsFiveToSeven CosetGraphContext SevenSix
open scoped commutatorElement
universe u
public theorem eight_six_cost_four_initial_quotient_bound
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
    QuotientOrderLe Q (twoCoreIn (EAt ctx.Γ ctx.criticalPath.a)) 4 := by
  classical
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let P := GAt Γ cp.firstStep
  let R := QAt Γ cp.firstStep
  let V := VAt Γ cp.firstStep
  let Za := ZAt Γ cp.a
  let pair := (VAt Γ previous ⊓ QAt Γ cp.a) ⊔ (V ⊓ QAt Γ cp.a)
  have hupper := (eight_six_cost_four_sylow_card_bounds ctx hcenter hquot hlength hcard
    previous D L Q hprev data E A0 actor geom hcore hedge hD hL ha hout hlarge hmin hQ hcost).2
  obtain ⟨f,hfsurj,hfker⟩ := eight_six_cost_four_next_quotient ctx hcenter hquot hlength hcard
    previous D L Q hprev data E A0 actor geom hcore hedge hD hL ha hout hlarge hmin hQ hcost
  obtain ⟨hSP,sylow,hsylow⟩ := (edge_sylow_data ctx.sectionSeven Γ cp).2
  have hSnative : (sylow : Subgroup P) = S.subgroupOf P := by
    apply Subgroup.map_injective P.subtype_injective
    rw [hsylow,Subgroup.map_subgroupOf_eq_of_le hSP]
  let T := sylow.mapSurjective hfsurj
  have hTmap : (T : Subgroup SL2TwoWreathC2) = (S.subgroupOf P).map f := by
    change (sylow : Subgroup P).map f = _
    rw [hSnative]
  have hTcard : Nat.card T = 8 := by
    obtain ⟨e⟩ := wreath_two_sylow_mulEquiv_dihedral_four T
    rw [Nat.card_congr e.toEquiv,DihedralGroup.nat_card]
  let restricted : S →* SL2TwoWreathC2 := f.comp (Subgroup.inclusion hSP)
  have hker : restricted.ker = R.subgroupOf S := by
    ext s
    change f (Subgroup.inclusion hSP s) = 1 ↔ (s:G) ∈ R
    rw [← MonoidHom.mem_ker,hfker]
    rfl
  have hrange : Nat.card restricted.range = 8 := by
    change Nat.card (f.comp (Subgroup.inclusion hSP)).range = 8
    rw [MonoidHom.range_comp,Subgroup.inclusion_range,←hTmap]
    exact hTcard
  have hScard : Nat.card S = Nat.card R * 8 := by
    have hh := restricted.ker.card_mul_index
    rw [Subgroup.index_ker,hker,hrange] at hh
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (local_cores_le_edge_sylow ctx.sectionSeven Γ cp).2).toEquiv] at hh
    exact hh.symm
  have hRupper : Nat.card R ≤ 128 := by
    rw [hScard] at hupper
    norm_num only [Nat.reducePow] at hupper
    omega
  have hVR : V ≤ R := neighbor_join_le_core_of_length_gt_one Γ cp
    (by change 1 < ctx.criticalPath.length; omega) _
  have hRP : R ≤ P := by
    change Γ.twoCoreAt _ ≤ _
    rw [Γ.twoCoreAt_def]
    exact Subgroup.map_subtype_le _
  obtain ⟨hNV,hWV,vaction,hvformula,hvkernel,hvgenerate⟩ :=
    eight_six_next_quotient_module_data_local ctx hcenter hlength hcard data.first_commutator
  have hVY : V = ⁅R,twoResidualIn E⁆ := (eight_six_cost_four_full_module_card
    ctx hcenter hquot hlength hcard previous D L Q hprev data E A0 actor geom hcore hedge
      hD hL ha hout hlarge hmin hQ hcost hNV hWV vaction hvformula hvkernel hvgenerate).2
  have hVcard : Nat.card V = 32 := by
    rw [hVY]
    exact (eight_six_cost_four_residual_card ctx hcenter hquot hlength hcard previous
      D L Q hprev data E A0 actor geom hcore hedge hD hL ha hout hlarge hmin hQ hcost).1
  have hcount := eight_six_cost_four_core_quotient_card ctx hcenter hquot hlength hcard
    previous D L Q hprev data E A0 actor geom hcore hedge hD hL ha hout hlarge hmin hQ hcost
  have hpairD : pair ⊓ D = Za := hcount.2
  have hcores := eight_six_rigidity_core_containments ctx.sectionSeven Γ cp previous D L Q hD data
  have hDQa : D ≤ QAt Γ cp.a := hcores.1.trans hcores.2.1
  have hVD : V ⊓ D = Za := by
    apply le_antisymm
    · exact (le_inf ((le_inf inf_le_left (inf_le_right.trans hDQa)).trans le_sup_right)
        inf_le_right).trans hpairD.le
    · exact le_inf (lemma_seven_four ctx.sectionSeven Γ cp).first_containment.1
        (hpairD.ge.trans inf_le_right)
  have hgen : R = V ⊔ D := eight_six_next_core_eq_v_sup_intersection ctx hlength
    previous D L Q hprev.1 hD hL data
  have hnorm : D ≤ Subgroup.normalizer (V : Set G) :=
    (hD.le.trans inf_le_right).trans (hRP.trans (stabilizer_le_normalizer_v Γ cp.firstStep))
  have hproduct := Subgroup.card_mul_eq_card_inf_mul_card_sup_of_normalizes V D hnorm
  rw [hVcard,hVD,hcard,←hgen] at hproduct
  have hDupper : Nat.card D ≤ 16 := by omega
  have hQupper : Nat.card Q ≤ 256 := by rw [hcount.1]; omega
  have hcoreCard : Nat.card (twoCoreIn (EAt Γ cp.a)) = 64 := by
    rw [←eight_six_cost_four_initial_pair_eq_residual_core ctx hcenter hquot hlength hcard
      previous D L Q hprev data E A0 actor geom hcore hedge hD hL ha hout hlarge hmin hQ hcost]
    exact (eight_six_cost_four_initial_pair_card ctx hcenter hquot hlength hcard
      previous D L Q hprev data E A0 actor geom hcore hedge hD hL ha hout hlarge hmin hQ hcost).2.2.2.2
  change Nat.card Q ≤ 4 * Nat.card (twoCoreIn (EAt Γ cp.a))
  rw [hcoreCard]
  exact hQupper
end Stellmacher.SectionEight
