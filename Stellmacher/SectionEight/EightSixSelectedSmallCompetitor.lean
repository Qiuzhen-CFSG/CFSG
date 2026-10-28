module
public import Stellmacher.SectionEight.EightSixSelectedFixedCoreIntersection
public import Stellmacher.SectionEight.EightSixSelectedOrbitCommutator
public import Stellmacher.SectionEight.EightSixNextQuotientModule
public import Stellmacher.SectionEight.GeneratedEightSixNormalizerExtraction
public import Theory.GroupAction.FixedCoatomDisplacement

/-!
# A small-cost competitor for the selected actor in (8.6)

Under the supported/fixed decomposition of the next module, the actual
selected coatom contains an actor outside the next core whose commutator
cost is at most two. The large predecessor-core index and exact geometric
selection are retained; no low-cost actor is assumed.

The selected center orbit and the residual-fixed subgroup meet the initial
core in factors centralized by the coatom modulo the next center, by
source-(11). The initial SL₂(2) quotient gives this core intersection index
dividing two. The large actor index forces the coatom to escape the next
core. Its induced automorphism therefore satisfies the proved fixed-coatom
displacement bound on the literal next-module quotient.

Source: Stellmacher (8.6), printed p.43, paragraph proving assertion (13),
`refs/files/stellmacher-n-group.pdf`. The decomposition is a conditional
input here; the transvection reduction and minimum-cost contradiction are
separate consumers.
-/

namespace Stellmacher.SectionEight
open Later SectionsFiveToSeven CosetGraphContext
open scoped commutatorElement Pointwise
universe u

public theorem eight_six_selected_small_competitor_of_split
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
    (hlarge : 4 * Nat.card
      ((VAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.a) ⊓ D : Subgroup G) ≤
      Nat.card (VAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.a : Subgroup G))
    (hsplit : VAt ctx.Γ ctx.criticalPath.firstStep =
      conjugateClosure (ZAt ctx.Γ ctx.criticalPath.a) E ⊔
        (VAt ctx.Γ ctx.criticalPath.firstStep ⊓
          Subgroup.centralizer (twoResidualIn E : Set G))) :
    ∃ other ∈ A0, other ∉ QAt ctx.Γ ctx.criticalPath.firstStep ∧
      eightSixCommutatorCost ctx.Γ ctx.criticalPath other ≤ 2 := by
  classical
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let A := VAt Γ previous ⊓ QAt Γ cp.a
  let P := GAt Γ cp.firstStep
  let R := QAt Γ cp.firstStep
  let V := VAt Γ cp.firstStep
  let Z := ZAt Γ cp.firstStep
  let U := conjugateClosure (ZAt Γ cp.a) E
  let V0 := R ⊓ Subgroup.centralizer (twoResidualIn E : Set G)
  let C := V ⊓ Subgroup.centralizer (twoResidualIn E : Set G)
  let K := V ⊓ QAt Γ cp.a
  have hA0A : A0 ≤ A := geom.coatom_eq ▸ inf_le_left
  have hAE : A ≤ E := geom.generated ▸ le_sup_left
  have hAP : A ≤ P := hAE.trans geom.group_le
  have hVR : V ≤ R := SevenSix.neighbor_join_le_core_of_length_gt_one Γ cp
    (by exact hlength ▸ by decide) _
  have hRP : R ≤ P := by
    change Γ.twoCoreAt _ ≤ Γ.vertexStabilizer _
    rw [Γ.twoCoreAt_def]
    exact Subgroup.map_subtype_le _
  have hPV := stabilizer_le_normalizer_v Γ cp.firstStep
  have hPZ := stabilizer_le_normalizer_z Γ cp.firstStep
  have hZV : Z ≤ V := (eight_six_first_step_fixed_line_local ctx hcenter hcard).2.trans
    (lemma_seven_four ctx.sectionSeven Γ cp).first_containment.1
  have hZC : Z ≤ C := le_inf hZV
    ((hcenter.trans (SevenSix.centerAmbient_le_centralizer _)).trans
      (Subgroup.centralizer_le ((SevenSix.twoResidualIn_le E).trans geom.group_le)))
  have hCV0 : C ≤ V0 := inf_le_inf_right _ hVR
  have hUV : U ≤ V := eight_six_conjugate_closure_le _ _ _
    (lemma_seven_four ctx.sectionSeven Γ cp).first_containment.1
    (geom.group_le.trans hPV)
  have hUC : U ≤ Subgroup.normalizer (C : Set G) :=
    Subgroup.le_normalizer_iff_commutator_le_right.mpr
      (((Subgroup.commutator_mono hUV (inf_le_left.trans hVR)).trans_eq
        data.first_commutator).trans hZC)
  have hU0 : ⁅U,A0⁆ ≤ Z := eight_six_selected_orbit_commutator_le ctx hcenter hcard
    E A0 geom.group_le (hA0A.trans inf_le_right) geom.coatom_commutator
  have hC0 : ⁅C ⊓ QAt Γ cp.a,A0⁆ ≤ Z :=
    (Subgroup.commutator_mono (inf_le_inf_right _ hCV0) hA0A).trans
      (eight_six_selected_fixed_core_commutator_bounds ctx hcenter hquot hlength hcard
        previous D L Q hprev hD hL data E A0 actor geom hedge).1
  have hK0 : ⁅K,A0⁆ ≤ Z := by
    apply Subgroup.commutator_le.mpr
    intro point hpoint mover hmover
    have hproduct : point ∈ (U : Set G) * (C : Set G) := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right _ _ hUC]
      exact hsplit ▸ hpoint.1
    obtain ⟨u,hu,c,hc,rfl⟩ := hproduct
    have hcQa : c ∈ QAt Γ cp.a := by
      have hh := (QAt Γ cp.a).mul_mem ((QAt Γ cp.a).inv_mem (hcore hu)) hpoint.2
      simpa only [inv_mul_cancel_left] using hh
    rw [commutatorElement_mul_left_eq_conj_mul]
    exact Z.mul_mem
      ((Subgroup.mem_normalizer_iff.mp (hPZ (hRP (hVR (hUV hu)))) _).mp
        (hC0 (Subgroup.commutator_mem_commutator ⟨hc,hcQa⟩ hmover)))
      (hU0 (Subgroup.commutator_mem_commutator hu hmover))
  have hVp : IsPGroup 2 V := by
    have hRp : IsPGroup 2 R := by
      change IsPGroup 2 (Γ.twoCoreAt _)
      rw [Γ.twoCoreAt_def]
      exact (pCore_isPGroup (p := 2)).map _
    exact hRp.to_le hVR
  have hVinitial : V ≤ GAt Γ cp.a := hVR.trans
    (((lemma_seven_three ctx.sectionSeven Γ).sylow_and_core cp.firstStep cp.a
      ((SevenSix.mem_neighborhood_iff_adjacent Γ).mpr (Γ.adjacent_symm cp.firstStep_adj))
      default).2.2)
  have hKindex : K.relIndex V ∣ 2 :=
    eight_six_two_subgroup_core_part_index_dvd_two _ _ V hVinitial hVp hquot
  have hAprevious : A ≤ QAt Γ previous := inf_le_left.trans
    (SevenSix.neighbor_join_le_core_of_length_gt_one Γ cp
      (by exact hlength ▸ by decide) previous)
  have hA0not : ¬ A0 ≤ R := by
    intro hA0R
    have hA0D : A0 ≤ A ⊓ D := le_inf hA0A (hD ▸ le_inf (hA0A.trans hAprevious) hA0R)
    have hbound := Subgroup.card_le_of_le hA0D
    have hcount : Nat.card A = 2 * Nat.card A0 := geom.coatom_card
    have hpos : 0 < Nat.card A0 := Nat.card_pos
    change 4 * Nat.card (A ⊓ D : Subgroup G) ≤ Nat.card A at hlarge
    omega
  obtain ⟨other, hother, hout⟩ := SetLike.not_le_iff_exists.mp hA0not
  obtain ⟨hN,hW,action,haction,_hkernel,_hgenerate⟩ :=
    eight_six_next_quotient_module_data_local ctx hcenter hlength hcard data.first_commutator
  let _ := hN
  have hbound := Subgroup.quotient_commutator_card_le_two_of_fixed_coatom P V Z K
    hZV hPV hN hW action haction ⟨other,hAP (hA0A hother)⟩ inf_le_left hKindex
    ((Subgroup.commutator_mono le_rfl (Subgroup.zpowers_le.mpr hother)).trans hK0)
  exact ⟨other,hother,hout,hbound⟩


end Stellmacher.SectionEight

