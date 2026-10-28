module
public import Stellmacher.SectionEight.EightSixCostFourFullModuleCard
public import Stellmacher.SectionEight.EightSixNextQuotientModule
public import Stellmacher.SectionEight.EightSixSelectedResidualDecomposition
public import Stellmacher.SectionEight.GeneratedEightSixRigidityLastCenter
public import Stellmacher.SectionEight.GeneratedEightSixSmallIndexCenter
public import Stellmacher.ResidualCommutatorIdempotence

/-!
# The center of the next module in the cost-four branch

Under the selected length-two configuration of (8.6), with initial center
of order four and the minimal actor of commutator cost four, the center of
the actual next module V is exactly the next central line Z. The theorem
uses the existing local context and selected geometric data and constructs
the literal quotient action internally.

Write C for the center of V. The next stabilizer normalizes C, and C lies
in the initial core because it centralizes the initial center. The
intersection rigidity theorem bounds [C,A] by Z; conjugation and the two
generators of the selected group E then give [C,E] ≤ Z. Residual
commutator idempotence forces C to centralize O²(E). The cost-four module
saturation theorem gives V=[Qnext,O²(E)], and the selected residual
decomposition reduces its fixed part to Z. This proves C≤Z; the reverse
inclusion is the given local centrality.

This is the center calculation for the quaternion-product module in
Stellmacher, Journal of Algebra 190 (1997), proof of (8.6)(b2), printed
p.44. The proof requires no identification of the next core with V.
-/

namespace Stellmacher.SectionEight
open Later SectionsFiveToSeven CosetGraphContext
open scoped commutatorElement
universe u

public theorem eight_six_cost_four_module_center
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
    (hcost : eightSixCommutatorCost ctx.Γ ctx.criticalPath actor = 4)
    : CenterAmbient (VAt ctx.Γ ctx.criticalPath.firstStep) =
      ZAt ctx.Γ ctx.criticalPath.firstStep := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let R := QAt Γ cp.firstStep
  let V := VAt Γ cp.firstStep
  let Z := ZAt Γ cp.firstStep
  let P := GAt Γ cp.firstStep
  let A := VAt Γ previous ⊓ QAt Γ cp.a
  let C := CenterAmbient V
  have hRP : R ≤ P := by
    change Γ.twoCoreAt _ ≤ _
    rw [Γ.twoCoreAt_def]
    exact Subgroup.map_subtype_le _
  have hVR : V ≤ R := SevenSix.neighbor_join_le_core_of_length_gt_one Γ cp
    (by exact hlength ▸ by decide) _
  have hCcontained : C ≤ V := Subgroup.map_subtype_le _
  have hCR : C ≤ R := hCcontained.trans hVR
  have hCV : C ≤ Subgroup.centralizer (V : Set G) := SevenSix.centerAmbient_le_centralizer V
  have hPV : P ≤ Subgroup.normalizer (V : Set G) := stabilizer_le_normalizer_v Γ _
  have hPZ : P ≤ Subgroup.normalizer (Z : Set G) := stabilizer_le_normalizer_z Γ _
  have hPC : P ≤ Subgroup.normalizer (C : Set G) := by
    have hcentN : Subgroup.normalizer (V : Set G) ≤
        Subgroup.normalizer (Subgroup.centralizer (V : Set G) : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer
        (Subgroup.centralizer_le_normalizer (V : Set G))).mp inferInstance
    change P ≤ Subgroup.normalizer (CenterAmbient V : Set G)
    rw [eight_six_centerAmbient_eq_inf_centralizer]
    exact (le_inf hPV (hPV.trans hcentN)).trans Subgroup.inf_normalizer_le_normalizer_inf
  have hCQa : C ≤ QAt Γ cp.a := by
    have hCS : C ≤ S := hCR.trans (SevenSix.local_cores_le_edge_sylow ctx.sectionSeven Γ cp).2
    have hCZa : C ≤ Subgroup.centralizer (ZAt Γ cp.a : Set G) :=
      hCV.trans (Subgroup.centralizer_le
        (lemma_seven_four ctx.sectionSeven Γ cp).first_containment.1)
    exact (le_inf hCS hCZa).trans_eq (lemma_seven_four ctx.sectionSeven Γ cp).edge_centralizer
  have hAE : A ≤ E := geom.generated ▸ le_sup_left
  have hAP : A ≤ P := hAE.trans geom.group_le
  have hAprevious : A ≤ QAt Γ previous := inf_le_left.trans
    (SevenSix.neighbor_join_le_core_of_length_gt_one Γ cp (by exact hlength ▸ by decide) previous)
  have hCNprevious : C ≤ Subgroup.normalizer (QAt Γ previous : Set G) :=
    (hCQa.trans ((lemma_seven_three ctx.sectionSeven Γ).sylow_and_core cp.a previous
      hprev.1 default).2.2).trans (SevenSix.stabilizer_le_normalizer_q Γ previous)
  have hCAPrevious : ⁅C,A⁆ ≤ QAt Γ previous :=
    (Subgroup.commutator_mono le_rfl hAprevious).trans
      (Subgroup.le_normalizer_iff_commutator_le_right.mp hCNprevious)
  have hCAC : ⁅C,A⁆ ≤ C := Subgroup.le_normalizer_iff_commutator_le_left.mp
    (hAP.trans hPC)
  have hCAD : ⁅C,A⁆ ≤ D := hD ▸ le_inf hCAPrevious (hCAC.trans hCR)
  have hfull := eight_six_intersection_centralizer_of_rigidity
    ctx.sectionSeven Γ cp hcenter previous D L Q hD data (by
      intro K hK hKS
      have hKZa := eight_six_rigidity_le_initial_center ctx.sectionSeven Γ cp hcenter hquot
        previous D L Q hD hL data K (hK.trans inf_le_left) hKS
      exact eight_six_rigidity_le_first_center_of_le_initial ctx hcenter hlength hcard
        previous D L Q data K hKZa (hK.trans inf_le_right))
  have hCA : ⁅C,A⁆ ≤ Z := (le_inf hCAD (hCAC.trans hCV)).trans_eq hfull
  have hxP : geom.x ∈ P := geom.group_le (SevenSix.twoResidualIn_le E geom.residual_mem)
  let f := (MulAut.conj geom.x).toMonoidHom
  have hCmap : C.map f = C := Subgroup.mem_normalizer_iff_map_conj_eq.mp (hPC hxP)
  have hZmap : Z.map f = Z := Subgroup.mem_normalizer_iff_map_conj_eq.mp (hPZ hxP)
  have hCAx : ⁅C,A.conjBy geom.x⁆ ≤ Z := by
    change ⁅C,A.map f⁆ ≤ Z
    rw [← hCmap,←Subgroup.map_commutator]
    exact (Subgroup.map_mono hCA).trans_eq hZmap
  have hCE : ⁅C,E⁆ ≤ Z := by
    rw [Subgroup.commutator_comm,geom.generated]
    have hh := eight_six_commutator_sSup_le ({A,A.conjBy geom.x} : Set (Subgroup G)) C Z P hPZ
      (by
        intro F hF
        simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hF
        rcases hF with rfl | rfl
        · exact hAP
        · exact (le_sup_right.trans_eq geom.generated.symm).trans geom.group_le)
      (by
        intro F hF
        simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hF
        rw [Subgroup.commutator_comm]
        rcases hF with rfl | rfl
        · exact hCA
        · exact hCAx)
    simpa only [sSup_pair] using hh
  have hCB : ⁅C,twoResidualIn E⁆ ≤ Z :=
    (Subgroup.commutator_mono le_rfl (SevenSix.twoResidualIn_le E)).trans hCE
  have hZB : ⁅Z,twoResidualIn E⁆ = ⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
    ((hcenter.trans (SevenSix.centerAmbient_le_centralizer P)).trans
      (Subgroup.centralizer_le ((SevenSix.twoResidualIn_le E).trans geom.group_le)))
  have hCtwo : IsPGroup 2 C := by
    have hRtwo : IsPGroup 2 R := by
      change IsPGroup 2 (Γ.twoCoreAt _)
      rw [Γ.twoCoreAt_def]
      exact (pCore_isPGroup (p := 2)).map _
    exact hRtwo.to_le hCR
  have hidem : ⁅⁅C,twoResidualIn E⁆,twoResidualIn E⁆ = ⁅C,twoResidualIn E⁆ :=
    commutator_twoResidualAmbient_idempotent C E hCtwo (geom.group_le.trans hPC)
  have hzero : ⁅C,twoResidualIn E⁆ = ⊥ := by
    rw [←hidem]
    exact bot_unique ((Subgroup.commutator_mono hCB le_rfl).trans_eq hZB)
  obtain ⟨hN,hW,action,hformula,hkernel,hgenerate⟩ :=
    eight_six_next_quotient_module_data_local ctx hcenter hlength hcard data.first_commutator
  let _ := hN
  have hmodule : V = ⁅R,twoResidualIn E⁆ :=
    (eight_six_cost_four_full_module_card ctx hcenter hquot hlength hcard
      previous D L Q hprev data E A0 actor geom hcore hedge hD hL ha hout hlarge hmin hQ hcost
      hN hW action hformula hkernel hgenerate).2
  have hdecomposition := eight_six_selected_residual_decomposition ctx hcenter hquot hlength hcard
    previous D L Q hprev data E A0 actor geom hcore hedge hD hL
  have hfixed : V ⊓ Subgroup.centralizer (twoResidualIn E : Set G) = Z := by
    have hh := hdecomposition.2.1
    change ⁅R,twoResidualIn E⁆ ⊓ (V ⊓ Subgroup.centralizer (twoResidualIn E : Set G)) = Z at hh
    rw [← hmodule] at hh
    simpa only [← inf_assoc,inf_idem] using hh
  apply le_antisymm
  · exact (le_inf hCcontained (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hzero)).trans_eq hfixed
  · change Z ≤ CenterAmbient V
    rw [eight_six_centerAmbient_eq_inf_centralizer]
    have hZV : Z ≤ V := (eight_six_first_step_fixed_line_local ctx hcenter hcard).2.trans
      (lemma_seven_four ctx.sectionSeven Γ cp).first_containment.1
    exact le_inf hZV
      ((hcenter.trans (SevenSix.centerAmbient_le_centralizer P)).trans
        (Subgroup.centralizer_le (hVR.trans hRP)))

end Stellmacher.SectionEight
