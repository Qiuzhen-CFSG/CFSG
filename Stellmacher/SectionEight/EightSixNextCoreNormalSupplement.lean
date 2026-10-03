module
public import Stellmacher.SectionEight.EightSixCommonStructure

/-!
An escaping subgroup of the next core that contains the opposite-core
intersection D and is normalized by Q must be the entire next core. The
initial core has index two in the edge Sylow, so an escaping element supplies
the other coset. Elementary Q/D then bounds [Q,Qnext] by the subgroup;
equation (1) fills its remaining intersection with the initial core.

For the selected group E, its residual-fixed part V0 is E-invariant. The
first commutator identity makes the terminal core part of Q normalize V0D,
and the predecessor actor normalizes both factors. Thus if V0 escapes the
initial core, Qnext=V0D. This is the algebraic reduction in the paragraph
proving (14) of Stellmacher's Lemma 8.6, printed p.44. The subsequent
transvection contradiction is a separate step.
-/

namespace Stellmacher.SectionEight
open Later SectionsFiveToSeven CosetGraphContext
open scoped commutatorElement Pointwise
universe u

public theorem eight_six_next_core_eq_of_normalized_escape
    {G : Type u} [Group G] [Finite G] {S P1 P2 : Subgroup G}
    (ctx : SectionEightLocalContext G S P1 P2)
    (hquot : QuotientIsModel (GAt ctx.Γ ctx.criticalPath.a)
      (QAt ctx.Γ ctx.criticalPath.a) SL2Two)
    (hlength : ctx.criticalPath.length = 2)
    (hcard : Nat.card (ZAt ctx.Γ ctx.criticalPath.a) = 4)
    (previous : ctx.Γ.Vertex) (D L Q : Subgroup G)
    (hprev : previous ∈ Neighborhood ctx.Γ ctx.criticalPath.a ∧
      previous ≠ ctx.criticalPath.firstStep)
    (hD : D = QAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.firstStep)
    (hL : L = conjugateClosure (QAt ctx.Γ previous) (GAt ctx.Γ ctx.criticalPath.a))
    (hQ : Q = twoCoreIn L)
    (data : EightSixEquationOneData ctx.Γ ctx.criticalPath previous D L Q)
    (W : Subgroup G) (hDW : D ≤ W)
    (hWR : W ≤ QAt ctx.Γ ctx.criticalPath.firstStep)
    (hQW : Q ≤ Subgroup.normalizer (W : Set G))
    (hescape : ¬ W ≤ QAt ctx.Γ ctx.criticalPath.a) :
    W = QAt ctx.Γ ctx.criticalPath.firstStep := by
  classical
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let R := QAt Γ cp.firstStep
  let Qa := QAt Γ cp.a
  have hcore := eight_six_rigidity_core_containments ctx.sectionSeven Γ cp previous D L Q hD data
  have hcoreEq := eight_six_generation_core_eq_inter ctx.sectionSeven Γ cp previous hprev.1
    L Q hL hQ
  have hRL : R ≤ L := by
    rw [hL]
    exact eight_six_first_core_le_previous_closure ctx.sectionSeven Γ cp previous hprev.1
  have hRS : R ≤ S := (SevenSix.local_cores_le_edge_sylow ctx.sectionSeven Γ cp).2
  have hWS : W ≤ S := hWR.trans hRS
  have hindex : Qa.relIndex S = 2 := by
    change (q Γ cp.a).relIndex S = 2
    rw [q,Γ.twoCoreAt_def]
    exact eight_two_core_relIndex_two _ _
      (SevenSix.edge_local_data ctx.sectionSeven Γ cp).1.1.1.2.1
      (eight_five_dihedral_action_of_card_four_local ctx hcard).1
  obtain ⟨outside,houtsideW,houtsideQa⟩ := SetLike.not_le_iff_exists.mp hescape
  change outside ∉ Qa at houtsideQa
  have houtsideR : outside ∈ R := hWR houtsideW
  have hreduce (r : G) (hr : r ∈ R) (hrQa : r ∉ Qa) : outside⁻¹ * r ∈ Qa := by
    apply (Qa.subgroupOf S).mul_mem_iff_of_index_two hindex
      (a := ⟨outside⁻¹,S.inv_mem (hWS houtsideW)⟩) (b := ⟨r,hRS hr⟩) |>.mpr
    simp only [Subgroup.mem_subgroupOf,Subgroup.inv_mem_iff,houtsideQa,hrQa]
  have hRcover : R ≤ Q ⊔ W := by
    intro r hr
    by_cases hQa : r ∈ Qa
    · apply (show Q ≤ Q ⊔ W from le_sup_left)
      rw [hcoreEq]
      exact ⟨hRL hr,hQa⟩
    · have hq : outside⁻¹ * r ∈ Q := by
        rw [hcoreEq]
        exact ⟨L.mul_mem (L.inv_mem (hRL houtsideR)) (hRL hr),hreduce r hr hQa⟩
      simpa only [mul_inv_cancel_left] using (Q ⊔ W).mul_mem
        ((show W ≤ Q ⊔ W from le_sup_right) houtsideW)
        ((show Q ≤ Q ⊔ W from le_sup_left) hq)
  have hQQ : ⁅Q,Q⁆ ≤ D := by
    have hp : IsPGroup 2 Q := by
      rw [hQ]
      exact (pCore_isPGroup (p := 2)).map _
    let _ : Fact (IsPGroup 2 Q) := ⟨hp⟩
    have hm : (_root_.commutator Q).map Q.subtype = ⁅Q,Q⁆ := by
      rw [_root_.commutator_def,Subgroup.map_commutator,
        ← MonoidHom.range_eq_map,Subgroup.range_subtype]
    rw [← hm]
    exact (Subgroup.map_mono (commutator_le_frattini_of_isPGroup (p := 2))).trans
      data.core_frattini_le
  have hQRW : ⁅Q,R⁆ ≤ W := by
    apply Subgroup.commutator_le.mpr
    intro q hq r hr
    have hrm : r ∈ (Q : Set G) * (W : Set G) := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right _ _ hQW]
      exact hRcover hr
    obtain ⟨q',hq',w,hw,rfl⟩ := hrm
    rw [commutatorElement_mul_right_eq_mul_conj]
    have hconj := (Subgroup.mem_normalizer_iff.mp (hQW hq') _).mp
      ((Subgroup.le_normalizer_iff_commutator_le_right.mp hQW)
        (Subgroup.commutator_mem_commutator hq hw))
    simpa only [mul_assoc] using
      W.mul_mem (hDW (hQQ (Subgroup.commutator_mem_commutator hq hq'))) hconj
  have hinter : R ⊓ Qa ≤ W := by
    have heq := eight_six_neighbor_core_part_local ctx hquot hlength previous hprev D hD
      data.intersection_normal (hcore.1.trans hcore.2.1)
    rw [heq,← data.core_commutator]
    exact sup_le hQRW hDW
  apply le_antisymm hWR
  intro r hr
  by_cases hQa : r ∈ Qa
  · exact hinter ⟨hr,hQa⟩
  · have hprod : outside⁻¹ * r ∈ W :=
      hinter ⟨R.mul_mem (R.inv_mem houtsideR) hr,hreduce r hr hQa⟩
    simpa only [mul_inv_cancel_left] using W.mul_mem houtsideW hprod

public theorem eight_six_selected_fixed_core_supplement_of_escape
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
    (hD : D = QAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.firstStep)
    (hL : L = conjugateClosure (QAt ctx.Γ previous) (GAt ctx.Γ ctx.criticalPath.a))
    (hQ : Q = twoCoreIn L)
    (data : EightSixEquationOneData ctx.Γ ctx.criticalPath previous D L Q)
    (E : Subgroup G) (hE : E ≤ GAt ctx.Γ ctx.criticalPath.firstStep)
    (hAE : VAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.a ≤ E)
    (hescape : ¬ QAt ctx.Γ ctx.criticalPath.firstStep ⊓
      Subgroup.centralizer (twoResidualIn E : Set G) ≤ QAt ctx.Γ ctx.criticalPath.a) :
    QAt ctx.Γ ctx.criticalPath.firstStep =
      (QAt ctx.Γ ctx.criticalPath.firstStep ⊓ Subgroup.centralizer (twoResidualIn E : Set G)) ⊔ D := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let A := VAt Γ previous ⊓ QAt Γ cp.a
  let V := VAt Γ cp.firstStep
  let R := QAt Γ cp.firstStep
  let B := twoResidualIn E
  let V0 := R ⊓ Subgroup.centralizer (B : Set G)
  let W := V0 ⊔ D
  have hcore := eight_six_rigidity_core_containments ctx.sectionSeven Γ cp previous D L Q hD data
  have hDR : D ≤ R := hD ▸ inf_le_right
  have hWR : W ≤ R := sup_le inf_le_left hDR
  have hZDW : ZAt Γ cp.firstStep ≤ W :=
    ((eight_six_first_step_fixed_line_local ctx hcenter hcard).2.trans hcore.2.2.1).trans
      le_sup_right
  have hBE : B ≤ E := SevenSix.twoResidualIn_le E
  have hENB : E ≤ Subgroup.normalizer (B : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hBE).mp (SevenSix.twoResidualIn_normal E)
  have hENC : E ≤ Subgroup.normalizer ((Subgroup.centralizer (B : Set G)) : Set G) :=
    hENB.trans ((Subgroup.normal_subgroupOf_iff_le_normalizer
      (Subgroup.centralizer_le_normalizer (B : Set G))).mp inferInstance)
  have hEV0 : E ≤ Subgroup.normalizer (V0 : Set G) :=
    (le_inf (hE.trans (SevenSix.stabilizer_le_normalizer_q Γ cp.firstStep)) hENC).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  have hAQ : A ≤ Q := by rw [data.core_generation]; exact le_sup_left.trans le_sup_left
  have hQaG : QAt Γ cp.a ≤ GAt Γ cp.a := by
    change Γ.twoCoreAt _ ≤ Γ.vertexStabilizer _
    rw [Γ.twoCoreAt_def]
    exact Subgroup.map_subtype_le _
  have hAD : A ≤ Subgroup.normalizer (D : Set G) :=
    ((hAQ.trans hcore.2.1).trans hQaG).trans
      ((Subgroup.normal_subgroupOf_iff_le_normalizer data.intersection_normal.1).mp
        data.intersection_normal.2)
  have hAW : A ≤ Subgroup.normalizer (W : Set G) :=
    (le_inf (hAE.trans hEV0) hAD).trans
      (Subgroup.normalizer_inf_normalizer_le_normalizer_sup V0 D)
  have hBW : V ⊓ QAt Γ cp.a ≤ Subgroup.normalizer (W : Set G) :=
    Subgroup.le_normalizer_iff_commutator_le_right.mpr
      (((Subgroup.commutator_mono inf_le_left hWR).trans_eq data.first_commutator).trans hZDW)
  have hQW : Q ≤ Subgroup.normalizer (W : Set G) := by
    rw [data.core_generation]
    exact sup_le (sup_le hAW hBW) ((show D ≤ W from le_sup_right).trans W.le_normalizer)
  exact (eight_six_next_core_eq_of_normalized_escape ctx hquot hlength hcard previous
    D L Q hprev hD hL hQ data W le_sup_right hWR hQW
      (fun hle => hescape (le_sup_left.trans hle))).symm

end Stellmacher.SectionEight
