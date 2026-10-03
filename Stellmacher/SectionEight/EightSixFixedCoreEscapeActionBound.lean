module
public import Stellmacher.SectionEight.EightSixNextCoreNormalSupplement
public import Stellmacher.SectionEight.EightSixSelectedFixedCoreIntersection

/-!
If the selected residual-fixed subgroup V0 of the next core escapes the
initial core, every actor in the predecessor core part has displacement
index at most two modulo C=Vnext intersect V0. The normal-supplement theorem
first gives Qnext=V0D. Since the actor normalizes V0 and [D,A] is contained
in the predecessor center line, its displacement on Vnext lies in V0Zprev.
Intersecting with Vnext replaces V0 by C, and the order-two line gives
the asserted relative-index bound.

This is the small-displacement consequence in the proof of (14) of
Stellmacher's Lemma 8.6, printed p.44. The raw subgroup quotient is retained
so the later source-(13) transvection exclusion applies without changing
the actual action or its fixed subgroup.
-/

namespace Stellmacher.SectionEight
open Later SectionsFiveToSeven CosetGraphContext
open scoped commutatorElement Pointwise
universe u

public theorem eight_six_fixed_core_escape_action_index_le_two
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
      Subgroup.centralizer (twoResidualIn E : Set G) ≤ QAt ctx.Γ ctx.criticalPath.a)
    (actor : G) (ha : actor ∈ VAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.a) :
    (VAt ctx.Γ ctx.criticalPath.firstStep ⊓ Subgroup.centralizer (twoResidualIn E : Set G)).relIndex
      (⁅VAt ctx.Γ ctx.criticalPath.firstStep,Subgroup.zpowers actor⁆ ⊔
        (VAt ctx.Γ ctx.criticalPath.firstStep ⊓ Subgroup.centralizer (twoResidualIn E : Set G))) ≤ 2 := by
  classical
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let A := VAt Γ previous ⊓ QAt Γ cp.a
  let V := VAt Γ cp.firstStep
  let R := QAt Γ cp.firstStep
  let B := twoResidualIn E
  let V0 := R ⊓ Subgroup.centralizer (B : Set G)
  let C := V ⊓ Subgroup.centralizer (B : Set G)
  let Z := ZAt Γ cp.firstStep
  let Zp := ZAt Γ previous
  let J := ⁅V,Subgroup.zpowers actor⁆
  have hVcore : V ≤ R := SevenSix.neighbor_join_le_core_of_length_gt_one Γ cp
    (by exact hlength ▸ by decide) _
  have hseedV : ZAt Γ cp.a ≤ V := (lemma_seven_four ctx.sectionSeven Γ cp).first_containment.1
  have hlines := eight_six_neighbor_center_lines ctx hcenter hquot hlength hcard previous hprev
  have hZpV : Zp ≤ V := hlines.2.1.trans hseedV
  have hZV : Z ≤ V := (eight_six_first_step_fixed_line_local ctx hcenter hcard).2.trans hseedV
  have hZC : Z ≤ C := le_inf hZV
    ((hcenter.trans (SevenSix.centerAmbient_le_centralizer _)).trans
      (Subgroup.centralizer_le ((SevenSix.twoResidualIn_le E).trans hE)))
  have hZV0 : Z ≤ V0 := le_inf (hZV.trans hVcore) (hZC.trans inf_le_right)
  have hBE : B ≤ E := SevenSix.twoResidualIn_le E
  have hENB : E ≤ Subgroup.normalizer (B : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hBE).mp (SevenSix.twoResidualIn_normal E)
  have hENC : E ≤ Subgroup.normalizer ((Subgroup.centralizer (B : Set G)) : Set G) :=
    hENB.trans ((Subgroup.normal_subgroupOf_iff_le_normalizer
      (Subgroup.centralizer_le_normalizer (B : Set G))).mp inferInstance)
  have hEV0 : E ≤ Subgroup.normalizer (V0 : Set G) :=
    (le_inf (hE.trans (SevenSix.stabilizer_le_normalizer_q Γ cp.firstStep)) hENC).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  have hAV0 : A ≤ Subgroup.normalizer (V0 : Set G) := hAE.trans hEV0
  have hRdecomp : R = V0 ⊔ D := eight_six_selected_fixed_core_supplement_of_escape
    ctx hcenter hquot hlength hcard previous D L Q hprev hD hL hQ data E hE hAE hescape
  have hRGa : R ≤ GAt Γ cp.a :=
    (eight_six_generation_neighbor_core_le ctx.sectionSeven Γ cp cp.firstStep
      ((SevenSix.mem_neighborhood_iff_adjacent Γ).mpr cp.firstStep_adj)).2
  have hV0ND : V0 ≤ Subgroup.normalizer (D : Set G) :=
    (inf_le_left.trans hRGa).trans
      ((Subgroup.normal_subgroupOf_iff_le_normalizer data.intersection_normal.1).mp
        data.intersection_normal.2)
  have hcomm := eight_six_predecessor_commutator_and_center_bound ctx.sectionSeven Γ cp hcenter
    hcard previous hprev.1 D L Q data
  have hDA : ⁅D,A⁆ ≤ Zp := (Subgroup.commutator_mono (hD ▸ inf_le_left) inf_le_left).trans_eq hcomm.1
  have hRA : ⁅R,A⁆ ≤ V0 ⊔ Zp := by
    apply Subgroup.commutator_le.mpr
    intro r hr a haa
    have hrm : r ∈ (V0 : Set G) * (D : Set G) := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right _ _ hV0ND,← hRdecomp]
      exact hr
    obtain ⟨v,hv,d,hd,rfl⟩ := hrm
    rw [commutatorElement_mul_left_eq_conj_mul]
    apply (V0 ⊔ Zp).mul_mem
    · exact (V0 ⊔ Zp).mul_mem
        ((V0 ⊔ Zp).mul_mem ((show V0 ≤ V0 ⊔ Zp from le_sup_left) hv)
          ((show Zp ≤ V0 ⊔ Zp from le_sup_right) (hDA (Subgroup.commutator_mem_commutator hd haa))))
        ((V0 ⊔ Zp).inv_mem ((show V0 ≤ V0 ⊔ Zp from le_sup_left) hv))
    · exact (show V0 ≤ V0 ⊔ Zp from le_sup_left)
        ((Subgroup.le_normalizer_iff_commutator_le_left.mp hAV0)
          (Subgroup.commutator_mem_commutator hv haa))
  have hza : Subgroup.zpowers actor ≤ A := Subgroup.zpowers_le.mpr ha
  have hJV : J ≤ V := Subgroup.le_normalizer_iff_commutator_le_left.mp
    (((hza.trans hAE).trans hE).trans (stabilizer_le_normalizer_v Γ cp.firstStep))
  have hJW : J ≤ V0 ⊔ Zp := (Subgroup.commutator_mono hVcore hza).trans hRA
  have hZpNV0 : Zp ≤ Subgroup.normalizer (V0 : Set G) :=
    Subgroup.le_normalizer_iff_commutator_le_right.mpr
      (((Subgroup.commutator_mono hZpV inf_le_left).trans_eq data.first_commutator).trans hZV0)
  have hJCZp : J ≤ C ⊔ Zp := by
    intro j hj
    have hjm : j ∈ (Zp : Set G) * (V0 : Set G) := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right _ _ hZpNV0,sup_comm]
      exact hJW hj
    obtain ⟨z,hz,c,hc,hjz⟩ := hjm
    have hcV : c ∈ V := by
      have hh := V.mul_mem (V.inv_mem (hZpV hz)) (hJV hj)
      rw [← hjz] at hh
      simpa only [inv_mul_cancel_left] using hh
    rw [← hjz]
    exact (C ⊔ Zp).mul_mem ((show Zp ≤ C ⊔ Zp from le_sup_right) hz)
      ((show C ≤ C ⊔ Zp from le_sup_left) ⟨hcV,hc.2⟩)
  have hZpNC : Zp ≤ Subgroup.normalizer (C : Set G) :=
    Subgroup.le_normalizer_iff_commutator_le_right.mpr
      (((Subgroup.commutator_mono hZpV (inf_le_left.trans hVcore)).trans_eq
        data.first_commutator).trans hZC)
  let T := C ⊔ Zp
  let _ : (C.subgroupOf T).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer (sup_le C.le_normalizer hZpNC)
  have hi := Subgroup.relIndex_sup_left (Zp.subgroupOf T) (C.subgroupOf T)
  rw [← Subgroup.subgroupOf_sup le_sup_left le_sup_right,
    Subgroup.relIndex_subgroupOf le_rfl,Subgroup.relIndex_subgroupOf le_sup_right] at hi
  have hb : C.relIndex (C ⊔ Zp) ≤ Nat.card Zp := by
    rw [hi]
    exact Nat.le_of_dvd Nat.card_pos (Subgroup.relIndex_dvd_card C Zp)
  have hsmaller : C.relIndex (J ⊔ C) ≤ C.relIndex (C ⊔ Zp) :=
    Subgroup.relIndex_le_of_le_right (sup_le hJCZp le_sup_left)
      (C.subgroupOf (C ⊔ Zp)).index_ne_zero_of_finite
  exact hsmaller.trans (hb.trans hcomm.2)

end Stellmacher.SectionEight
