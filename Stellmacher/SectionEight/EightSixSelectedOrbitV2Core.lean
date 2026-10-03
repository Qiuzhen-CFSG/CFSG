module
public import Stellmacher.SectionEight.EightSixSelectedOrbitIntersection
public import Stellmacher.SectionEight.EightSixSelectedResidualDecomposition

/-!
# Coatom and core control for the second selected orbit

In the high-cost branch of Stellmacher (8.6), let Y=[Qnext,O²(E)],
U=⟨Za^E⟩, and V2=⟨(Y intersect D)^E⟩. The actual selected coatom A0
satisfies [V2,A0]≤U, and V2 lies in the initial two-core Qa. The source-(12)
local telescope, the uniform high-cost premise, and the source-(7) actor
index bound are retained. No small quotient action model is assumed.

The seed commutator lies in Zprevious≤U. Since [E,A0]≤Qnext and
[Vnext,Qnext]=Znext≤U, an explicit commutator identity propagates this
bound to all E-conjugates and their closure. Source (16) gives U≤D.
If V2 escaped Qa, the cubic subgroup-forcing lemma would put A0 inside D,
contradicting the large actor index. The first conclusion also supplies
the coatom displacement bound used in source (17).

Source: Stellmacher, Journal of Algebra 190 (1997), proof of (8.6), printed
p.44, the paragraph following assertion (16); refs/files/stellmacher-n-group.pdf.
-/

namespace Stellmacher.SectionEight
open Later SectionsFiveToSeven CosetGraphContext
open scoped commutatorElement
universe u

private theorem closure_commutator_le_of_commutator_kernel
    {G : Type u} [Group G] (B E A R V U : Subgroup G)
    (hBV : B ≤ V) (hEV : E ≤ Subgroup.normalizer (V : Set G))
    (hEU : E ≤ Subgroup.normalizer (U : Set G))
    (hVU : V ≤ Subgroup.normalizer (U : Set G))
    (hRU : R ≤ Subgroup.normalizer (U : Set G))
    (hEA : ⁅E,A⁆ ≤ R) (hVR : ⁅V,R⁆ ≤ U) (hBA : ⁅B,A⁆ ≤ U) :
    ⁅conjugateClosure B E,A⁆ ≤ U := by
  have hconj (e : G) (he : e ∈ E) (b : G) (hb : b ∈ B) (a : G) (ha : a ∈ A) :
      ⁅e*b*e⁻¹,a⁆ ∈ U := by
    have hc : ⁅e⁻¹,a⁆ ∈ R := hEA (Subgroup.commutator_mem_commutator (E.inv_mem he) ha)
    have hbc : ⁅b,⁅e⁻¹,a⁆⁆ ∈ U := hVR (Subgroup.commutator_mem_commutator (hBV hb) hc)
    have hba : ⁅b,a⁆ ∈ U := hBA (Subgroup.commutator_mem_commutator hb ha)
    have hp : ⁅b,⁅e⁻¹,a⁆*a⁆ ∈ U := by
      rw [commutatorElement_mul_right_eq_mul_conj]
      simpa only [mul_assoc] using (U.mul_mem hbc
        ((Subgroup.mem_normalizer_iff.mp (hRU hc) _).mp hba))
    have heq : ⁅e*b*e⁻¹,a⁆ = e * ⁅b,⁅e⁻¹,a⁆*a⁆ * e⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [heq]
    exact (Subgroup.mem_normalizer_iff.mp (hEU he) _).mp hp
  apply Subgroup.commutator_le.mpr
  intro x hx a ha
  have hh : x ∈ V ∧ ∀ a ∈ A, ⁅x,a⁆ ∈ U := by
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨e,b,rfl⟩ := hx
      exact ⟨(Subgroup.mem_normalizer_iff.mp (hEV e.property) b).mp (hBV b.property),
        hconj e e.property b b.property⟩
    | one => exact ⟨V.one_mem,by simp⟩
    | mul x y hx hy hix hiy =>
      refine ⟨V.mul_mem hix.1 hiy.1, ?_⟩
      intro a ha
      rw [commutatorElement_mul_left_eq_conj_mul]
      exact U.mul_mem ((Subgroup.mem_normalizer_iff.mp (hVU hix.1) _).mp (hiy.2 a ha))
        (hix.2 a ha)
    | inv x hx hix =>
      refine ⟨V.inv_mem hix.1, ?_⟩
      intro a ha
      rw [commutatorElement_inv_left, ← commutatorElement_inv]
      simpa only [inv_inv] using (Subgroup.mem_normalizer_iff.mp
        (hVU (V.inv_mem hix.1)) _).mp (U.inv_mem (hix.2 a ha))
  exact hh.2 a ha

public theorem eight_six_selected_orbit_v2_core
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
    (hhigh : ∀ mover : G, mover ∈ VAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.a →
      mover ∉ QAt ctx.Γ ctx.criticalPath.firstStep →
        8 ≤ eightSixCommutatorCost ctx.Γ ctx.criticalPath mover)
    (hlarge : 4 * Nat.card
      ((VAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.a) ⊓ D : Subgroup G) ≤
      Nat.card (VAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.a : Subgroup G)) :
    ⁅conjugateClosure (⁅QAt ctx.Γ ctx.criticalPath.firstStep,twoResidualIn E⁆ ⊓ D) E,A0⁆ ≤
      conjugateClosure (ZAt ctx.Γ ctx.criticalPath.a) E ∧
    conjugateClosure (⁅QAt ctx.Γ ctx.criticalPath.firstStep,twoResidualIn E⁆ ⊓ D) E ≤
      QAt ctx.Γ ctx.criticalPath.a := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let V := VAt Γ cp.firstStep
  let R := QAt Γ cp.firstStep
  let Z := ZAt Γ cp.firstStep
  let U := conjugateClosure (ZAt Γ cp.a) E
  let Y := ⁅R,twoResidualIn E⁆
  let A := VAt Γ previous ⊓ QAt Γ cp.a
  let V2 := conjugateClosure (Y ⊓ D) E
  have hlen : cp.length = 2 := hlength
  have hAE : A ≤ E := geom.generated ▸ le_sup_left
  have hA0A : A0 ≤ A := geom.coatom_eq ▸ inf_le_left
  have hEV : E ≤ Subgroup.normalizer (V : Set G) :=
    geom.group_le.trans (stabilizer_le_normalizer_v Γ cp.firstStep)
  have hVR : V ≤ R := SevenSix.neighbor_join_le_core_of_length_gt_one Γ cp (by omega) _
  have hpacket := eight_six_selected_residual_decomposition ctx hcenter hquot hlength hcard
    previous D L Q hprev data E A0 actor geom hcore hedge hD hL
  have hYV : Y ≤ V := hpacket.1.le.trans
    (Subgroup.le_normalizer_iff_commutator_le_left.mp ((SevenSix.twoResidualIn_le E).trans hEV))
  have hV2V : V2 ≤ V := eight_six_conjugate_closure_le _ _ _ (inf_le_left.trans hYV) hEV
  have hseed : ZAt Γ cp.a ≤ U := by
    intro z hz
    exact Subgroup.subset_closure ⟨(1:E),⟨z,hz⟩,by simp⟩
  have hZU : Z ≤ U := (eight_six_first_step_fixed_line_local ctx hcenter hcard).2.trans hseed
  have hRU : R ≤ Subgroup.normalizer (U : Set G) :=
    Subgroup.le_normalizer_iff_commutator_le_left.mpr
      ((Subgroup.commutator_mono
        (eight_six_conjugate_closure_le _ _ _
          (lemma_seven_four ctx.sectionSeven Γ cp).first_containment.1 hEV) le_rfl).trans
            (data.first_commutator.le.trans hZU))
  have hprevComm := (eight_six_predecessor_commutator_and_center_bound ctx.sectionSeven Γ cp
    hcenter hcard previous hprev.1 D L Q data).1
  have hprevZa : ZAt Γ previous ≤ ZAt Γ cp.a :=
    (eight_six_neighbor_center_lines ctx hcenter hquot hlength hcard previous hprev).2.1
  have hcomm : ⁅V2,A0⁆ ≤ U := closure_commutator_le_of_commutator_kernel
    (Y ⊓ D) E A0 R V U (inf_le_left.trans hYV) hEV
    (eight_six_conjugate_closure_normalizer _ _) (hVR.trans hRU) hRU
    geom.coatom_commutator
    (data.first_commutator.le.trans hZU)
    (((Subgroup.commutator_mono
      (inf_le_right.trans (hD ▸ inf_le_left)) (hA0A.trans inf_le_left)).trans_eq hprevComm).trans
      (hprevZa.trans hseed))
  have hUD : U ≤ D := eight_six_selected_orbit_le_intersection ctx hcenter hquot
    hlength hcard previous D L Q hprev data E A0 actor geom hcore hedge hD hL hhigh
  refine ⟨hcomm,?_⟩
  by_contra hnot
  obtain ⟨x,hx,hout⟩ := SetLike.not_le_iff_exists.mp hnot
  have hforced : A0 ≤ D := by
    apply eight_six_cubic_subgroup_forcing ctx.sectionSeven Γ cp.a cp.firstStep previous
      hquot ((SevenSix.mem_neighborhood_iff_adjacent Γ).mpr cp.firstStep_adj)
      hprev.1 hprev.2 D hD data.intersection_normal x (hVR (hV2V hx)) hout A0
    · exact (hA0A.trans inf_le_left).trans
        (SevenSix.neighbor_join_le_core_of_length_gt_one Γ cp (by omega) previous)
    · exact (Subgroup.commutator_mono le_rfl (Subgroup.zpowers_le.mpr hx)).trans
        ((Subgroup.commutator_comm V2 A0 ▸ hcomm).trans hUD)
  have hbound : Nat.card A0 ≤ Nat.card (A ⊓ D : Subgroup G) :=
    Subgroup.card_le_of_le (le_inf hA0A hforced)
  have hcoatom : Nat.card A = 2 * Nat.card A0 := geom.coatom_card
  have hpos : 0 < Nat.card A0 := Nat.card_pos
  change 4 * Nat.card (A ⊓ D : Subgroup G) ≤ Nat.card A at hlarge
  omega

end Stellmacher.SectionEight
