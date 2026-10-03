module
public import Stellmacher.SectionEight.EightSixSelectedOrbitCardEight
public import Theory.GroupAction.CyclicQuotientSmallLayer

/-!
# Backward displacement of a selected orbit element

Every element of the selected elementary eight in (8.6) has displacement
of order at most four on the predecessor module modulo its center. The
actual local context, geometric witnesses, and first-commutator hypotheses
are retained. The shared local lemma requires only an initial-core actor whose predecessor
core-part commutator lies in the initial center; it is also used for (18).
This supplies the upper bound used to force the selected
orbit into the opposite-core intersection in source assertion (16).

The predecessor commutator identity makes its central quotient abelian.
Conjugation by the selected element therefore gives a literal displacement
homomorphism from the predecessor module to that quotient. The cyclic displacement
lemma identifies its image with the full cyclic commutator image, without
requiring an involution hypothesis. On the predecessor core part this
image lies in the initial center modulo the predecessor center, of order
two. The core part has index at most two, and the image/kernel count bounds
the full displacement by four. Finally the quotient-image cardinal is
translated back into the prescribed ambient relative index.

Source: Stellmacher, Journal of Algebra 190 (1997), proof of (8.6)(16),
printed p.44, `refs/files/stellmacher-n-group.pdf`.
-/

namespace Stellmacher.SectionEight
open Later SectionsFiveToSeven CosetGraphContext
open scoped commutatorElement IsMulCommutative
universe u

public theorem eight_six_backward_cost_le_four_of_core_part_commutator
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
    (mover : G) (hmQa : mover ∈ QAt ctx.Γ ctx.criticalPath.a)
    (hcomm : ⁅VAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.a,
      Subgroup.zpowers mover⁆ ≤ ZAt ctx.Γ ctx.criticalPath.a) :
    (ZAt ctx.Γ previous).relIndex
      (⁅VAt ctx.Γ previous,Subgroup.zpowers mover⁆ ⊔ ZAt ctx.Γ previous) ≤ 4 := by
  classical
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let V := VAt Γ previous
  let R := QAt Γ previous
  let Z := ZAt Γ previous
  let B := ZAt Γ cp.a
  let A := V ⊓ QAt Γ cp.a
  have hback : cp.a ∈ Neighborhood Γ previous :=
    (SevenSix.mem_neighborhood_iff_adjacent Γ).mpr
      (Γ.adjacent_symm ((SevenSix.mem_neighborhood_iff_adjacent Γ).mp hprev.1))
  have hVR : V ≤ R := SevenSix.neighbor_join_le_core_of_length_gt_one Γ cp
    (by exact hlength ▸ by decide) previous
  have hRG : R ≤ GAt Γ previous := by
    change Γ.twoCoreAt _ ≤ _
    rw [Γ.twoCoreAt_def]
    exact Subgroup.map_subtype_le _
  have hBV : B ≤ V := by
    change ZAt Γ cp.a ≤ VAt Γ previous
    rw [VAt, v, Γ.vAt_def]
    exact le_sSup ⟨cp.a,hback,rfl⟩
  have hlines := eight_six_neighbor_center_lines ctx hcenter hquot hlength hcard previous hprev
  have hZB : Z ≤ B := hlines.2.1
  have hZV : Z ≤ V := hZB.trans hBV
  have hZcard : Nat.card Z = 2 := hlines.1
  have hBcard : Nat.card B = 4 := hcard
  have hRV : ⁅R,V⁆ = Z := (eight_six_predecessor_commutator_and_center_bound
    ctx.sectionSeven Γ cp hcenter hcard previous hprev.1 D L Q data).1
  have hZcentral : Z ≤ Subgroup.centralizer (V : Set G) :=
    (((lemma_seven_three ctx.sectionSeven Γ).center_core previous cp.a hback).trans
      ((SevenSix.omegaOneCenter_le_centerAmbient _).trans
        (SevenSix.centerAmbient_le_centralizer _))).trans (Subgroup.centralizer_le hVR)
  let hN : (Z.subgroupOf V).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer
      ((Subgroup.le_centralizer_iff.mp hZcentral).trans (Subgroup.centralizer_le_normalizer _))
  have hmG : mover ∈ GAt Γ previous :=
    ((lemma_seven_three ctx.sectionSeven Γ).sylow_and_core cp.a previous hprev.1 default).2.2
      hmQa
  have hmV : mover ∈ Subgroup.normalizer (V : Set G) :=
    stabilizer_le_normalizer_v Γ previous hmG
  have hsmall : Z.relIndex B ≤ 2 := by
    have hcount := (Z.subgroupOf B).index_mul_card
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZB).toEquiv,hZcard,hBcard] at hcount
    change Z.relIndex B * 2 = 4 at hcount
    omega
  have hVp : IsPGroup 2 V := by
    have hRp : IsPGroup 2 R := by
      change IsPGroup 2 (Γ.twoCoreAt _)
      rw [Γ.twoCoreAt_def]
      exact (pCore_isPGroup (p := 2)).map _
    exact hRp.to_le hVR
  have hVGa : V ≤ GAt Γ cp.a := hVR.trans
    (((lemma_seven_three ctx.sectionSeven Γ).sylow_and_core previous cp.a hback default).2.2)
  have hindex : A.relIndex V ∣ 2 :=
    eight_six_two_subgroup_core_part_index_dvd_two _ _ V hVGa hVp hquot
  have hidxBound : (A.subgroupOf V).index ≤ 2 := Nat.le_of_dvd (by decide) hindex
  have hsize : Nat.card V ≤ 2 * Nat.card A := by
    have hh := (A.subgroupOf V).index_mul_card
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (show A ≤ V from inf_le_left)).toEquiv] at hh
    calc
      Nat.card V = (A.subgroupOf V).index * Nat.card A := hh.symm
      _ ≤ 2 * Nat.card A := Nat.mul_le_mul_right _ hidxBound
  exact Subgroup.quotient_commutator_relIndex_le_four_of_index_two_small_layer
    V A Z B inf_le_left hZV hBV hN
    ((Subgroup.commutator_mono hVR le_rfl).trans_eq hRV)
    mover hmV hsize hsmall hcomm

public theorem eight_six_selected_orbit_backward_cost_le_four
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
    (mover : G) (hmover : mover ∈ conjugateClosure (ZAt ctx.Γ ctx.criticalPath.a) E) :
    (ZAt ctx.Γ previous).relIndex
      (⁅VAt ctx.Γ previous, Subgroup.zpowers mover⁆ ⊔ ZAt ctx.Γ previous) ≤ 4 := by
  let A := VAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.a
  let U := conjugateClosure (ZAt ctx.Γ ctx.criticalPath.a) E
  have hUA : ⁅U,A⁆ ≤ ZAt ctx.Γ ctx.criticalPath.a := le_sup_left.trans_eq
    (eight_six_selected_orbit_commutator_sup_line ctx hcenter hquot hlength hcard
      previous D L Q hprev data E A0 actor geom hcore hedge hD hL)
  have hAB : ⁅A,Subgroup.zpowers mover⁆ ≤ ZAt ctx.Γ ctx.criticalPath.a := by
    rw [Subgroup.commutator_comm]
    exact (Subgroup.commutator_mono (Subgroup.zpowers_le.mpr hmover) le_rfl).trans hUA
  exact eight_six_backward_cost_le_four_of_core_part_commutator ctx hcenter hquot hlength
    hcard previous D L Q hprev data mover (hcore hmover) hAB

end Stellmacher.SectionEight
