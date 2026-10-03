module
public import Theory.GroupAction.CyclicQuotientRestrictionBound
public import Stellmacher.SectionEight.EightSixSelectedOrbitV2

/-!
# The selected coatom has residual displacement at most sixteen

In the high-cost branch of Stellmacher (8.6), every mover in the actual
selected coatom A0 has displacement order at most sixteen on Y/Znext,
where Y=[Qnext,O²(E)]. The exact source-(12) telescope, high-cost premise,
source-(7) actor index and source-(14) residual noncontainment are retained.
There is no extra involution hypothesis or raw quotient action model.

Put V2=⟨(Y intersect D)^E⟩ and U=⟨Za^E⟩. The previous packet gives
|Y:V2|=4 and [V2,A0]≤U. Source (12) gives |U|=8, and the actual next
center line has order two, so U/Znext has order four. The generic quotient
displacement restriction count therefore bounds the full cyclic image by
4*4=16. Normality and quotient commutativity follow from the original
first-commutator identity, and every subgroup remains the actual one.

Source: Stellmacher, Journal of Algebra 190 (1997), proof of (8.6), printed
pp.44–45, paragraph before assertion (17); refs/files/stellmacher-n-group.pdf.
-/

namespace Stellmacher.SectionEight
open Later SectionsFiveToSeven CosetGraphContext
universe u

public theorem eight_six_selected_coatom_displacement_le_sixteen
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
      Nat.card (VAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.a : Subgroup G))
    (hYnot : ¬ ⁅QAt ctx.Γ ctx.criticalPath.firstStep,twoResidualIn E⁆ ≤
      QAt ctx.Γ ctx.criticalPath.a)
   
    (mover : G) (hmover : mover ∈ A0) :
    let Y := ⁅QAt ctx.Γ ctx.criticalPath.firstStep,twoResidualIn E⁆
    (ZAt ctx.Γ ctx.criticalPath.firstStep).relIndex
      (⁅Y,Subgroup.zpowers mover⁆ ⊔ ZAt ctx.Γ ctx.criticalPath.firstStep) ≤ 16 := by
  classical
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let V := VAt Γ cp.firstStep
  let R := QAt Γ cp.firstStep
  let Z := ZAt Γ cp.firstStep
  let U := conjugateClosure (ZAt Γ cp.a) E
  let B := twoResidualIn E
  let Y := ⁅R,B⁆
  let V2 := conjugateClosure (Y ⊓ D) E
  have hEV : E ≤ Subgroup.normalizer (V : Set G) :=
    geom.group_le.trans (stabilizer_le_normalizer_v Γ cp.firstStep)
  have hER : E ≤ Subgroup.normalizer (R : Set G) :=
    geom.group_le.trans (SevenSix.stabilizer_le_normalizer_q Γ cp.firstStep)
  have hBE : B ≤ E := SevenSix.twoResidualIn_le E
  have hEB : E ≤ Subgroup.normalizer (B : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hBE).mp (SevenSix.twoResidualIn_normal E)
  have hEY : E ≤ Subgroup.normalizer (Y : Set G) := by
    intro e he
    apply Subgroup.mem_normalizer_iff_map_conj_eq.mpr
    change (⁅R,B⁆).map (MulAut.conj e).toMonoidHom = ⁅R,B⁆
    rw [Subgroup.map_commutator]
    exact congrArg₂ (fun K J : Subgroup G => ⁅K,J⁆)
      (Subgroup.mem_normalizer_iff_map_conj_eq.mp (hER he))
      (Subgroup.mem_normalizer_iff_map_conj_eq.mp (hEB he))
  have hVR : V ≤ R := SevenSix.neighbor_join_le_core_of_length_gt_one Γ cp
    (by exact hlength ▸ by decide) _
  have hpacket := eight_six_selected_residual_decomposition ctx hcenter hquot hlength hcard
    previous D L Q hprev data E A0 actor geom hcore hedge hD hL
  have hYV : Y ≤ V := hpacket.1.le.trans
    (Subgroup.le_normalizer_iff_commutator_le_left.mp (hBE.trans hEV))
  have hV2Y : V2 ≤ Y := eight_six_conjugate_closure_le _ _ _ inf_le_left hEY
  have hUY : U ≤ Y := eight_six_selected_orbit_le_residual_commutator ctx hcenter hquot
    hlength hcard previous D L Q hprev data E A0 actor geom hcore hedge hD hL
  have hseed : ZAt Γ cp.a ≤ U := by
    intro z hz
    exact Subgroup.subset_closure ⟨(1:E),⟨z,hz⟩,by simp⟩
  have hZU : Z ≤ U := (eight_six_first_step_fixed_line_local ctx hcenter hcard).2.trans hseed
  have hZY : Z ≤ Y := hZU.trans hUY
  have hRG : R ≤ GAt Γ cp.firstStep := by
    change Γ.twoCoreAt cp.firstStep ≤ Γ.vertexStabilizer cp.firstStep
    rw [Γ.twoCoreAt_def]
    exact Subgroup.map_subtype_le _
  have hN : (Z.subgroupOf Y).Normal := Subgroup.normal_subgroupOf_of_le_normalizer
    (((hYV.trans hVR).trans hRG).trans (stabilizer_le_normalizer_z Γ cp.firstStep))
  have habelian : ⁅Y,Y⁆ ≤ Z := (Subgroup.commutator_mono hYV (hYV.trans hVR)).trans_eq
    data.first_commutator
  have hmE : mover ∈ E := (geom.generated ▸ le_sup_left)
    ((geom.coatom_eq ▸ hmover).1)
  have hbound := eight_six_selected_orbit_v2_core ctx hcenter hquot hlength hcard
    previous D L Q hprev data E A0 actor geom hcore hedge hD hL hhigh hlarge
  have hcomm : ⁅V2,Subgroup.zpowers mover⁆ ≤ U :=
    (Subgroup.commutator_mono le_rfl (Subgroup.zpowers_le.mpr hmover)).trans hbound.1
  have hcardinal := (eight_six_selected_orbit_v2_support ctx hcenter hquot hlength hcard
    previous D L Q hprev data E A0 actor geom hcore hedge hD hL hhigh hlarge hYnot).2
  have hindex : V2.relIndex Y = 4 := by
    have hh := (V2.subgroupOf Y).index_mul_card
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hV2Y).toEquiv] at hh
    change V2.relIndex Y * Nat.card V2 = Nat.card Y at hh
    change Nat.card Y = 4 * Nat.card V2 at hcardinal
    have hp : 0 < Nat.card V2 := Nat.card_pos
    nlinarith
  have hsmall : Z.relIndex U = 4 := by
    have hu : Nat.card U = 8 := eight_six_selected_orbit_card_eight ctx hcenter hquot
      hlength hcard previous D L Q hprev data E A0 actor geom hcore hedge hD hL
    have hz : Nat.card Z = 2 := (eight_six_first_step_fixed_line_local ctx hcenter hcard).1
    have hh := (Z.subgroupOf U).index_mul_card
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZU).toEquiv,hz,hu] at hh
    change Z.relIndex U * 2 = 8 at hh
    omega
  have hh := Subgroup.quotient_commutator_relIndex_le_mul_of_restriction
    Y V2 Z U hV2Y hZY hUY hN habelian mover (hEY hmE) hcomm
  rw [hindex,hsmall] at hh
  exact hh

end Stellmacher.SectionEight
