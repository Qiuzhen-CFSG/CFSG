module
public import Stellmacher.SectionEight.EightSixSelectedResidualDecomposition
public import Stellmacher.SectionEight.EightSixSelectedOrbitCardEight
public import Stellmacher.SectionEight.GeneratedEightSixResidualCommutator

/-!
# The next residual acts as a three-group

Retain the actual selected configuration of Stellmacher (8.6)(12), and a
supplied conjugation action of the next stabilizer P on Vnext/Znext whose
kernel contains O₂(P). Then the image of O²(P) is a 3-group. The literal
normality proof, elementary quotient and action are preserved. No high-cost
premise or identification of E/C(U) with a model group is assumed.

The local residual theorem (3.3) first makes the full residual image an odd
p-group. The selected residual image preserves the image of the actual orbit
U=⟨Za^E⟩, which has order four modulo Znext. The source-(12) containment U≤Y
and the proved coprime fixed/commutator decomposition show that its only fixed
point is the identity. The p-group fixed-point congruence gives 4≡1 modulo p,
so p=3. Mapping from the range-restricted action gives the stated literal
residual image.

This supplies the prime identification used with source (19) in (8.6)(20),
Stellmacher, Journal of Algebra 190 (1997), printed pp.43–45,
refs/files/stellmacher-n-group.pdf.
-/

namespace Stellmacher.SectionEight
open Later SectionsFiveToSeven CosetGraphContext SevenSix
universe u
public theorem eight_six_next_residual_action_is_three_group
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
    (hN : ((ZAt ctx.Γ ctx.criticalPath.firstStep).subgroupOf
      (VAt ctx.Γ ctx.criticalPath.firstStep)).Normal) :
    let _ := hN
    let P := GAt ctx.Γ ctx.criticalPath.firstStep
    let V := VAt ctx.Γ ctx.criticalPath.firstStep
    let Z := ZAt ctx.Γ ctx.criticalPath.firstStep
    ∀ (_hW : IsElementaryAbelian 2 (V ⧸ Z.subgroupOf V))
      (action : P →* MulAut (V ⧸ Z.subgroupOf V)),
      (∀ mover : P, ∀ point : V,
        action mover (QuotientGroup.mk' (Z.subgroupOf V) point) =
          QuotientGroup.mk' (Z.subgroupOf V)
            ⟨(mover:G)*(point:G)*(mover:G)⁻¹,
              (Subgroup.mem_normalizer_iff.mp
                (stabilizer_le_normalizer_v ctx.Γ ctx.criticalPath.firstStep
                  mover.property) point).mp point.property⟩) →
      pCore 2 P ≤ action.ker →
      IsPGroup 3 (((twoResidualIn P).subgroupOf P).map action) := by
  classical
  let _ := hN
  dsimp only
  intro hW action hformula hkernel
  let _ := hW
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let P := GAt Γ cp.firstStep
  let V := VAt Γ cp.firstStep
  let Z := ZAt Γ cp.firstStep
  let W := V ⧸ Z.subgroupOf V
  let U := conjugateClosure (ZAt Γ cp.a) E
  let B := twoResidualIn E
  let Y := ⁅QAt Γ cp.firstStep,B⁆
  let Bbar := (B.subgroupOf P).map action.rangeRestrict
  let π := QuotientGroup.mk' (Z.subgroupOf V)
  let J := (U.subgroupOf V).map π
  have hBE : B ≤ E := twoResidualIn_le E
  have hBP : B ≤ P := hBE.trans geom.group_le
  have hpacket := eight_six_selected_residual_decomposition ctx hcenter hquot hlength
    hcard previous D L Q hprev data E A0 actor geom hcore hedge hD hL
  have hYV : Y ≤ V := hpacket.2.2.ge.trans' le_sup_left
  have hUY : U ≤ Y := eight_six_selected_orbit_le_residual_commutator ctx hcenter hquot
    hlength hcard previous D L Q hprev data E A0 actor geom hcore hedge hD hL
  have hUV : U ≤ V := hUY.trans hYV
  have hZaU : ZAt Γ cp.a ≤ U := by
    intro z hz
    exact Subgroup.subset_closure ⟨(1:E),⟨z,hz⟩,by simp⟩
  have hZU : Z ≤ U := (eight_six_first_step_fixed_line_local ctx hcenter hcard).2.trans hZaU
  have hUcard : Nat.card U = 8 := eight_six_selected_orbit_card_eight ctx hcenter hquot
    hlength hcard previous D L Q hprev data E A0 actor geom hcore hedge hD hL
  have hZcard : Nat.card Z = 2 := (eight_six_first_step_fixed_line_local ctx hcenter hcard).1
  have hJcard : Nat.card J = 4 := by
    change Nat.card ((U.subgroupOf V).map (QuotientGroup.mk' (Z.subgroupOf V))) = 4
    rw [← Subgroup.relIndex_ker,QuotientGroup.ker_mk',Subgroup.relIndex_subgroupOf hUV]
    have hcount := (Z.subgroupOf U).index_mul_card
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZU).toEquiv,hZcard,hUcard] at hcount
    change Z.relIndex U * 2 = 8 at hcount
    omega
  have hEU : E ≤ Subgroup.normalizer (U : Set G) :=
    eight_six_conjugate_closure_normalizer _ _
  have hJforward (b : P) (hb : b ∈ B.subgroupOf P) (w : W) (hw : w ∈ J) :
      action b w ∈ J := by
    obtain ⟨v,hv,rfl⟩ := hw
    rw [hformula]
    exact Subgroup.mem_map_of_mem π
      ((Subgroup.mem_normalizer_iff.mp (hEU (hBE hb)) v).mp hv)
  let _ : IsInvariant Bbar W J := ⟨by
    intro r w
    obtain ⟨b,hb,hr⟩ := r.property
    have hh : ((r : action.range) : MulAut W) = action b := congrArg Subtype.val hr.symm
    constructor
    · intro hw
      change ((r : action.range) : MulAut W) w ∈ J
      rw [hh]
      exact hJforward b hb w hw
    · intro hw
      have hh' := hJforward b⁻¹ ((B.subgroupOf P).inv_mem hb)
        (((r : action.range) : MulAut W) w) hw
      rw [hh,map_inv] at hh'
      simpa only [← MulAut.mul_apply,inv_mul_cancel,MulAut.one_apply] using hh'⟩
  have hdecomp := eight_six_residual_fixed_decomposition ctx hcenter hlength hcard
    E geom.group_le hN hW action hformula hkernel
  have hactorImage : Bbar.map action.range.subtype = (B.subgroupOf P).map action := by
    rw [Subgroup.map_map]
    rfl
  have hYImage : (Y.subgroupOf V).map π = commutatorAction Bbar W := by
    have hYcomm : Y = ⁅V,B⁆ := hpacket.1
    rw [hYcomm,←commutatorAction_map_actor_subtype action.range Bbar,hactorImage]
    exact (Subgroup.quotient_conjugation_commutatorAction_eq_image P V Z B
      (stabilizer_le_normalizer_v Γ cp.firstStep) hBP hN action hformula).symm
  have hJcomm : J ≤ commutatorAction Bbar W := by
    rw [←hYImage]
    exact Subgroup.map_mono (Subgroup.subgroupOf_mono V hUY)
  have hfixed : FixedPoints.subgroup Bbar J = ⊥ := by
    apply bot_unique
    intro j hj
    have hw : (j:W) ∈ FixedPoints.subgroup Bbar W := by
      intro b
      exact congrArg Subtype.val (hj b)
    apply Subtype.ext
    exact Subgroup.mem_bot.mp (hdecomp.2.2.1.inf_eq_bot ▸
      (show (j:W) ∈ FixedPoints.subgroup Bbar W ⊓ commutatorAction Bbar W from
        ⟨hw,hJcomm j.property⟩))
  let edgeSylow : Sylow 2 (P ⊓ GAt Γ cp.a : Subgroup G) := default
  let edge := sylowTwoAmbient (P ⊓ GAt Γ cp.a) edgeSylow
  have hdata := edge_sectionThree_data ctx.sectionSeven Γ
    ((mem_neighborhood_iff_adjacent Γ).mpr (Γ.adjacent_symm cp.firstStep_adj)) edgeSylow
  have hkernelRange : pCore 2 P ≤ action.rangeRestrict.ker := by
    intro x hx
    apply MonoidHom.mem_ker.mpr
    apply Subtype.ext
    exact MonoidHom.mem_ker.mp (hkernel hx)
  obtain ⟨p,hp,_hodd,hFp⟩ := SectionThree.pSet_residual_image_is_odd_pGroup
    edge hdata.1 P hdata.2.1 hdata.2.2.2.1 action.rangeRestrict hkernelRange
  let _ : Fact p.Prime := ⟨hp⟩
  have hnative : (twoResidualIn P).subgroupOf P = twoResidualSubgroup P :=
    Subgroup.comap_map_eq_self_of_injective P.subtype_injective _
  have hmono : B ≤ twoResidualIn P := eight_six_residual_mono E P geom.group_le
  have hBple : Bbar ≤ (twoResidualSubgroup P).map action.rangeRestrict := by
    rw [←hnative]
    exact Subgroup.map_mono (Subgroup.subgroupOf_mono P hmono)
  have hBp : IsPGroup p Bbar := hFp.to_le hBple
  have hcongruence := hBp.card_modEq_card_fixedPoints J
  change Nat.ModEq p (Nat.card J) (Nat.card (FixedPoints.subgroup Bbar J)) at hcongruence
  rw [hJcard,hfixed,Subgroup.card_bot] at hcongruence
  have hdiv : p ∣ 3 := hcongruence.symm.dvd'
  have hp3 : p = 3 := ((Nat.dvd_prime Nat.prime_three).mp hdiv).resolve_left hp.ne_one
  have hmap := hFp.map action.range.subtype
  rw [hp3,Subgroup.map_map] at hmap
  rw [hnative]
  exact hmap

end Stellmacher.SectionEight
