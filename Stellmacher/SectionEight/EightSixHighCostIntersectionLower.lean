module
public import Stellmacher.SectionEight.EightSixHighCostResidualCard
public import Stellmacher.SectionEight.EightSixHighCostNextCore
public import Stellmacher.SectionEight.EightSixSelectedOrbitV2

/-!
# The high-cost core intersection has at least thirty-two elements

For the actual selected high-cost configuration in Stellmacher (8.6), the
intersection D of the predecessor and next cores has order at least 32.
The full geometric telescope and elementary D are retained. Neither an
extraspecial model nor the actor quotient rank is assumed.

The proved equality Qnext=Vnext=Y puts D inside Y. Its E-conjugate closure W
is the second selected orbit and has order 128. The inclusions W≤Qa and
W≤Qnext give [W,A]≤D. Conjugating this bound along the supplied residual
witness x, the generation E=A∨A^x shows W=D∨D^x. The first selected orbit U
is E-invariant, has order eight and lies in D, hence lies in D∩D^x. The
identity [Vnext,Qnext]=Znext≤D makes the two factors normalize each other.
Their product-cardinality identity therefore gives |D|²≥8·128.

This is the lower-cardinality part of the calculation between (18) and (19)
in Stellmacher, Journal of Algebra 190 (1997), printed p.45,
refs/files/stellmacher-n-group.pdf. The separate extraspecial bound and
neighbor transport complete the actor-rank computation.
-/

namespace Stellmacher.SectionEight
open Later SectionsFiveToSeven CosetGraphContext SevenSix
universe u
public theorem eight_six_high_cost_intersection_card_lower
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
    (hhigh : ∀ mover : G, mover ∈ VAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.a →
      mover ∉ QAt ctx.Γ ctx.criticalPath.firstStep →
        8 ≤ eightSixCommutatorCost ctx.Γ ctx.criticalPath mover)
    (helementary : IsElementaryAbelianSubgroup 2 D) :
    32 ≤ Nat.card D := by
  classical
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let R := QAt Γ cp.firstStep
  let V := VAt Γ cp.firstStep
  let Z := ZAt Γ cp.firstStep
  let A := VAt Γ previous ⊓ QAt Γ cp.a
  let B := twoResidualIn E
  let Y := ⁅R,B⁆
  let U := conjugateClosure (ZAt Γ cp.a) E
  let W := conjugateClosure D E
  let Dx := D.conjBy geom.x
  have hlen : cp.length = 2 := hlength
  have hVR : V ≤ R := neighbor_join_le_core_of_length_gt_one Γ cp (by omega) _
  have hEV : E ≤ Subgroup.normalizer (V : Set G) :=
    geom.group_le.trans (stabilizer_le_normalizer_v Γ cp.firstStep)
  have hAE : A ≤ E := geom.generated ▸ le_sup_left
  have hselected := eight_six_selected_fixed_core_containment ctx hcenter hquot hlength
    hcard previous D L Q hprev hD hL hQ data E A0 actor geom hcore hedge ha hout hlarge hmin
  have hRV : R = V := eight_six_high_cost_next_core_eq_v ctx hcenter hquot hlength hcard
    previous D L Q hprev data E A0 actor geom hcore hedge hD hL hhigh hselected.1 helementary
  have hpacket := eight_six_selected_residual_decomposition ctx hcenter hquot hlength hcard
    previous D L Q hprev data E A0 actor geom hcore hedge hD hL
  have hYV : Y ≤ V := hpacket.2.2.ge.trans' le_sup_left
  have hUY : U ≤ Y := eight_six_selected_orbit_le_residual_commutator ctx hcenter hquot
    hlength hcard previous D L Q hprev data E A0 actor geom hcore hedge hD hL
  have hseedU : ZAt Γ cp.a ≤ U := by
    intro z hz
    exact Subgroup.subset_closure ⟨(1:E),⟨z,hz⟩,by simp⟩
  have hZU : Z ≤ U := (eight_six_first_step_fixed_line_local ctx hcenter hcard).2.trans hseedU
  have hfixed : R ⊓ Subgroup.centralizer (B : Set G) = Z :=
    eight_six_selected_fixed_core_eq_next_center ctx hcenter hquot hlength hcard
      previous D L Q hprev data E A0 actor geom hcore hedge hD hL hhigh hselected.1
  have hVY : V = Y := by
    apply le_antisymm ?_ hYV
    have hspan : V = Y ⊔ (V ⊓ Subgroup.centralizer (B : Set G)) := hpacket.2.2
    rw [hspan]
    exact sup_le le_rfl (((inf_le_inf hVR le_rfl).trans hfixed.le).trans (hZU.trans hUY))
  have hDY : D ≤ Y := ((hD ▸ inf_le_right).trans hRV.le).trans hVY.le
  have hUD : U ≤ D := eight_six_selected_orbit_le_intersection ctx hcenter hquot
    hlength hcard previous D L Q hprev data E A0 actor geom hcore hedge hD hL hhigh
  have hZD : Z ≤ D := hZU.trans hUD
  have hV2data := eight_six_selected_orbit_v2_support ctx hcenter hquot hlength hcard
    previous D L Q hprev data E A0 actor geom hcore hedge hD hL hhigh hlarge hselected.2
  have hYD : Y ⊓ D = D := inf_eq_right.mpr hDY
  have hWcore : W ≤ QAt Γ cp.a := by
    have hh := hV2data.1
    rw [hYD] at hh
    exact hh
  have hWcount : Nat.card Y = 4 * Nat.card W := by
    have hh := hV2data.2
    rw [hYD] at hh
    exact hh
  have hYcard : Nat.card Y = 512 := (eight_six_high_cost_residual_card ctx hcenter hquot
    hlength hcard previous D L Q hprev data E A0 actor geom hcore hedge hD hL
    ha hout hlarge hmin hQ hhigh).2
  have hWcard : Nat.card W = 128 := by omega
  have hDW : D ≤ W := by
    intro d hd
    exact Subgroup.subset_closure ⟨(1:E),⟨d,hd⟩,by simp⟩
  have hENW : E ≤ Subgroup.normalizer (W : Set G) := eight_six_conjugate_closure_normalizer _ _
  have hWV : W ≤ V := eight_six_conjugate_closure_le D E V (hDY.trans hYV) hEV
  have hQaPrev : QAt Γ cp.a ≤ GAt Γ previous :=
    ((lemma_seven_three ctx.sectionSeven Γ).sylow_and_core cp.a previous hprev.1 default).2.2
  have hWcomm : ⁅W,A⁆ ≤ D := by
    rw [hD]
    apply le_inf
    · exact (Subgroup.commutator_mono le_rfl
        (inf_le_left.trans (neighbor_join_le_core_of_length_gt_one Γ cp (by omega) previous))).trans
        (Subgroup.le_normalizer_iff_commutator_le_right.mp
          ((hWcore.trans hQaPrev).trans (stabilizer_le_normalizer_q Γ previous)))
    · exact (Subgroup.commutator_mono (hWV.trans hVR) le_rfl).trans
        (Subgroup.le_normalizer_iff_commutator_le_left.mp
          ((hAE.trans geom.group_le).trans (stabilizer_le_normalizer_q Γ cp.firstStep)))
  have hxE : geom.x ∈ E := twoResidualIn_le E geom.residual_mem
  have hWmap : W.map (MulAut.conj geom.x).toMonoidHom = W :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (hENW hxE)
  have hDxW : Dx ≤ W := by
    have hh := Subgroup.map_mono (f := (MulAut.conj geom.x).toMonoidHom) hDW
    rw [hWmap] at hh
    exact hh
  have hWcommx : ⁅W,A.conjBy geom.x⁆ ≤ Dx := by
    have hh := Subgroup.map_mono (f := (MulAut.conj geom.x).toMonoidHom) hWcomm
    rw [Subgroup.map_commutator,hWmap] at hh
    exact hh
  have hjoinW : D ⊔ Dx ≤ W := sup_le hDW hDxW
  have hEjoin : E ≤ Subgroup.normalizer ((D ⊔ Dx : Subgroup G) : Set G) := by
    rw [geom.generated]
    apply sup_le
    · exact Subgroup.le_normalizer_iff_commutator_le_left.mpr
        ((Subgroup.commutator_mono hjoinW le_rfl).trans (hWcomm.trans le_sup_left))
    · exact Subgroup.le_normalizer_iff_commutator_le_left.mpr
        ((Subgroup.commutator_mono hjoinW le_rfl).trans (hWcommx.trans le_sup_right))
  have hWeq : W = D ⊔ Dx := le_antisymm
    (eight_six_conjugate_closure_le D E (D ⊔ Dx) le_sup_left hEjoin) hjoinW
  have hUmap : U.map (MulAut.conj geom.x).toMonoidHom = U :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp
      (eight_six_conjugate_closure_normalizer _ _ hxE)
  have hUDx : U ≤ Dx := by
    have hh := Subgroup.map_mono (f := (MulAut.conj geom.x).toMonoidHom) hUD
    rw [hUmap] at hh
    exact hh
  have hDxNormD : Dx ≤ Subgroup.normalizer (D : Set G) :=
    Subgroup.le_normalizer_iff_commutator_le_left.mpr
      (((Subgroup.commutator_mono (hDY.trans hYV) (hDxW.trans (hWV.trans hVR))).trans_eq
        data.first_commutator).trans hZD)
  have hprod := Subgroup.card_mul_eq_card_inf_mul_card_sup_of_normalizes D Dx hDxNormD
  have hDxCard : Nat.card Dx = Nat.card D := Subgroup.card_map_of_injective (MulAut.conj geom.x).injective
  have hUcard : Nat.card U = 8 := eight_six_selected_orbit_card_eight ctx hcenter hquot
    hlength hcard previous D L Q hprev data E A0 actor geom hcore hedge hD hL
  have hbound := Subgroup.card_le_of_le (le_inf hUD hUDx)
  rw [hUcard] at hbound
  rw [hDxCard,←hWeq,hWcard] at hprod
  nlinarith

end Stellmacher.SectionEight
