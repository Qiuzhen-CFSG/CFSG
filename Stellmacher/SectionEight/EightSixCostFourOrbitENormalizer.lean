module
public import Stellmacher.SectionEight.EightSixCostFourModuleQuaternion
public import Stellmacher.SectionEight.EightSixCostFourCentralQuotient
public import Stellmacher.SectionEight.EightSixSelectedOrbitFirstCommutator
public import Stellmacher.SectionEight.EightSixNextResidualCoreAction
public import Theory.GroupTheory.CommutatorPreimage

/-!
# The selected group normalizes the native cost-four cubic support

Retain the original selected cost-four configuration and let U be the
E-conjugate closure of the initial center. Any actual subgroup W containing
U, contained in the initial core Q, and centralizing U is normalized by E.
No model action, additional residual-core equality, or faithful replacement
of the selected E image is assumed.

The selected coatom A0 and next core R centralize U modulo the next center Z.
The first commutator identity shows that the whole actor group A does not.
Its index-two coatom therefore identifies the kernel on U/Z, putting W in
K=A0R. This K is an E-normal two-subgroup. The actor/coatom identities give
[K,E]≤R and [R,E]≤Vnext. Residual commutator idempotence then improves the
O²(E)-part of [K,E] to Vnext; the A-part lies there as well. Since E=O²(E)A,
[W,E]≤Vnext. Normalization of U also puts this commutator in C_G(U), and the
proved equality C_Vnext(U)=U finally gives [W,E]≤U≤W.

Source: Stellmacher, Journal of Algebra 190 (1997), proof of (8.6)(b3),
printed p.44, the implication from [V1,W]=1 to E≤N_G(W). This isolates the
native normalization step needed by the actual cubic-orbit construction.
-/

namespace Stellmacher.SectionEight
open Later SectionsFiveToSeven CosetGraphContext SevenSix
open scoped Pointwise commutatorElement
universe u

private theorem commutator_join_le
    {G : Type u} [Group G] (A B E Z : Subgroup G)
    (hnorm : A⊔B≤Subgroup.normalizer (Z:Set G))
    (hA : ⁅A,E⁆≤Z) (hB : ⁅B,E⁆≤Z) : ⁅A⊔B,E⁆≤Z := by
  have hle : A⊔B≤Subgroup.commutatorPreimage (A⊔B) E Z :=
    sup_le (Subgroup.le_commutatorPreimage le_sup_left hA)
      (Subgroup.le_commutatorPreimage le_sup_right hB)
  exact (Subgroup.commutator_mono hle le_rfl).trans
    (Subgroup.commutator_commutatorPreimage_le _ _ _ hnorm)

public theorem eight_six_cost_four_orbit_e_normalizer
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
    (W : Subgroup G)
    (hUW : conjugateClosure (ZAt ctx.Γ ctx.criticalPath.a) E ≤ W)
    (hWQ : W≤Q)
    (hcomm : ⁅conjugateClosure (ZAt ctx.Γ ctx.criticalPath.a) E,W⁆=⊥) :
    E≤Subgroup.normalizer (W:Set G) := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  have hlen : cp.length=2 := hlength
  let P := GAt Γ cp.firstStep
  let R := QAt Γ cp.firstStep
  let V := VAt Γ cp.firstStep
  let Z := ZAt Γ cp.firstStep
  let Za := ZAt Γ cp.a
  let U := conjugateClosure Za E
  let Act := VAt Γ previous⊓QAt Γ cp.a
  have hEP : E≤P := geom.group_le
  have hAE : Act≤E := geom.generated ▸ le_sup_left
  have hAP : Act≤P := hAE.trans hEP
  have hA0A : A0≤Act := geom.coatom_eq ▸ inf_le_left
  have hA0P : A0≤P := hA0A.trans hAP
  have hRP : R≤P := by
    change Γ.twoCoreAt cp.firstStep≤Γ.vertexStabilizer cp.firstStep
    rw [Γ.twoCoreAt_def]
    exact twoCoreIn_le _
  have hVR : V≤R := neighbor_join_le_core_of_length_gt_one Γ cp (by omega) _
  have hPR : P≤Subgroup.normalizer (R:Set G) := stabilizer_le_normalizer_q Γ _
  have hPV : P≤Subgroup.normalizer (V:Set G) := stabilizer_le_normalizer_v Γ _
  have hPZ : P≤Subgroup.normalizer (Z:Set G) := stabilizer_le_normalizer_z Γ _
  have hUN : E≤Subgroup.normalizer (U:Set G) := eight_six_conjugate_closure_normalizer _ _
  have hZaV : Za≤V := (lemma_seven_four ctx.sectionSeven Γ cp).first_containment.1
  have hUV : U≤V := eight_six_conjugate_closure_le Za E V hZaV (hEP.trans hPV)
  have hline := eight_six_first_step_fixed_line_local ctx hcenter hcard
  have hnotZa : ¬Za≤Z := by
    intro hle
    have hh := Subgroup.card_le_of_le hle
    have hc : Nat.card Za=4 := hcard
    have hz : Nat.card Z=2 := hline.1
    rw [hc,hz] at hh
    omega
  have hUZ : ⁅U,R⁆≤Z := (Subgroup.commutator_mono hUV le_rfl).trans_eq data.first_commutator
  have hU0 : ⁅U,A0⁆≤Z := eight_six_selected_orbit_commutator_le ctx hcenter hcard
    E A0 geom.group_le (hA0A.trans inf_le_right) geom.coatom_commutator
  have hUA : ⁅U,Act⁆⊔Z=Za := eight_six_selected_orbit_commutator_sup_line
    ctx hcenter hquot hlength hcard previous D L Q hprev data E A0 actor geom hcore hedge hD hL
  have hQA : Q≤Act⊔R := by
    rw [data.core_generation]
    exact sup_le (sup_le le_sup_left (inf_le_left.trans (hVR.trans le_sup_right)))
      ((hD ▸ inf_le_right).trans le_sup_right)
  let F := Subgroup.commutatorPreimage (Act⊔R) U Z
  have hFcomm : ⁅F,U⁆≤Z := Subgroup.commutator_commutatorPreimage_le _ _ _
    ((sup_le hAP hRP).trans hPZ)
  have hA0F : A0≤F := Subgroup.le_commutatorPreimage (hA0A.trans le_sup_left)
    (by rwa [Subgroup.commutator_comm])
  have hRF : R≤F := Subgroup.le_commutatorPreimage le_sup_right
    (by rwa [Subgroup.commutator_comm])
  have hAFnot : ¬Act≤F := by
    intro hle
    apply hnotZa
    rw [←hUA]
    exact sup_le (by rw [Subgroup.commutator_comm]; exact
      (Subgroup.commutator_mono hle le_rfl).trans hFcomm) le_rfl
  have hindex : (A0.subgroupOf Act).index=2 := by
    have hh := (A0.subgroupOf Act).index_mul_card
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hA0A).toEquiv] at hh
    have hc : Nat.card Act=2*Nat.card A0 := geom.coatom_card
    have hp : 0<Nat.card A0 := Nat.card_pos
    nlinarith
  have hAF : Act⊓F≤A0 := by
    rintro a ⟨ha,haf⟩
    by_contra ha0
    apply hAFnot
    intro b hb
    by_cases hb0 : b∈A0
    · exact hA0F hb0
    have hk : a⁻¹*b∈A0 := by
      have hh := (A0.subgroupOf Act).mul_mem_iff_of_index_two hindex
        (a:=⟨a⁻¹,Act.inv_mem ha⟩) (b:=⟨b,hb⟩)
      exact hh.mpr (by simp only [Subgroup.mem_subgroupOf,Subgroup.inv_mem_iff,ha0,hb0])
    simpa only [mul_inv_cancel_left] using F.mul_mem haf (hA0F hk)
  have hWF : W≤F := Subgroup.le_commutatorPreimage (hWQ.trans hQA)
    (by rw [Subgroup.commutator_comm,hcomm]; exact bot_le)
  let K := A0⊔R
  have hWK : W≤K := by
    intro w hw
    have hh : w∈(Act:Set G)*(R:Set G) := by
      rw [←Subgroup.coe_mul_of_left_le_normalizer_right Act R (hAP.trans hPR)]
      exact hQA (hWQ hw)
    obtain ⟨a,ha,r,hr,rfl⟩ := hh
    have haf : a∈F := by
      simpa only [mul_inv_cancel_right] using F.mul_mem (hWF hw) (F.inv_mem (hRF hr))
    exact K.mul_mem (Subgroup.mem_sup_left (hAF ⟨ha,haf⟩)) (Subgroup.mem_sup_right hr)
  have hRA : ⁅R,Act⁆≤V := eight_six_next_core_actor_commutator_le_v
    ctx hcenter hlength previous D L Q hprev.1 hD hL data
  have hxE : geom.x∈E := twoResidualIn_le E geom.residual_mem
  have hRx : R.map (MulAut.conj geom.x).toMonoidHom=R :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (hPR (hEP hxE))
  have hVx : V.map (MulAut.conj geom.x).toMonoidHom=V :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (hPV (hEP hxE))
  have hRAx : ⁅R,Act.conjBy geom.x⁆≤V := by
    have hh := Subgroup.map_mono (f:=(MulAut.conj geom.x).toMonoidHom) hRA
    rw [Subgroup.map_commutator,hRx,hVx] at hh
    exact hh
  have hRE : ⁅R,E⁆≤V := by
    rw [Subgroup.commutator_comm,geom.generated]
    apply commutator_join_le Act (Act.conjBy geom.x) R V
    · rw [←geom.generated]; exact hEP.trans hPV
    · rwa [Subgroup.commutator_comm]
    · rwa [Subgroup.commutator_comm]
  have hKP : K≤P := sup_le hA0P hRP
  have hKER : ⁅K,E⁆≤R := commutator_join_le A0 R E R (hKP.trans hPR)
    (by rw [Subgroup.commutator_comm]; exact geom.coatom_commutator) (hRE.trans hVR)
  have hENK : E≤Subgroup.normalizer (K:Set G) :=
    Subgroup.le_normalizer_iff_commutator_le_left.mpr (hKER.trans le_sup_right)
  have hRtwo : IsPGroup 2 R := by
    change IsPGroup 2 (Γ.twoCoreAt cp.firstStep)
    rw [Γ.twoCoreAt_def]
    exact (pCore_isPGroup (p:=2)).map _
  have hA0two : IsPGroup 2 A0 :=
    (((pCore_isPGroup (p:=2) (G:=GAt Γ cp.a)).map (GAt Γ cp.a).subtype).to_le
      ((hA0A.trans inf_le_right).trans_eq (Γ.twoCoreAt_def cp.a)))
  have hKtwo : IsPGroup 2 K := by
    change IsPGroup 2 (A0⊔R : Subgroup G)
    rw [sup_comm]
    exact hRtwo.to_sup_of_normal_left' hA0two (hA0P.trans hPR)
  let B := twoResidualIn E
  have hBE : B≤E := twoResidualIn_le E
  have hidem : ⁅⁅K,B⁆,B⁆=⁅K,B⁆ := commutator_twoResidualAmbient_idempotent K E hKtwo hENK
  have hKB : ⁅K,B⁆≤V := hidem.symm.le.trans
    ((Subgroup.commutator_mono ((Subgroup.commutator_mono le_rfl hBE).trans hKER) hBE).trans hRE)
  have hAA : ⁅Act,Act⁆≤Za := (Subgroup.commutator_mono inf_le_left inf_le_left).trans
    (eight_six_neighbor_join_bounds_local ctx hcenter hlength hcard Za
      (stabilizer_le_normalizer_z Γ cp.a) le_rfl data.first_commutator previous hprev.1).1
  have hKA : ⁅K,Act⁆≤V := commutator_join_le A0 R Act V (hKP.trans hPV)
    (((Subgroup.commutator_mono hA0A le_rfl).trans hAA).trans hZaV) hRA
  have hEgen : E=B⊔Act := by
    apply le_antisymm ?_ (sup_le hBE hAE)
    rw [geom.generated]
    apply sup_le le_sup_right
    rintro x ⟨a,ha,rfl⟩
    change geom.x*a*geom.x⁻¹∈B⊔Act
    exact (B⊔Act).mul_mem ((B⊔Act).mul_mem (Subgroup.mem_sup_left geom.residual_mem)
      (Subgroup.mem_sup_right ha)) ((B⊔Act).inv_mem (Subgroup.mem_sup_left geom.residual_mem))
  have hKE : ⁅K,E⁆≤V := by
    rw [Subgroup.commutator_comm,hEgen]
    apply commutator_join_le B Act K V
    · rw [←hEgen]; exact hEP.trans hPV
    · rwa [Subgroup.commutator_comm]
    · rwa [Subgroup.commutator_comm]
  have hWE : ⁅W,E⁆≤V := (Subgroup.commutator_mono hWK le_rfl).trans hKE
  have hWC : W≤Subgroup.centralizer (U:Set G) :=
    Subgroup.le_centralizer_iff.mp (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm)
  have hEC : E≤Subgroup.normalizer (Subgroup.centralizer (U:Set G):Set G) :=
    hUN.trans ((Subgroup.normal_subgroupOf_iff_le_normalizer
      (Subgroup.centralizer_le_normalizer _)).mp
        (Subgroup.normal_subgroupOf_centralizer_normalizer (U:Set G)))
  have hWEC : ⁅W,E⁆≤Subgroup.centralizer (U:Set G) :=
    (Subgroup.commutator_mono hWC le_rfl).trans
      (Subgroup.le_normalizer_iff_commutator_le_left.mp hEC)
  have hfixed : V⊓Subgroup.centralizer (U:Set G)=U :=
    (eight_six_cost_four_module_quaternion ctx hcenter hquot hlength hcard previous D L Q
      hprev data E A0 actor geom hcore hedge hD hL ha hout hlarge hmin hQ hcost).2
  exact Subgroup.le_normalizer_iff_commutator_le_left.mpr
    (((le_inf hWE hWEC).trans_eq hfixed).trans hUW)

end Stellmacher.SectionEight
