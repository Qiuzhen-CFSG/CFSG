module
public import Stellmacher.SectionEight.EightSixCostFourResidualCard
public import Stellmacher.SectionEight.EightSixResidualFixedQuotient
public import Stellmacher.SectionEight.EightSixSelectedFixedCoreContainment
public import Stellmacher.SectionEight.EightSixSelectedFixedCoreIntersection
public import Stellmacher.SectionEight.EightSixSelectedOrbitCommutator
public import Theory.GroupAction.SixteenCentralInvolutionDisplacement

/-!
# The coatom commutator and quadratic action in the cost-four branch

For the actual selected minimum-cost actor in the large-index configuration,
let Y=[Qnext,O²(E)], let U be the E-orbit closure of the initial center, and
let Z be the next central line. If the selected cost is four, the coatom
commutator [Y,A0] joined with Z is exactly U, and A0 acts quadratically on
Vnext/Z. These are the coatom assertions in the cost-four paragraph of
Stellmacher (8.6), Journal of Algebra 190 (1997), printed p.44.

Use the literal residual-fixed quotient Vnext/C of order sixteen. The image
of U has order four because U has order eight and Y intersects C in Z.
Each coatom actor is an involution on this quotient through the actual
Frattini containment, commutes with the residual image, and fixes U's image.
The elementary sixteen-plane theorem makes its displacement trivial or the
whole plane. The identity Y intersect C=Z reflects this bound back to U.

If all coatom displacements vanished modulo Z, an actual element of Y
outside the initial core would force A0 into D by the cubic subgroup-forcing
lemma. This contradicts the coatom cardinality and large-index assumption,
so the full plane occurs and [Y,A0]Z=U. Finally source (11) controls the fixed
part C, which lies in the initial core by source (14). Expanding the proved
product Vnext=YC gives [Vnext,A0]≤U and hence the quadratic conclusion.
All quotient normality, action and invariant-subgroup witnesses are retained.
-/

namespace Stellmacher.SectionEight
open Later SectionsFiveToSeven CosetGraphContext SevenSix
open scoped commutatorElement IsMulCommutative
universe u
public theorem eight_six_cost_four_coatom_commutator
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
    (hcost : eightSixCommutatorCost ctx.Γ ctx.criticalPath actor = 4) :
    let V := VAt ctx.Γ ctx.criticalPath.firstStep
    let Z := ZAt ctx.Γ ctx.criticalPath.firstStep
    let Y := ⁅QAt ctx.Γ ctx.criticalPath.firstStep,twoResidualIn E⁆
    let U := conjugateClosure (ZAt ctx.Γ ctx.criticalPath.a) E
    ⁅Y,A0⁆ ⊔ Z = U ∧ ⁅⁅V,A0⁆,A0⁆ ≤ Z := by
  classical
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let P := GAt Γ cp.firstStep
  let R := QAt Γ cp.firstStep
  let V := VAt Γ cp.firstStep
  let Z := ZAt Γ cp.firstStep
  let A := VAt Γ previous ⊓ QAt Γ cp.a
  let B := twoResidualIn E
  let Y := ⁅R,B⁆
  let C := V ⊓ Subgroup.centralizer (B : Set G)
  let U := conjugateClosure (ZAt Γ cp.a) E
  have hAE : A ≤ E := geom.generated ▸ le_sup_left
  have hA0A : A0 ≤ A := geom.coatom_eq ▸ inf_le_left
  have hA0E : A0 ≤ E := hA0A.trans hAE
  have hEP : E ≤ P := geom.group_le
  have hEV : E ≤ Subgroup.normalizer (V : Set G) :=
    hEP.trans (stabilizer_le_normalizer_v Γ cp.firstStep)
  have hEU : E ≤ Subgroup.normalizer (U : Set G) :=
    eight_six_conjugate_closure_normalizer _ _
  have hVR : V ≤ R := neighbor_join_le_core_of_length_gt_one Γ cp (by exact hlength ▸ by decide) _
  have hEY : E ≤ Subgroup.normalizer (Y : Set G) :=
    le_normalizer_commutator_of_le_normalizers'
      (hEP.trans (stabilizer_le_normalizer_q Γ cp.firstStep))
      ((Subgroup.normal_subgroupOf_iff_le_normalizer (twoResidualIn_le E)).mp
        (twoResidualIn_normal E))
  have hpacket := eight_six_selected_residual_decomposition ctx hcenter hquot hlength hcard
    previous D L Q hprev data E A0 actor geom hcore hedge hD hL
  have hYC : Y ⊓ C = Z := hpacket.2.1
  have hsplit : V = Y ⊔ C := hpacket.2.2
  have hYV : Y ≤ V := hsplit.ge.trans' le_sup_left
  have hUY : U ≤ Y := eight_six_selected_orbit_le_residual_commutator ctx hcenter hquot
    hlength hcard previous D L Q hprev data E A0 actor geom hcore hedge hD hL
  have hUV : U ≤ V := hUY.trans hYV
  have hZaU : ZAt Γ cp.a ≤ U := by
    intro z hz
    exact Subgroup.subset_closure ⟨(1:E),⟨z,hz⟩,by simp⟩
  have hZU : Z ≤ U := (eight_six_first_step_fixed_line_local ctx hcenter hcard).2.trans hZaU
  have hZY : Z ≤ Y := hZU.trans hUY
  have hZC : Z ≤ C := hYC.ge.trans inf_le_right
  have hZcard : Nat.card Z = 2 := (eight_six_first_step_fixed_line_local ctx hcenter hcard).1
  have hUcard : Nat.card U = 8 := eight_six_selected_orbit_card_eight ctx hcenter hquot hlength
    hcard previous D L Q hprev data E A0 actor geom hcore hedge hD hL
  have hUC : U ⊓ C = Z := le_antisymm
    ((inf_le_inf hUY le_rfl).trans hYC.le) (le_inf hZU hZC)
  have hUA0 : ⁅U,A0⁆ ≤ Z := eight_six_selected_orbit_commutator_le ctx hcenter hcard
    E A0 hEP (hA0A.trans inf_le_right) geom.coatom_commutator
  have hfixed := (eight_six_selected_fixed_core_containment ctx hcenter hquot hlength hcard
    previous D L Q hprev hD hL hQ data E A0 actor geom hcore hedge ha hout hlarge hmin).1
  have hCcore : C ≤ QAt Γ cp.a := ((inf_le_inf hVR le_rfl).trans hfixed)
  have hCA0 : ⁅C,A0⁆ ≤ Z :=
    (Subgroup.commutator_mono
      (le_inf (inf_le_inf hVR le_rfl) hCcore) hA0A).trans
      ((eight_six_selected_fixed_core_commutator_bounds ctx hcenter hquot hlength hcard
        previous D L Q hprev hD hL data E A0 actor geom hedge).1)
  obtain ⟨hN,hW,action,haction,hkernel,hfixedW⟩ := eight_six_residual_fixed_quotient_module
    ctx hcenter hlength hcard data.first_commutator E hEP
  let _ := hN
  let _ := hW
  let W := V ⧸ C.subgroupOf V
  let π : V →* W := QuotientGroup.mk' (C.subgroupOf V)
  let J := (U.subgroupOf V).map π
  let F := (twoResidualAmbient (⊤ : Subgroup E)).map action
  have hWcard : Nat.card W = 16 := by
    have hcount := Subgroup.card_eq_card_quotient_mul_card_subgroup (C.subgroupOf V)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (show C ≤ V from inf_le_left)).toEquiv]
      at hcount
    have hc := eight_six_cost_four_fixed_quotient_card ctx hcenter hquot hlength hcard
      previous D L Q hprev data E A0 actor geom hcore hedge hD hL ha hout hlarge hmin hQ hcost
    change Nat.card V = 16 * Nat.card C at hc
    change Nat.card V = Nat.card W * Nat.card C at hcount
    have hpos : 0 < Nat.card C := Nat.card_pos
    nlinarith
  have hJcard : Nat.card J = 4 := by
    change Nat.card ((U.subgroupOf V).map (QuotientGroup.mk' (C.subgroupOf V))) = 4
    rw [← Subgroup.relIndex_ker, QuotientGroup.ker_mk', Subgroup.relIndex_subgroupOf hUV]
    have hsub : C.subgroupOf U = Z.subgroupOf U := by
      ext x
      constructor
      · intro hx
        exact hUC.le ⟨x.property,hx⟩
      · intro hx
        exact hZC hx
    have hcount := (C.subgroupOf U).index_mul_card
    rw [hsub, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZU).toEquiv,hZcard,hUcard] at hcount
    change Z.relIndex U * 2 = 8 at hcount
    change (C.subgroupOf U).index = 4
    rw [hsub]
    change Z.relIndex U = 4
    omega
  have hJforward (e : E) (w : W) (hw : w ∈ J) : action e w ∈ J := by
    obtain ⟨v,hv,rfl⟩ := hw
    rw [haction]
    exact Subgroup.mem_map_of_mem π
      ((Subgroup.mem_normalizer_iff.mp (hEU e.property) v).mp hv)
  let _ : IsInvariant F W J := ⟨by
    intro r w
    obtain ⟨e,he,hr⟩ := r.property
    have hh : (r : MulAut W) = action e := hr.symm
    constructor
    · intro hw
      change (r : MulAut W) w ∈ J
      rw [hh]
      exact hJforward e w hw
    · intro hw
      have hh' := hJforward e⁻¹ ((r : MulAut W) w) hw
      change w ∈ J
      rw [hh,map_inv] at hh'
      simpa only [← MulAut.mul_apply, inv_mul_cancel, MulAut.one_apply] using hh'⟩
  have hYA0Y : ⁅Y,A0⁆ ≤ Y :=
    Subgroup.le_normalizer_iff_commutator_le_left.mp (hA0E.trans hEY)
  have hVY : V ≤ Subgroup.normalizer (Y : Set G) :=
    hVR.trans (Subgroup.normalizer_commutator_ge_left R B)
  have hVU : V ≤ Subgroup.normalizer (U : Set G) :=
    Subgroup.le_normalizer_iff_commutator_le_left.mpr
      (((Subgroup.commutator_mono hUV hVR).trans_eq data.first_commutator).trans hZU)
  have hwhole (M : Subgroup G) (hMN : V ≤ Subgroup.normalizer (M : Set G))
      (hYM : ⁅Y,A0⁆ ≤ M) (hCM : ⁅C,A0⁆ ≤ M) : ⁅V,A0⁆ ≤ M := by
    let _ : (Y.subgroupOf V).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hYV).mpr hVY
    apply Subgroup.commutator_le.mpr
    intro v hv b hb
    have hmem : (⟨v,hv⟩ : V) ∈ Y.subgroupOf V ⊔ C.subgroupOf V := by
      rw [← Subgroup.subgroupOf_sup hYV (show C ≤ V from inf_le_left),← hsplit]
      exact hv
    obtain ⟨y,hy,c,hc,hprod⟩ := Subgroup.mem_sup_of_normal_left.mp hmem
    have heq := congrArg Subtype.val hprod
    change (y:G)*(c:G) = v at heq
    rw [← heq,commutatorElement_mul_left_eq_conj_mul]
    exact M.mul_mem
      ((Subgroup.mem_normalizer_iff.mp (hMN y.property) _).mp
        (hCM (Subgroup.commutator_mem_commutator hc hb)))
      (hYM (Subgroup.commutator_mem_commutator hy hb))
  have hreflect (M : Subgroup G) (hMY : M ≤ Y) (hZM : Z ≤ M)
      (v : V) (hv : (v:G) ∈ Y)
      (himage : π v ∈ (M.subgroupOf V).map π) : (v:G) ∈ M := by
    obtain ⟨m,hm,heq⟩ := himage
    have hdiff : v/m ∈ C.subgroupOf V := QuotientGroup.eq_iff_div_mem.mp heq.symm
    change (v:G)/(m:G) ∈ C at hdiff
    have hz : (v:G)/(m:G) ∈ Z := hYC.le ⟨Y.div_mem hv (hMY hm),hdiff⟩
    have hv' := M.mul_mem (hZM hz) hm
    change (v:G)/(m:G)*(m:G) ∈ M at hv'
    simpa only [div_mul_cancel] using hv'
  have hnonzero : ¬ ⁅Y,A0⁆ ≤ Z := by
    intro hzero
    have hyout := (eight_six_selected_fixed_core_containment ctx hcenter hquot hlength hcard
      previous D L Q hprev hD hL hQ data E A0 actor geom hcore hedge ha hout hlarge hmin).2
    obtain ⟨y,hy,hyout⟩ := SetLike.not_le_iff_exists.mp hyout
    have hZD : Z ≤ D := (eight_six_first_step_fixed_line_local ctx hcenter hcard).2.trans
      (eight_six_initial_center_le_intersection_of_length_two Γ cp hlength previous hprev.1 D hD)
    have hAprev : A ≤ QAt Γ previous := inf_le_left.trans
      (neighbor_join_le_core_of_length_gt_one Γ cp (by exact hlength ▸ by decide) previous)
    have hforce : A0 ≤ D := eight_six_cubic_subgroup_forcing ctx.sectionSeven Γ cp.a cp.firstStep
      previous hquot ((mem_neighborhood_iff_adjacent Γ).mpr cp.firstStep_adj) hprev.1 hprev.2
      D hD data.intersection_normal y (hVR (hYV hy)) hyout A0 (hA0A.trans hAprev) (by
        rw [Subgroup.commutator_comm]
        exact (Subgroup.commutator_mono (Subgroup.zpowers_le.mpr hy) le_rfl).trans (hzero.trans hZD))
    have hbound := Subgroup.card_le_of_le (le_inf hA0A hforce)
    have hcoatom : Nat.card A = 2 * Nat.card A0 := geom.coatom_card
    have hpos : 0 < Nat.card A0 := Nat.card_pos
    change Nat.card A0 ≤ Nat.card (A ⊓ D : Subgroup G) at hbound
    change 4 * Nat.card (A ⊓ D : Subgroup G) ≤ Nat.card A at hlarge
    omega
  have hA0central : (A0.subgroupOf E).map action ≤
      Subgroup.centralizer (action.range : Set (MulAut W)) := by
    rintro mover ⟨b,hb,rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro image ⟨e,rfl⟩
    have hk : ⁅e,b⁆ ∈ action.ker := hkernel
      (geom.coatom_commutator (Subgroup.commutator_mem_commutator e.property hb))
    have hone : ⁅action e,action b⁆ = 1 := by
      rw [← map_commutatorElement]
      exact MonoidHom.mem_ker.mp hk
    exact commutatorElement_eq_one_iff_mul_comm.mp hone
  have hAQ : A ≤ Q := data.core_generation ▸ le_sup_of_le_left le_sup_left
  have hQtwo : IsPGroup 2 Q := by
    rw [hQ,twoCoreIn]
    exact (pCore_isPGroup (p := 2)).map _
  let _ : Fact (IsPGroup 2 Q) := ⟨hQtwo⟩
  have hbsquare (b : E) (hb : (b:G) ∈ A0) : (action b)^2 = 1 := by
    have hpowD : (b:G)^2 ∈ D := data.core_frattini_le
      (Subgroup.mem_map.mpr ⟨(⟨b,hAQ (hA0A hb)⟩:Q)^2,
        pth_power_mem_frattini_of_isPGroup (p := 2) (⟨b,hAQ (hA0A hb)⟩:Q),rfl⟩)
    rw [← map_pow]
    exact MonoidHom.mem_ker.mp (hkernel ((hD ▸ hpowD).2))
  have hbfix (b : E) (hb : (b:G) ∈ A0) : ∀ j ∈ J, action b j = j := by
    rintro j ⟨u,hu,rfl⟩
    rw [haction]
    apply QuotientGroup.eq_iff_div_mem.mpr
    change (b:G)*(u:G)*(b:G)⁻¹/(u:G) ∈ C
    have hh : ⁅(b:G),(u:G)⁆ ∈ Z := (Subgroup.commutator_comm U A0 ▸ hUA0)
      (Subgroup.commutator_mem_commutator hb hu)
    simpa only [commutatorElement_def,div_eq_mul_inv] using hZC hh
  have hFle : F ≤ action.range := by
    rintro r ⟨e,_,rfl⟩
    exact ⟨e,rfl⟩
  have hplane (b : E) (hb : (b:G) ∈ A0) :
      commutatorAction (Subgroup.zpowers (action b)) W = ⊥ ∨
      commutatorAction (Subgroup.zpowers (action b)) W = J :=
    commutatorAction_eq_bot_or_four_plane_of_central_involution F J hWcard hJcard hfixedW
      (action b) (hbsquare b hb)
      (Subgroup.centralizer_le hFle (hA0central (Subgroup.mem_map_of_mem action hb)))
      (hbfix b hb)
  have hdeltaImage (b : E) :
      commutatorAction (Subgroup.zpowers (action b)) W =
        ((⁅V,Subgroup.zpowers (b:G)⁆).subgroupOf V).map π := by
    have hcyclic : (Subgroup.zpowers (b:G)).subgroupOf E = Subgroup.zpowers b := by
      apply Subgroup.map_injective E.subtype_injective
      rw [Subgroup.map_subgroupOf_eq_of_le (Subgroup.zpowers_le.mpr b.property),
        MonoidHom.map_zpowers]
      rfl
    have hh := Subgroup.quotient_conjugation_commutatorAction_eq_image E V C
      (Subgroup.zpowers (b:G)) hEV (Subgroup.zpowers_le.mpr b.property) hN action haction
    rw [hcyclic,MonoidHom.map_zpowers] at hh
    exact hh
  have hbound : ⁅Y,A0⁆ ≤ U := by
    apply Subgroup.commutator_le.mpr
    intro y hy b hb
    let e : E := ⟨b,hA0E hb⟩
    have hcY := hYA0Y (Subgroup.commutator_mem_commutator hy hb)
    let c : V := ⟨⁅y,b⁆,hYV hcY⟩
    apply hreflect U hUY hZU c hcY
    have hdeltaLe : commutatorAction (Subgroup.zpowers (action e)) W ≤ J := by
      rcases hplane e hb with hbot | hfull
      · exact hbot ▸ bot_le
      · exact hfull.le
    rw [hdeltaImage] at hdeltaLe
    apply hdeltaLe
    exact Subgroup.mem_map_of_mem π
      (show c ∈ (⁅V,Subgroup.zpowers (e:G)⁆).subgroupOf V from
        Subgroup.commutator_mem_commutator (hYV hy) (Subgroup.mem_zpowers b))
  have hVA0U : ⁅V,A0⁆ ≤ U := hwhole U hVU hbound (hCA0.trans hZU)
  have hex : ∃ y ∈ Y, ∃ b ∈ A0, ⁅y,b⁆ ∉ Z := by
    by_contra! hnone
    exact hnonzero (Subgroup.commutator_le.mpr hnone)
  obtain ⟨y,hy,b,hb,houtZ⟩ := hex
  let e : E := ⟨b,hA0E hb⟩
  have hcY := hYA0Y (Subgroup.commutator_mem_commutator hy hb)
  let c : V := ⟨⁅y,b⁆,hYV hcY⟩
  have hcImage : π c ∈ commutatorAction (Subgroup.zpowers (action e)) W := by
    rw [hdeltaImage]
    exact Subgroup.mem_map_of_mem π
      (show c ∈ (⁅V,Subgroup.zpowers (e:G)⁆).subgroupOf V from
        Subgroup.commutator_mem_commutator (hYV hy) (Subgroup.mem_zpowers b))
  have hdeltaFull : commutatorAction (Subgroup.zpowers (action e)) W = J := by
    rcases hplane e hb with hbot | hfull
    · have hone : π c = 1 := Subgroup.mem_bot.mp (hbot ▸ hcImage)
      have hcC : c ∈ C.subgroupOf V := (QuotientGroup.eq_one_iff _).mp hone
      exact False.elim (houtZ (hYC.le ⟨hcY,hcC⟩))
    · exact hfull
  let M := ⁅Y,A0⁆ ⊔ Z
  have hMY : M ≤ Y := sup_le hYA0Y hZY
  have hMU : M ≤ U := sup_le hbound hZU
  have hVM : V ≤ Subgroup.normalizer (M : Set G) :=
    Subgroup.le_normalizer_iff_commutator_le_left.mpr
      (((Subgroup.commutator_mono (hMU.trans hUV) hVR).trans_eq data.first_commutator).trans
        le_sup_right)
  have hVAM : ⁅V,A0⁆ ≤ M := hwhole M hVM le_sup_left (hCA0.trans le_sup_right)
  have hJM : J ≤ (M.subgroupOf V).map π := by
    rw [← hdeltaFull,hdeltaImage]
    apply Subgroup.map_mono
    intro v hv
    exact hVAM ((Subgroup.commutator_mono le_rfl (Subgroup.zpowers_le.mpr hb)) hv)
  have hUM : U ≤ M := by
    intro u hu
    exact hreflect M hMY le_sup_right ⟨u,hUV hu⟩ (hUY hu)
      (hJM (Subgroup.mem_map_of_mem π hu))
  exact ⟨le_antisymm hMU hUM,(Subgroup.commutator_mono hVA0U le_rfl).trans hUA0⟩

end Stellmacher.SectionEight
