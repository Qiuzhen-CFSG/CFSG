module
public import Stellmacher.SectionNine.NineSixLengthThree
public import Stellmacher.SectionNine.NineSevenTerminalContainedCommutatorBound
public import Theory.GroupTheory.Commutator.BoundedImageKernel
public import Stellmacher.SectionNine.NineSevenModelInputs
public import Theory.GroupTheory.NormalCenterQuotient

/-!
# The zero backward commutator coatom in Stellmacher (9.6)

Assume the actual ambient Section Nine critical path has length greater than
three, the first core quotient is SL₂(2), and the first module has order
sixteen. For a predecessor neighboring the initial vertex, if its module
centralizes the module at offset b−2, there is a subgroup K of index at most
two in the predecessor module whose terminal-module commutator lies in the
actual mutual endpoint-module commutator R. No coatom data are assumed.

The full module-centralizer bound and neighboring-core transfer first put
the predecessor module in the penultimate core. Four-edge center expansion
makes it commute with the first module. At the terminal edge, residual
generation and the transported center/residual intersection show that R
is not contained in the penultimate center Y. Consequently Y joined with R
has index at most two in the terminal module of order sixteen. It centralizes
the predecessor module and the abelian image R joined with the terminal
center Z. The bounded-image kernel theorem, applied in their abelian join,
produces K; the residual image modulo R has order at most |Z|=2. The index-one
case gives the entire predecessor module directly.

The residual-generation identity is reused from the length-three proof;
this result has no dependency on the conclusion of (9.6). Source: Stellmacher,
Journal of Algebra 190 (1997), (9.6), printed p.53/PDF p.43 of
`refs/files/stellmacher-n-group.pdf`, the paragraph assuming R₀=1.
-/

namespace Stellmacher.SectionNine
open Later SectionsFiveToSeven CosetGraphContext SevenSix SectionEight
universe u

private theorem normalized_line_centralizes
    {G : Type u} [Group G] (Z : Subgroup G) (hcard : Nat.card Z = 2) :
    Subgroup.normalizer (Z : Set G) ≤ Subgroup.centralizer (Z : Set G) := by
  let N := Subgroup.normalizer (Z : Set G)
  let line := Z.subgroupOf N
  let _ : line.Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer Z.le_normalizer).mpr le_rfl
  have hlinecard : Nat.card line = 2 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe Z.le_normalizer).toEquiv]
    exact hcard
  have hcentral := Subgroup.central_of_normal_card_two line hlinecard
  intro actor hactor vector hvector
  have hh := Subgroup.mem_center_iff.mp
    (hcentral (show (⟨vector,Z.le_normalizer hvector⟩ : N) ∈ line from hvector))
      (⟨actor,hactor⟩ : N)
  exact (congrArg Subtype.val hh).symm

private theorem terminal_commutator_not_le_penultimate_center
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : 1 < ctx.criticalPath.length)
    (hquot : QuotientIsModel (GAt ctx.Γ ctx.criticalPath.firstStep)
      (QAt ctx.Γ ctx.criticalPath.firstStep) SL2Two)
    (hcard : Nat.card (VAt ctx.Γ ctx.criticalPath.firstStep) = 16) :
    ¬ ⁅VAt ctx.Γ ctx.criticalPath.firstStep,VAt ctx.Γ ctx.criticalPath.a'⁆ ≤
      ZAt ctx.Γ (ctx.criticalPath.path ⟨ctx.criticalPath.length-1,by omega⟩) := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let pen := cp.path ⟨cp.length-1,by omega⟩
  let U := VAt Γ cp.firstStep
  let V := VAt Γ cp.a'
  let Z := ZAt Γ pen
  let P := GAt Γ cp.a'
  let E := EAt Γ cp.a'
  let D := ⁅V,E⁆
  have hUP : U ≤ P := (lemma_seven_four ctx.sectionSeven Γ cp).first_containment.2
  have hEP : E ≤ P := by
    change Γ.twoResidualAt cp.a' ≤ Γ.vertexStabilizer cp.a'
    rw [Γ.twoResidualAt_def]
    exact twoResidualIn_le _
  have hPE : P ≤ Subgroup.normalizer (E : Set G) := by
    apply (Subgroup.normal_subgroupOf_iff_le_normalizer hEP).mp
    change ((Γ.twoResidualAt cp.a').subgroupOf P).Normal
    rw [Γ.twoResidualAt_def]
    exact twoResidualIn_normal _
  have hPD : P ≤ Subgroup.normalizer (D : Set G) := by
    intro actor hactor
    rw [Subgroup.mem_normalizer_iff_map_conj_eq, Subgroup.map_commutator,
      Subgroup.mem_normalizer_iff_map_conj_eq.mp
        (stabilizer_le_normalizer_v Γ cp.a' hactor),
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (hPE hactor)]
  obtain ⟨actor, hpen, hend⟩ := lemma_seven_five_endpoint_alignment
    ctx.sectionSeven Γ cp ctx.commutator_eq
  let equiv := MulAut.conj actor⁻¹
  have hZmap : (ZAt Γ cp.a).map equiv.toMonoidHom = Z := by
    change (z Γ cp.a).map (MulAut.conj actor⁻¹).toMonoidHom = z Γ pen
    rw [← z_act,hpen]
  have hVmap : (VAt Γ cp.firstStep).map equiv.toMonoidHom = V := by
    change (v Γ cp.firstStep).map (MulAut.conj actor⁻¹).toMonoidHom = v Γ cp.a'
    rw [← v_act,hend]
  have hLmap : (ZAt Γ cp.firstStep).map equiv.toMonoidHom = ZAt Γ cp.a' := by
    change (z Γ cp.firstStep).map (MulAut.conj actor⁻¹).toMonoidHom = z Γ cp.a'
    rw [← z_act,hend]
  have hEmap : (EAt Γ cp.firstStep).map equiv.toMonoidHom = E := by
    change (Γ.twoResidualAt cp.firstStep).map equiv.toMonoidHom = Γ.twoResidualAt cp.a'
    rw [Γ.twoResidualAt_def,Γ.twoResidualAt_def,← twoResidualIn_map_equiv]
    change twoResidualIn (conjugateBy (stabilizer Γ cp.firstStep) actor⁻¹) =
      twoResidualIn (stabilizer Γ cp.a')
    rw [← stabilizer_act,hend]
  have hDmap : (⁅VAt Γ cp.firstStep,EAt Γ cp.firstStep⁆).map equiv.toMonoidHom = D := by
    rw [Subgroup.map_commutator,hVmap,hEmap]
  have hgen : V = Z ⊔ D := by
    have hh := congrArg (fun subgroup : Subgroup G => subgroup.map equiv.toMonoidHom)
      (nine_six_initial_residual_generation ctx.toLocalContext)
    change (VAt Γ cp.firstStep).map equiv.toMonoidHom =
      (ZAt Γ cp.a ⊔ ⁅VAt Γ cp.firstStep,EAt Γ cp.firstStep⁆).map equiv.toMonoidHom at hh
    rwa [Subgroup.map_sup,hVmap,hZmap,hDmap] at hh
  have hZD : Z ⊓ D ≤ ZAt Γ cp.a' := by
    have hh := Subgroup.map_mono (f := equiv.toMonoidHom)
      (nine_six_initial_center_residual_intersection_le_next_center ctx hb hquot hcard)
    change (ZAt Γ cp.a ⊓ ⁅VAt Γ cp.firstStep,EAt Γ cp.firstStep⁆).map
      equiv.toMonoidHom ≤ (ZAt Γ cp.firstStep).map equiv.toMonoidHom at hh
    rwa [Subgroup.map_inf _ _ _ equiv.injective,hZmap,hDmap,hLmap] at hh
  have hUcore : U ≤ QAt Γ pen := (nine_three_initial_extraction_inputs
    ctx.toLocalContext hb).2.1
  have hadj : Γ.adjacent pen cp.a' := nine_five_penultimate_adjacent ctx.toLocalContext
  have hZcore : Z ≤ omegaOneCenter (QAt Γ pen) :=
    (lemma_seven_three ctx.sectionSeven Γ).center_core _ _
      ((mem_neighborhood_iff_adjacent Γ).mpr hadj)
  have hZU : ⁅Z,U⁆ = ⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
    ((hZcore.trans ((omegaOneCenter_le_centerAmbient _).trans
      (centerAmbient_le_centralizer _))).trans (Subgroup.centralizer_le hUcore))
  have hZV : Z ≤ V := hgen ▸ le_sup_left
  have hVP : V ≤ P :=
    (neighbor_join_le_core_of_length_gt_one Γ cp hb cp.a').trans (by
      change Γ.twoCoreAt cp.a' ≤ Γ.vertexStabilizer cp.a'
      rw [Γ.twoCoreAt_def]
      exact twoCoreIn_le _)
  have hRD : ⁅V,U⁆ ≤ D := by
    conv_lhs => rw [hgen]
    exact nine_five_commutator_join_le Z D U D
      ((hZV.trans hVP).trans hPD) Subgroup.le_normalizer
      (hZU.le.trans bot_le)
      (Subgroup.le_normalizer_iff_commutator_le_left.mp (hUP.trans hPD))
  intro hRZ
  rw [Subgroup.commutator_comm] at hRZ
  have hRline : ⁅V,U⁆ ≤ ZAt Γ cp.a' := (le_inf hRZ hRD).trans hZD
  have hkernel := (nine_next_center_commutator_and_kernel ctx hb cp.a' ⟨actor,hend⟩).2.2
  have hUQ : U ≤ QAt Γ cp.a' := by
    intro point hpoint
    exact (hkernel point (hUP hpoint)).mp
      ((Subgroup.commutator_mono le_rfl (Subgroup.zpowers_le.mpr hpoint)).trans hRline)
  exact cp.critical.2
    ((lemma_seven_four ctx.sectionSeven Γ cp).first_containment.1.trans hUQ)

private theorem neighboring_modules_commute
    {G : Type u} [Group G] [Finite G] {T A B : Subgroup G}
    (ctx : SectionNineLocalContext G T A B)
    (hb : 4 < ctx.criticalPath.length)
    (previous : ctx.Γ.Vertex)
    (hprevious : previous ∈ neighborhood ctx.Γ ctx.criticalPath.a) :
    ⁅VAt ctx.Γ previous,VAt ctx.Γ ctx.criticalPath.firstStep⁆ = ⊥ := by
  apply Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
  rw [VAt,v,ctx.Γ.vAt_def]
  apply sSup_le
  rintro center ⟨left,hleft,rfl⟩
  apply Subgroup.le_centralizer_iff.mpr
  rw [VAt,v,ctx.Γ.vAt_def]
  apply sSup_le
  rintro center ⟨right,hright,rfl⟩
  have hleftAdj := (mem_neighborhood_iff_adjacent ctx.Γ).mp hleft
  have hrightAdj := (mem_neighborhood_iff_adjacent ctx.Γ).mp hright
  have hprevAdj := (mem_neighborhood_iff_adjacent ctx.Γ).mp hprevious
  let vertices : Fin 5 → ctx.Γ.Vertex :=
    ![right,ctx.criticalPath.firstStep,ctx.criticalPath.a,previous,left]
  have hwalk : ∀ step : Fin 4,
      ctx.Γ.adjacent (vertices step.castSucc) (vertices step.succ) := by
    intro step
    fin_cases step
    · exact ctx.Γ.adjacent_symm hrightAdj
    · exact ctx.Γ.adjacent_symm ctx.criticalPath.firstStep_adj
    · exact hprevAdj
    · exact hleftAdj
  have hdist := ctx.Γ.distance_le_of_path 4 vertices hwalk
  change ctx.Γ.distance right left ≤ 4 at hdist
  have hcore := critical_minimality ctx.Γ ctx.criticalPath (hdist.trans_lt hb)
  have hcenter := (lemma_seven_three ctx.sectionSeven ctx.Γ).center_core left previous
    ((mem_neighborhood_iff_adjacent ctx.Γ).mpr (ctx.Γ.adjacent_symm hleftAdj))
  exact hcore.trans (Subgroup.le_centralizer_iff.mp
    (hcenter.trans ((omegaOneCenter_le_centerAmbient _).trans (centerAmbient_le_centralizer _))))

public theorem nine_six_zero_commutator_coatom
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : 3 < ctx.criticalPath.length)
    (hquot : QuotientIsModel (GAt ctx.Γ ctx.criticalPath.firstStep)
      (QAt ctx.Γ ctx.criticalPath.firstStep) SL2Two)
    (hcard : Nat.card (VAt ctx.Γ ctx.criticalPath.firstStep) = 16)
    (previous : ctx.Γ.Vertex)
    (hprevious : previous ∈ neighborhood ctx.Γ ctx.criticalPath.a)
    (_hprevious_ne : previous ≠ ctx.criticalPath.firstStep)
    (hzero : ⁅VAt ctx.Γ previous,VAt ctx.Γ
      (ctx.criticalPath.path ⟨ctx.criticalPath.length-2,by omega⟩)⁆ = ⊥) :
    ∃ K : Subgroup G, K ≤ VAt ctx.Γ previous ∧
      Nat.card (VAt ctx.Γ previous) ≤ 2 * Nat.card K ∧
      ⁅K,VAt ctx.Γ ctx.criticalPath.a'⁆ ≤
        ⁅VAt ctx.Γ ctx.criticalPath.firstStep,VAt ctx.Γ ctx.criticalPath.a'⁆ := by
  classical
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  have hb1 : 1 < cp.length := by change 3 < cp.length at hb; omega
  have hb4 : 4 < cp.length := by
    obtain ⟨half,hhalf⟩ := (lemma_seven_five ctx.sectionSeven Γ cp ctx.commutator_eq).odd_distance
    change 3 < cp.length at hb
    omega
  let pen := cp.path ⟨cp.length-1,by omega⟩
  let pre := cp.path ⟨cp.length-2,by omega⟩
  let U := VAt Γ cp.firstStep
  let V := VAt Γ cp.a'
  let C := VAt Γ previous
  let R := ⁅U,V⁆
  let Z := ZAt Γ cp.a'
  let Y := ZAt Γ pen
  let J := Y ⊔ R
  let image := R ⊔ Z
  let W := C ⊔ image
  have hpenTerm : Γ.adjacent pen cp.a' := nine_five_penultimate_adjacent ctx.toLocalContext
  have hprePen : Γ.adjacent pre pen := nine_five_previous_adjacent_penultimate
    ctx.toLocalContext hb1 pre (by
      change IsCriticalPathOffset Γ cp (cp.length-2) pre
      exact ⟨⟨cp.length-2,by omega⟩,rfl,rfl⟩)
  obtain ⟨align,hpen,hterm⟩ := lemma_seven_five_endpoint_alignment
    ctx.sectionSeven Γ cp ctx.commutator_eq
  have horbitTerm : IsConjugateVertex Γ cp.firstStep cp.a' := ⟨align,hterm⟩
  have horbitPen : IsConjugateVertex Γ cp.a pen := ⟨align,hpen⟩
  have horbitPre : IsConjugateVertex Γ cp.firstStep pre :=
    nine_five_penultimate_neighbor_orbit ctx.toLocalContext pre (Γ.adjacent_symm hprePen)
  have hYpre : Y ≤ VAt Γ pre := by
    change z Γ pen ≤ v Γ pre
    rw [v,Γ.vAt_def]
    exact le_sSup ⟨pen,(mem_neighborhood_iff_adjacent Γ).mpr hprePen,rfl⟩
  have hCpre : C ≤ QAt Γ pre :=
    (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hzero).trans
      (nine_three_module_centralizer_core_at_vertex ctx pre horbitPre)
  have hCY : C ≤ Subgroup.centralizer (Y : Set G) :=
    (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hzero).trans
      (Subgroup.centralizer_le hYpre)
  have hCpen : C ≤ QAt Γ pen :=
    (le_inf hCpre hCY).trans (nine_three_orbit_edge_core_centralizer ctx.toLocalContext
      pen horbitPen pre ((mem_neighborhood_iff_adjacent Γ).mpr (Γ.adjacent_symm hprePen)))
  have hQpenG : QAt Γ pen ≤ GAt Γ pen := by
    change Γ.twoCoreAt pen ≤ Γ.vertexStabilizer pen
    rw [Γ.twoCoreAt_def]
    exact twoCoreIn_le _
  have hQpenTerm : QAt Γ pen ≤ GAt Γ cp.a' :=
    ((lemma_seven_three ctx.sectionSeven Γ).sylow_and_core pen cp.a'
      ((mem_neighborhood_iff_adjacent Γ).mpr hpenTerm) default).2.2
  have hCterm : C ≤ GAt Γ cp.a' := hCpen.trans hQpenTerm
  have hCU : C ≤ Subgroup.centralizer (U : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp
      (neighboring_modules_commute ctx.toLocalContext hb4 previous hprevious)
  have hUV : U ≤ GAt Γ cp.a' := (lemma_seven_four ctx.sectionSeven Γ cp).first_containment.2
  have hVU : V ≤ GAt Γ cp.firstStep := (lemma_seven_four ctx.sectionSeven Γ cp).reverse_containment.2
  have hRV : R ≤ V := Subgroup.le_normalizer_iff_commutator_le_right.mp
    (hUV.trans (stabilizer_le_normalizer_v Γ cp.a'))
  have hRU : R ≤ U := Subgroup.le_normalizer_iff_commutator_le_left.mp
    (hVU.trans (stabilizer_le_normalizer_v Γ cp.firstStep))
  have hCR : C ≤ Subgroup.centralizer (R : Set G) := hCU.trans (Subgroup.centralizer_le hRU)
  have hVQ := neighbor_join_le_core_of_length_gt_one Γ cp hb1 cp.a'
  have hZcentral : GAt Γ cp.a' ≤ Subgroup.centralizer (Z : Set G) := by
    apply (stabilizer_le_normalizer_z Γ cp.a').trans
    exact normalized_line_centralizes Z
      (nine_next_center_commutator_and_kernel ctx hb1 cp.a' horbitTerm).1
  have hCZ : C ≤ Subgroup.centralizer (Z : Set G) := hCterm.trans hZcentral
  have hZV : Z ≤ V := by
    have hQP : QAt Γ cp.a' ≤ GAt Γ cp.a' := by
      change Γ.twoCoreAt cp.a' ≤ Γ.vertexStabilizer cp.a'
      rw [Γ.twoCoreAt_def]
      exact twoCoreIn_le _
    exact (nine_next_center_commutator_and_kernel ctx hb1 cp.a' horbitTerm).2.1.symm.le.trans
      (Subgroup.le_normalizer_iff_commutator_le_left.mp
        (hQP.trans (stabilizer_le_normalizer_v Γ cp.a')))
  have hYV : Y ≤ V := by
    change z Γ pen ≤ v Γ cp.a'
    rw [v,Γ.vAt_def]
    exact le_sSup ⟨pen,(mem_neighborhood_iff_adjacent Γ).mpr (Γ.adjacent_symm hpenTerm),rfl⟩
  have hJV : J ≤ V := sup_le hYV hRV
  have hImageV : image ≤ V := sup_le hRV hZV
  have hfour := (lemma_nine_three_ambient ctx hb1 cp.a ⟨1,Γ.act_one _⟩).2
  have hYcard : Nat.card Y = 4 := by
    change Nat.card (z Γ pen) = 4
    change Γ.act align cp.a = pen at hpen
    rw [← hpen,z_act,Subgroup.card_map_of_injective (MulAut.conj align⁻¹).injective]
    exact hfour
  have hVcard : Nat.card V = 16 :=
    (nine_seven_endpoint_module_card ctx.toLocalContext).symm.trans hcard
  have hRnot : ¬ R ≤ Y := terminal_commutator_not_le_penultimate_center ctx hb1 hquot hcard
  have hYlt : Nat.card Y < Nat.card J := lt_of_le_of_ne
    (Subgroup.card_le_of_le (show Y ≤ J from le_sup_left)) (by
      intro heq
      have hEq := Subgroup.eq_of_le_of_card_ge (show Y ≤ J from le_sup_left) heq.ge
      exact hRnot (le_sup_right.trans hEq.ge))
  have hJcard : 4 < Nat.card J := hYcard ▸ hYlt
  have hJindexBound : J.relIndex V ≤ 2 := by
    have hprod := (J.subgroupOf V).index_mul_card
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hJV).toEquiv,hVcard] at hprod
    change J.relIndex V * Nat.card J = 16 at hprod
    have hdvd : Nat.card J ∣ 16 := hVcard ▸ Subgroup.card_dvd_of_le hJV
    have hle : Nat.card J ≤ 16 := hVcard ▸ Subgroup.card_le_of_le hJV
    have hidxle : J.relIndex V ≤ 3 := by nlinarith
    have hidxdvd : J.relIndex V ∣ 16 := hVcard ▸ Subgroup.relIndex_dvd_card J V
    interval_cases hi : J.relIndex V
    all_goals first | decide | norm_num at hidxdvd
  have hJC : J ≤ Subgroup.centralizer (C : Set G) := sup_le
    (Subgroup.le_centralizer_iff.mp hCY) (Subgroup.le_centralizer_iff.mp hCR)
  by_cases hJone : J.relIndex V = 1
  · have hVJ : V ≤ J := Subgroup.relIndex_eq_one.mp hJone
    refine ⟨C,le_rfl,?_,?_⟩
    · change Nat.card C ≤ 2 * Nat.card C
      omega
    · exact (Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
      (Subgroup.le_centralizer_iff.mp (hVJ.trans hJC))).le.trans bot_le
  have hJindex : J.relIndex V = 2 := by
    have hpositive : 0 < J.relIndex V := Nat.card_pos
    omega
  have hlong := (lemma_seven_five ctx.sectionSeven Γ cp ctx.commutator_eq).longer_case hb1
  let _ : IsElementaryAbelian 2 U := hlong.1
  let _ : IsElementaryAbelian 2 V := (nine_three_second_extraction_inputs ctx.toLocalContext hb1).2.2.1
  obtain ⟨move,hmove⟩ := (lemma_seven_one ctx.sectionSeven Γ).local_transitivity cp.a
    ((mem_neighborhood_iff_adjacent Γ).mpr cp.firstStep_adj) hprevious
  have hCmap : U.map (MulAut.conj (move:G)⁻¹).toMonoidHom = C := by
    change (v Γ cp.firstStep).map _ = v Γ previous
    rw [← v_act,hmove]
  let _ : IsElementaryAbelian 2 C := hCmap ▸ IsElementaryAbelian.map _
  have hCimage : C ≤ Subgroup.centralizer (image : Set G) :=
    Subgroup.le_centralizer_iff.mpr (sup_le
      (Subgroup.le_centralizer_iff.mp hCR) (Subgroup.le_centralizer_iff.mp hCZ))
  have hCself : C ≤ Subgroup.centralizer (C : Set G) :=
    Subgroup.le_centralizer_iff_isMulCommutative.mpr inferInstance
  have hVself : V ≤ Subgroup.centralizer (V : Set G) :=
    Subgroup.le_centralizer_iff_isMulCommutative.mpr inferInstance
  have hJimage : J ≤ Subgroup.centralizer (image : Set G) :=
    (hJV.trans hVself).trans (Subgroup.centralizer_le hImageV)
  have hImageSelf : image ≤ Subgroup.centralizer (image : Set G) :=
    (hImageV.trans hVself).trans (Subgroup.centralizer_le hImageV)
  have hWC : IsMulCommutative W := Subgroup.le_centralizer_iff_isMulCommutative.mp
    (sup_le
      (Subgroup.le_centralizer_iff.mpr (sup_le hCself (Subgroup.le_centralizer_iff.mp hCimage)))
      (Subgroup.le_centralizer_iff.mpr (sup_le hCimage hImageSelf)))
  have hJW : J ≤ Subgroup.centralizer (W : Set G) :=
    Subgroup.le_centralizer_iff.mpr (sup_le
      (Subgroup.le_centralizer_iff.mp hJC) (Subgroup.le_centralizer_iff.mp hJimage))
  have hCcomm : ⁅C,V⁆ ≤ image := by
    have hbound := nine_seven_subgroup_terminal_commutator_le ctx hb1 hfour
      ((nine_seven_endpoint_quotient_model_iff ctx.toLocalContext).mp hquot)
      C (hCpen.trans hQpenG) hCterm
    exact hbound.trans (sup_le_sup (by
      rw [Subgroup.commutator_comm]
      exact Subgroup.commutator_mono
        (lemma_seven_four ctx.sectionSeven Γ cp).first_containment.1 le_rfl) le_rfl)
  have hImageComm : ⁅image,V⁆ = ⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
    (hImageV.trans hVself)
  have hWcomm : ⁅W,V⁆ ≤ image := nine_five_commutator_join_le C image V image
    (hCimage.trans (Subgroup.centralizer_le_normalizer _)) Subgroup.le_normalizer
    hCcomm (hImageComm.le.trans bot_le)
  obtain ⟨K,hKC,hKcard,hKcomm⟩ :=
    Subgroup.exists_large_subgroup_commutator_le_of_index_two C W V J R image
      le_sup_left hWC le_sup_right hWcomm hJV hJW hJindex
  have hImageIndex : R.relIndex image ≤ 2 := by
    let _ : CommGroup V := IsMulCommutative.instCommGroup
    have heq := Subgroup.relIndex_sup_left (Z.subgroupOf V) (R.subgroupOf V)
    rw [← Subgroup.subgroupOf_sup hRV hZV,
      Subgroup.relIndex_subgroupOf hImageV,Subgroup.relIndex_subgroupOf hZV] at heq
    have hbound : R.relIndex Z ≤ Nat.card Z :=
      Nat.le_of_dvd Nat.card_pos (Subgroup.relIndex_dvd_card R Z)
    have hZcard := (nine_next_center_commutator_and_kernel ctx hb1 cp.a' horbitTerm).1
    exact heq.le.trans (hZcard ▸ hbound)
  exact ⟨K,hKC,hKcard.trans (Nat.mul_le_mul_right _ hImageIndex),hKcomm⟩

end Stellmacher.SectionNine
