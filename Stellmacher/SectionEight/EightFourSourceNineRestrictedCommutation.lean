module
public import Stellmacher.SectionEight.EightFourShiftedCenterAction
public import Stellmacher.SectionEight.EightFourStarNeighborModule
public import Stellmacher.SectionOne.OneSevenFixedSpaceFixer

/-!
# Restricted star commutation after source (9)

The actual first-step star centralizes the initial center when the critical
length exceeds two. The first configuration then makes its intersection with
the intermediate center trivial: that intersection centralizes both factors
of the retained generating subgroup, hence both adjacent stabilizers, and the
ambient two-core is trivial. Source (9) consequently makes the star disjoint
from the shifted edge-fixed subgroup. Normality of the actual star puts the
restricted commutator in it, proving the source's R1 intersection is trivial.

For the remaining module step, the one-seven natural-factor decomposition
identifies the pointwise fixer of the J-fixed space with J, whose commutator
lies in its fixed space. This is transported through the original quotient
witness and along the actual edge, with reversed orientation excluded. The
restricted star fixes that edge-fixed subgroup, by normality and the proved
intersection, so its full commutator lies in R1 and vanishes.

The geometric elimination and module-action kernels use the local context.
The source-nine consumer still uses the original configuration record; no
generated source-nine producer or full (8.4) normality theorem is asserted.
The conditional index reduction is not used in these proofs.

Source: Stellmacher (8.4), printed pp.39–40, especially the R1 paragraph after
(9), in `refs/files/stellmacher-n-group.pdf`.

The source-nine elimination results are also proved over the exact local
context and local configuration record. Their original canonical statements
remain fieldwise-data wrappers with the same quotient action and star family.
-/

namespace Stellmacher.SectionEight
open Later SectionsFiveToSeven CosetGraphContext
universe u

public theorem eight_four_first_configuration_centralizing_inf_eq_bot_local
    {H : Type u} [Group H] [Finite H] {S P1 P2 : Subgroup H}
    (ctx : SectionEightLocalContext H S P1 P2)
    (hcenter : ZAt ctx.Γ ctx.criticalPath.firstStep ≤
      CenterAmbient (GAt ctx.Γ ctx.criticalPath.firstStep))
    (A L0 B : Subgroup H) (x : H)
    (hBA : B ≤ Subgroup.centralizer (A : Set H))
    (hAprev : A ≤ QAt ctx.Γ
      (ctx.criticalPath.path ⟨ctx.criticalPath.length - 1, by omega⟩))
    (hL0 : L0 ≤ GAt ctx.Γ ctx.criticalPath.a')
    (hLgen : L0 = A ⊔ A.conjBy x) (hx : x ∈ L0)
    (hfull : L0 ⊔
      (GAt ctx.Γ (ctx.criticalPath.path ⟨ctx.criticalPath.length - 1, by omega⟩) ⊓
        GAt ctx.Γ ctx.criticalPath.a') = GAt ctx.Γ ctx.criticalPath.a') :
    B ⊓
      ZAt ctx.Γ (ctx.Γ.act x⁻¹
        (ctx.criticalPath.path ⟨ctx.criticalPath.length - 1, by omega⟩)) = ⊥ := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let h := ctx.sectionSeven
  let previous := cp.path ⟨cp.length - 1, by omega⟩
  let neighbor := Γ.act x⁻¹ previous
  let R := B ⊓ ZAt Γ neighbor
  let conjugation := (MulAut.conj x).toMonoidHom
  have hpos := cp.length_pos
  have hprevious : Γ.adjacent cp.a' previous := by
    have hedge := cp.path_adj ⟨cp.length - 1, by omega⟩
    have hindex : (⟨cp.length - 1, by omega⟩ : Fin cp.length).succ =
        ⟨cp.length, Nat.lt_succ_self _⟩ := by
      apply Fin.ext
      dsimp
      omega
    rw [hindex, cp.path_end] at hedge
    exact Γ.adjacent_symm hedge
  have hfix : Γ.act x⁻¹ cp.a' = cp.a' := by
    have hmem := (GAt Γ cp.a').inv_mem (hL0 hx)
    change x⁻¹ ∈ (Γ.vertexStabilizer cp.a' : Set H) at hmem
    rw [Γ.stabilizer_def] at hmem
    exact hmem
  have hadj : Γ.adjacent cp.a' neighbor := by
    have hedge := adjacent_act Γ x⁻¹ hprevious
    rwa [hfix] at hedge
  have hneighbor := (SevenSix.mem_neighborhood_iff_adjacent Γ).mpr hadj
  have hcentral := eight_four_terminal_neighbor_center_le_local ctx hcenter neighbor hadj
  have hRC : R ≤ Subgroup.centralizer (GAt Γ neighbor : Set H) :=
    inf_le_right.trans (hcentral.trans (SevenSix.centerAmbient_le_centralizer _))
  have hRA : R ≤ Subgroup.centralizer (A : Set H) := inf_le_left.trans hBA
  have hQmap : (QAt Γ previous).map conjugation = QAt Γ neighbor := by
    simp only [neighbor, SevenSix.q_act, inv_inv, conjugation]
  have hAxQ : A.conjBy x ≤ QAt Γ neighbor :=
    (Subgroup.map_mono hAprev).trans_eq hQmap
  have hAxP : A.conjBy x ≤ GAt Γ neighbor := hAxQ.trans (by
    rw [show QAt Γ neighbor = twoCoreIn (GAt Γ neighbor) from Γ.twoCoreAt_def neighbor]
    exact Subgroup.map_subtype_le _)
  have hAxR : A.conjBy x ≤ Subgroup.centralizer (R : Set H) :=
    hAxP.trans (Subgroup.le_centralizer_iff.mp hRC)
  have hL0R : L0 ≤ Subgroup.centralizer (R : Set H) := by
    rw [hLgen]
    exact sup_le (Subgroup.le_centralizer_iff.mp hRA) hAxR
  have hL0map : L0.map conjugation = L0 :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (L0.le_normalizer hx)
  have hPmap : (GAt Γ cp.a').map conjugation = GAt Γ cp.a' :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp ((GAt Γ cp.a').le_normalizer (hL0 hx))
  have hpreviousMap : (GAt Γ previous).map conjugation = GAt Γ neighbor := by
    simp only [neighbor, stabilizer_act, conjugateBy, inv_inv, conjugation]
  have hnewgen : L0 ⊔ (GAt Γ neighbor ⊓ GAt Γ cp.a') = GAt Γ cp.a' := by
    have hmap := congrArg (Subgroup.map conjugation) hfull
    change (L0 ⊔ (GAt Γ previous ⊓ GAt Γ cp.a')).map conjugation =
      (GAt Γ cp.a').map conjugation at hmap
    rw [Subgroup.map_sup, Subgroup.map_inf _ _ _ (MulAut.conj x).injective,
      hL0map, hpreviousMap, hPmap] at hmap
    exact hmap
  have hneighborR : GAt Γ neighbor ≤ Subgroup.centralizer (R : Set H) :=
    Subgroup.le_centralizer_iff.mp hRC
  have hendR : GAt Γ cp.a' ≤ Subgroup.centralizer (R : Set H) := by
    rw [← hnewgen]
    exact sup_le hL0R (inf_le_left.trans hneighborR)
  have hgenerated : GAt Γ cp.a' ⊔ GAt Γ neighbor = ⊤ :=
    (edge_sectionThree_data h Γ hneighbor default).2.2.2.2.1
  have htopR : (⊤ : Subgroup H) ≤ Subgroup.centralizer (R : Set H) := by
    rw [← hgenerated]
    exact sup_le hendR hneighborR
  have hnormal : R.Normal := Subgroup.normalizer_eq_top_iff.mp
    (top_unique (htopR.trans (Subgroup.centralizer_le_normalizer (R : Set H))))
  let _ : IsElementaryAbelian 2 (ZAt Γ neighbor) :=
    SevenSix.z_isElementaryAbelian_of_neighbor h Γ
      ((SevenSix.mem_neighborhood_iff_adjacent Γ).mpr (Γ.adjacent_symm hadj))
  have htwo : IsPGroup 2 R :=
    (IsElementaryAbelian.isPGroup 2 (ZAt Γ neighbor)).to_le inf_le_right
  have hcore : R ≤ pCore 2 H := le_sSup ⟨hnormal, htwo⟩
  exact bot_unique (hcore.trans_eq h.twoCore_eq_bot)

public theorem eight_four_neighbor_module_centralizes_initial_center_local
    {H : Type u} [Group H] [Finite H] {S P1 P2 : Subgroup H}
    (ctx : SectionEightLocalContext H S P1 P2)
    (hlen : 2 < ctx.criticalPath.length) :
    VAt ctx.Γ ctx.criticalPath.firstStep ≤
      Subgroup.centralizer (ZAt ctx.Γ ctx.criticalPath.a : Set H) := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  have hfirst := (SevenSix.mem_neighborhood_iff_adjacent Γ).mpr cp.firstStep_adj
  have hcore : QAt Γ cp.a ≤ Subgroup.centralizer (ZAt Γ cp.a : Set H) :=
    Subgroup.le_centralizer_iff.mp
      (((lemma_seven_three ctx.sectionSeven Γ).center_core cp.a cp.firstStep hfirst).trans
        ((SevenSix.omegaOneCenter_le_centerAmbient _).trans
          (SevenSix.centerAmbient_le_centralizer _)))
  change v Γ cp.firstStep ≤ _
  rw [v, Γ.vAt_def]
  apply sSup_le
  rintro _ ⟨vertex, hvertex, rfl⟩
  have hadj := (SevenSix.mem_neighborhood_iff_adjacent Γ).mp hvertex
  have hdist : Γ.distance vertex cp.a ≤ 2 := by
    let path : Fin 3 → Γ.Vertex := ![vertex, cp.firstStep, cp.a]
    have hpath : ∀ index : Fin 2, Γ.adjacent (path index.castSucc) (path index.succ) := by
      intro index
      fin_cases index
      · exact Γ.adjacent_symm hadj
      · exact Γ.adjacent_symm cp.firstStep_adj
    exact Γ.distance_le_of_path 2 path hpath
  exact (SevenSix.critical_minimality Γ cp (hdist.trans_lt hlen)).trans hcore

public theorem eight_four_initial_fixed_centralizer_commutator_local
    {H : Type u} [Group H] [Finite H] {S P1 P2 : Subgroup H}
    (ctx : SectionEightLocalContext H S P1 P2)
    (w : QuotientModuleWitness
      (GAt ctx.Γ ctx.criticalPath.a)
      (GAt ctx.Γ ctx.criticalPath.a ⊓
        Subgroup.centralizer (ZAt ctx.Γ ctx.criticalPath.a : Set H))
      (ZAt ctx.Γ ctx.criticalPath.a))
    (D : Subgroup H) (hDP : D ≤ GAt ctx.Γ ctx.criticalPath.a)
    (hfix : D ≤ Subgroup.centralizer (w.oneJFixedPoints S : Set H)) :
    ⁅D, ZAt ctx.Γ ctx.criticalPath.a⁆ ≤ w.oneJFixedPoints S := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let P := GAt Γ cp.a
  let Za := ZAt Γ cp.a
  let _ := w.groupX
  let _ := w.finiteX
  let _ := MulDistribMulAction.compHom Za w.action
  have hfirst := (SevenSix.mem_neighborhood_iff_adjacent Γ).mpr cp.firstStep_adj
  let _ := SevenSix.z_isElementaryAbelian_of_neighbor ctx.sectionSeven Γ hfirst
  have hlocal := (local_quotient_sylow_action_setup ctx.sectionSeven Γ cp w).1
  obtain ⟨hSP, U, hU⟩ := (SevenSix.edge_sylow_data ctx.sectionSeven Γ cp).1
  have hUS : (U : Subgroup P) = S.subgroupOf P := by
    apply Subgroup.map_injective P.subtype_injective
    rw [Subgroup.map_subgroupOf_eq_of_le hSP]
    exact hU
  let Ub := U.mapSurjective w.surjective
  let Sb := (S.subgroupOf P).map w.projection
  let J := SectionOne.oneJ (V := Za) Sb
  have hUb : (Ub : Subgroup w.X) = Sb := by
    change (U : Subgroup P).map w.projection = _
    rw [hUS]
  have hfixer := SectionOne.oneSeven_fixedSpace_fixer_eq_oneJ_unconditional hlocal Ub
  have hquad := SectionOne.oneSeven_commutator_le_fixed hlocal Ub
  rw [hUb] at hfixer hquad
  have himage : (D.subgroupOf P).map w.projection ≤ J := by
    change (D.subgroupOf P).map w.projection ≤ SectionOne.oneJ (V := ZAt Γ cp.a) Sb
    rw [← hfixer]
    rintro _ ⟨actor, hactor, rfl⟩
    rw [mem_fixingSubgroup_iff]
    intro point hpoint
    apply Subtype.ext
    change ((w.action (w.projection actor)) point : H) = point
    rw [w.action_compatible]
    have hF : (point : H) ∈ w.oneJFixedPoints S :=
      Subgroup.mem_map_of_mem Za.subtype hpoint
    have hcomm := Subgroup.mem_centralizer_iff.mp (hfix hactor) (point : H) hF
    change (point : H) * (actor : H) = (actor : H) * (point : H) at hcomm
    rw [← hcomm, mul_inv_cancel_right]
  have hcomm : commutatorAction ((D.subgroupOf P).map w.projection) Za ≤
      commutatorAction J Za := by
    rw [commutatorAction_eq_closure, commutatorAction_eq_closure]
    apply Subgroup.closure_mono
    rintro point ⟨actor, vector, rfl⟩
    exact ⟨⟨actor, himage actor.property⟩, vector, rfl⟩
  have hm := Subgroup.map_mono (hcomm.trans hquad) (f := Za.subtype)
  rw [w.commutatorAction_image_map_subtype D hDP, Subgroup.commutator_comm] at hm
  exact hm

public theorem eight_four_edge_fixed_centralizer_commutator_local
    {H : Type u} [Group H] [Finite H] {S P1 P2 : Subgroup H}
    (ctx : SectionEightLocalContext H S P1 P2)
    (w : QuotientModuleWitness
      (GAt ctx.Γ ctx.criticalPath.a)
      (GAt ctx.Γ ctx.criticalPath.a ⊓
        Subgroup.centralizer (ZAt ctx.Γ ctx.criticalPath.a : Set H))
      (ZAt ctx.Γ ctx.criticalPath.a))
    (F : ctx.Γ.Vertex → ctx.Γ.Vertex → Subgroup H)
    (hbase : F ctx.criticalPath.a ctx.criticalPath.firstStep = w.oneJFixedPoints S)
    (hcov : ∀ g d l, F (ctx.Γ.act g d) (ctx.Γ.act g l) = (F d l).conjBy g⁻¹)
    (vertex neighbor : ctx.Γ.Vertex) (hadj : ctx.Γ.adjacent vertex neighbor)
    (hcentral : ZAt ctx.Γ neighbor ≤ CenterAmbient (GAt ctx.Γ neighbor))
    (D : Subgroup H) (hDP : D ≤ GAt ctx.Γ vertex)
    (hfix : D ≤ Subgroup.centralizer (F vertex neighbor : Set H)) :
    ⁅D, ZAt ctx.Γ vertex⁆ ≤ F vertex neighbor := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  obtain ⟨actor, horient | horient⟩ :=
    (lemma_seven_one ctx.sectionSeven Γ).edge_not_vertex_transitive.1 cp.firstStep_adj hadj
  · have hvertex : Γ.act actor⁻¹ vertex = cp.a := by
      rw [← horient.1, ← Γ.act_mul, mul_inv_cancel, Γ.act_one]
    have hneighbor : Γ.act actor⁻¹ neighbor = cp.firstStep := by
      rw [← horient.2, ← Γ.act_mul, mul_inv_cancel, Γ.act_one]
    have hP := stabilizer_act Γ actor⁻¹ vertex
    have hZ := z_act Γ actor⁻¹ vertex
    have hF := hcov actor⁻¹ vertex neighbor
    rw [hvertex, inv_inv] at hP hZ
    rw [hvertex, hneighbor, inv_inv, hbase] at hF
    have hDP' : D.conjBy actor ≤ GAt Γ cp.a :=
      (Subgroup.map_mono hDP (f := (MulAut.conj actor).toMonoidHom)).trans_eq hP.symm
    have hfix' : D.conjBy actor ≤ Subgroup.centralizer (w.oneJFixedPoints S : Set H) := by
      apply Subgroup.commutator_eq_bot_iff_le_centralizer.mp
      have hm := congrArg (Subgroup.map (MulAut.conj actor).toMonoidHom)
        (Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hfix)
      rw [Subgroup.map_commutator, Subgroup.map_bot] at hm
      rw [hF]
      exact hm
    have hbound := eight_four_initial_fixed_centralizer_commutator_local ctx w
      (D.conjBy actor) hDP' hfix'
    change ⁅D.conjBy actor, z Γ cp.a⁆ ≤ w.oneJFixedPoints S at hbound
    rw [hZ, hF] at hbound
    change ⁅D.map (MulAut.conj actor).toMonoidHom,
      (z Γ vertex).map (MulAut.conj actor).toMonoidHom⁆ ≤
        (F vertex neighbor).map (MulAut.conj actor).toMonoidHom at hbound
    rw [← Subgroup.map_commutator] at hbound
    exact (Subgroup.map_le_map_iff_of_injective (MulAut.conj actor).injective).mp hbound
  · have hZendP : z Γ (Γ.act actor cp.a') ≤ stabilizer Γ neighbor := by
      rw [← horient.1, stabilizer_act, z_act]
      exact Subgroup.map_mono (lemma_seven_four ctx.sectionSeven Γ cp).reverse_containment.1
    have hcomm : ⁅z Γ neighbor, z Γ (Γ.act actor cp.a')⁆ = ⊥ :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
        (hcentral.trans ((SevenSix.centerAmbient_le_centralizer _).trans
          (Subgroup.centralizer_le hZendP)))
    rw [← horient.1, z_act, z_act, ← Subgroup.map_commutator] at hcomm
    exact (ctx.commutator_ne (Subgroup.map_injective (MulAut.conj actor⁻¹).injective
      (hcomm.trans (Subgroup.map_bot _).symm))).elim

public theorem eight_four_equivariant_edge_fixed_normalizer
    {H : Type u} [Group H] [Finite H] {S P1 P2 : Subgroup H}
    (Γ : CosetGraphContext H S P1 P2)
    (F : Γ.Vertex → Γ.Vertex → Subgroup H)
    (hcov : ∀ g d l, F (Γ.act g d) (Γ.act g l) = (F d l).conjBy g⁻¹)
    (vertex neighbor : Γ.Vertex) :
    GAt Γ vertex ⊓ GAt Γ neighbor ≤ Subgroup.normalizer (F vertex neighbor : Set H) := by
  intro actor hactor
  have hvertex : Γ.act actor⁻¹ vertex = vertex := by
    have hmem := (GAt Γ vertex).inv_mem hactor.1
    change actor⁻¹ ∈ (Γ.vertexStabilizer vertex : Set H) at hmem
    rwa [Γ.stabilizer_def] at hmem
  have hneighbor : Γ.act actor⁻¹ neighbor = neighbor := by
    have hmem := (GAt Γ neighbor).inv_mem hactor.2
    change actor⁻¹ ∈ (Γ.vertexStabilizer neighbor : Set H) at hmem
    rwa [Γ.stabilizer_def] at hmem
  apply Subgroup.mem_normalizer_iff_map_conj_eq.mpr
  have heq := hcov actor⁻¹ vertex neighbor
  rw [hvertex, hneighbor, inv_inv] at heq
  exact heq.symm

public theorem eight_four_source_nine_star_inf_center_eq_bot_local
    {H : Type u} [Group H] [Finite H]
    {S P1 P2 : Subgroup H}
    (ctx : SectionEightLocalContext H S P1 P2)
    (hcenter : ZAt ctx.Γ ctx.criticalPath.firstStep ≤
      CenterAmbient (GAt ctx.Γ ctx.criticalPath.firstStep))
    (w : QuotientModuleWitness
      (GAt ctx.Γ ctx.criticalPath.a)
      (GAt ctx.Γ ctx.criticalPath.a ⊓
        Subgroup.centralizer (ZAt ctx.Γ ctx.criticalPath.a : Set H))
      (ZAt ctx.Γ ctx.criticalPath.a))
    (F : ctx.Γ.Vertex → ctx.Γ.Vertex → Subgroup H)
    (hsub : ∀ d l, F d l ≤ ZAt ctx.Γ d ⊓ GAt ctx.Γ l)
    (hformula : ∀ d l, F d l = ⨆ (g : H)
      (_ : ctx.Γ.act g ctx.criticalPath.a = d ∧
        ctx.Γ.act g ctx.criticalPath.firstStep = l),
      (w.oneJFixedPoints S).conjBy g⁻¹)
    (configuration : EightFourSourceNineLocalData ctx F)
    (hlen : 2 < ctx.criticalPath.length) :
    (⨆ vertex, F vertex ctx.criticalPath.firstStep) ⊓
      ZAt ctx.Γ configuration.d = ⊥ := by
  have hCA := ((eight_four_star_le_neighbor_module_local ctx w F hsub hformula)
    ctx.criticalPath.firstStep).trans
      ((eight_four_neighbor_module_centralizes_initial_center_local ctx hlen).trans
        (Subgroup.centralizer_le configuration.hA))
  rw [configuration.hd]
  exact eight_four_first_configuration_centralizing_inf_eq_bot_local ctx
    hcenter configuration.A configuration.L0 (⨆ vertex, F vertex ctx.criticalPath.firstStep)
    configuration.x hCA configuration.hAprev configuration.hL0 configuration.hLgen
    configuration.hx configuration.hfirstfull

public theorem eight_four_source_nine_star_inf_fixed_eq_bot_local
    {H : Type u} [Group H] [Finite H]
    {S P1 P2 : Subgroup H}
    (ctx : SectionEightLocalContext H S P1 P2)
    (hcenter : ZAt ctx.Γ ctx.criticalPath.firstStep ≤
      CenterAmbient (GAt ctx.Γ ctx.criticalPath.firstStep))
    (w : QuotientModuleWitness
      (GAt ctx.Γ ctx.criticalPath.a)
      (GAt ctx.Γ ctx.criticalPath.a ⊓
        Subgroup.centralizer (ZAt ctx.Γ ctx.criticalPath.a : Set H))
      (ZAt ctx.Γ ctx.criticalPath.a))
    (hbranch : (Subgroup.normalClosure
      ((w.oneJFixedPoints S).subgroupOf (GAt ctx.Γ ctx.criticalPath.firstStep) :
        Set (GAt ctx.Γ ctx.criticalPath.firstStep))).map
          (GAt ctx.Γ ctx.criticalPath.firstStep).subtype ≠ w.oneJFixedPoints S)
    (F : ctx.Γ.Vertex → ctx.Γ.Vertex → Subgroup H)
    (hbase : F ctx.criticalPath.a ctx.criticalPath.firstStep = w.oneJFixedPoints S)
    (hcov : ∀ g d l, F (ctx.Γ.act g d) (ctx.Γ.act g l) = (F d l).conjBy g⁻¹)
    (hsub : ∀ d l, F d l ≤ ZAt ctx.Γ d ⊓ GAt ctx.Γ l)
    (hformula : ∀ d l, F d l = ⨆ (g : H)
      (_ : ctx.Γ.act g ctx.criticalPath.a = d ∧
        ctx.Γ.act g ctx.criticalPath.firstStep = l),
      (w.oneJFixedPoints S).conjBy g⁻¹)
    (configuration : EightFourSourceNineLocalData ctx F)
    (hlen : 2 < ctx.criticalPath.length) :
    (⨆ vertex, F vertex ctx.criticalPath.firstStep) ⊓
      F (ctx.Γ.act configuration.y⁻¹ ctx.criticalPath.a') configuration.d = ⊥ := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let C := ⨆ vertex, F vertex cp.firstStep
  let next := Γ.act configuration.y⁻¹ cp.a'
  have hcore := (eight_four_star_elementary_core_local ctx hcenter w hbranch
    F hbase hcov hsub hformula cp.firstStep).2
  have hCP : C ≤ GAt Γ cp.a := hcore.trans
    ((lemma_seven_three (ctx.sectionSeven) Γ).sylow_and_core
      cp.firstStep cp.a
      ((SevenSix.mem_neighborhood_iff_adjacent Γ).mpr (Γ.adjacent_symm cp.firstStep_adj))
      default).2.2
  have hbound : C ⊓ F next configuration.d ≤ C ⊓ ZAt Γ configuration.d :=
    le_inf inf_le_left ((le_inf inf_le_right (inf_le_left.trans hCP)).trans configuration.forward)
  exact bot_unique (hbound.trans_eq
    (eight_four_source_nine_star_inf_center_eq_bot_local ctx hcenter w F hsub hformula configuration hlen))

public theorem eight_four_source_nine_r1_eq_bot_local
    {H : Type u} [Group H] [Finite H]
    {S P1 P2 : Subgroup H}
    (ctx : SectionEightLocalContext H S P1 P2)
    (hcenter : ZAt ctx.Γ ctx.criticalPath.firstStep ≤
      CenterAmbient (GAt ctx.Γ ctx.criticalPath.firstStep))
    (w : QuotientModuleWitness
      (GAt ctx.Γ ctx.criticalPath.a)
      (GAt ctx.Γ ctx.criticalPath.a ⊓
        Subgroup.centralizer (ZAt ctx.Γ ctx.criticalPath.a : Set H))
      (ZAt ctx.Γ ctx.criticalPath.a))
    (hbranch : (Subgroup.normalClosure
      ((w.oneJFixedPoints S).subgroupOf (GAt ctx.Γ ctx.criticalPath.firstStep) :
        Set (GAt ctx.Γ ctx.criticalPath.firstStep))).map
          (GAt ctx.Γ ctx.criticalPath.firstStep).subtype ≠ w.oneJFixedPoints S)
    (F : ctx.Γ.Vertex → ctx.Γ.Vertex → Subgroup H)
    (hbase : F ctx.criticalPath.a ctx.criticalPath.firstStep = w.oneJFixedPoints S)
    (hcov : ∀ g d l, F (ctx.Γ.act g d) (ctx.Γ.act g l) = (F d l).conjBy g⁻¹)
    (hsub : ∀ d l, F d l ≤ ZAt ctx.Γ d ⊓ GAt ctx.Γ l)
    (hformula : ∀ d l, F d l = ⨆ (g : H)
      (_ : ctx.Γ.act g ctx.criticalPath.a = d ∧
        ctx.Γ.act g ctx.criticalPath.firstStep = l),
      (w.oneJFixedPoints S).conjBy g⁻¹)
    (configuration : EightFourSourceNineLocalData ctx F)
    (hlen : 2 < ctx.criticalPath.length) :
    let next := ctx.Γ.act configuration.y⁻¹ ctx.criticalPath.a'
    let C := ⨆ vertex, F vertex ctx.criticalPath.firstStep
    ⁅C ⊓ GAt ctx.Γ next, ZAt ctx.Γ next⁆ ⊓ F next configuration.d = ⊥ := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let C := ⨆ vertex, F vertex cp.firstStep
  let next := Γ.act configuration.y⁻¹ cp.a'
  have hCn := (eight_four_edge_star_closure_local ctx w F hbase hcov hsub hformula).2.2.2 cp.firstStep
  have hnorm : GAt Γ cp.firstStep ≤ Subgroup.normalizer (C : Set H) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hCn.1).mp hCn.2
  have hZP := (eight_four_source_nine_shifted_center_action_local ctx hcenter w hbranch
    F hbase hcov hsub hformula configuration hlen).2.1
  have hW : ⁅C ⊓ GAt Γ next, ZAt Γ next⁆ ≤ C :=
    (Subgroup.commutator_mono inf_le_left le_rfl).trans
      (Subgroup.le_normalizer_iff_commutator_le_left.mp (hZP.trans hnorm))
  exact bot_unique ((inf_le_inf_right _ hW).trans_eq
    (eight_four_source_nine_star_inf_fixed_eq_bot_local ctx hcenter w hbranch
      F hbase hcov hsub hformula configuration hlen))

public theorem eight_four_source_nine_restricted_commutation_local
    {H : Type u} [Group H] [Finite H]
    {S P1 P2 : Subgroup H}
    (ctx : SectionEightLocalContext H S P1 P2)
    (hcenter : ZAt ctx.Γ ctx.criticalPath.firstStep ≤
      CenterAmbient (GAt ctx.Γ ctx.criticalPath.firstStep))
    (w : QuotientModuleWitness
      (GAt ctx.Γ ctx.criticalPath.a)
      (GAt ctx.Γ ctx.criticalPath.a ⊓
        Subgroup.centralizer (ZAt ctx.Γ ctx.criticalPath.a : Set H))
      (ZAt ctx.Γ ctx.criticalPath.a))
    (hbranch : (Subgroup.normalClosure
      ((w.oneJFixedPoints S).subgroupOf (GAt ctx.Γ ctx.criticalPath.firstStep) :
        Set (GAt ctx.Γ ctx.criticalPath.firstStep))).map
          (GAt ctx.Γ ctx.criticalPath.firstStep).subtype ≠ w.oneJFixedPoints S)
    (F : ctx.Γ.Vertex → ctx.Γ.Vertex → Subgroup H)
    (hbase : F ctx.criticalPath.a ctx.criticalPath.firstStep = w.oneJFixedPoints S)
    (hcov : ∀ g d l, F (ctx.Γ.act g d) (ctx.Γ.act g l) = (F d l).conjBy g⁻¹)
    (hsub : ∀ d l, F d l ≤ ZAt ctx.Γ d ⊓ GAt ctx.Γ l)
    (hformula : ∀ d l, F d l = ⨆ (g : H)
      (_ : ctx.Γ.act g ctx.criticalPath.a = d ∧
        ctx.Γ.act g ctx.criticalPath.firstStep = l),
      (w.oneJFixedPoints S).conjBy g⁻¹)
    (configuration : EightFourSourceNineLocalData ctx F)
    (hlen : 2 < ctx.criticalPath.length) :
    let next := ctx.Γ.act configuration.y⁻¹ ctx.criticalPath.a'
    let C := ⨆ vertex, F vertex ctx.criticalPath.firstStep
    ⁅C ⊓ GAt ctx.Γ next, ZAt ctx.Γ next⁆ = ⊥ := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let h := ctx.sectionSeven
  let C := ⨆ vertex, F vertex cp.firstStep
  let next := Γ.act configuration.y⁻¹ cp.a'
  let D := C ⊓ GAt Γ next
  have hpos := cp.length_pos
  let previous := cp.path ⟨cp.length - 1, by omega⟩
  have hprevious : Γ.adjacent cp.a' previous := by
    have hedge := cp.path_adj ⟨cp.length - 1, by omega⟩
    have hindex : (⟨cp.length - 1, by omega⟩ : Fin cp.length).succ =
        ⟨cp.length, Nat.lt_succ_self _⟩ := by
      apply Fin.ext
      dsimp
      omega
    rw [hindex, cp.path_end] at hedge
    exact Γ.adjacent_symm hedge
  have hfix : Γ.act configuration.x⁻¹ cp.a' = cp.a' := by
    have hmem := (GAt Γ cp.a').inv_mem (configuration.hL0 configuration.hx)
    change configuration.x⁻¹ ∈ (Γ.vertexStabilizer cp.a' : Set H) at hmem
    rwa [Γ.stabilizer_def] at hmem
  have hmiddle : Γ.adjacent cp.a' configuration.d := by
    have hedge := adjacent_act Γ configuration.x⁻¹ hprevious
    rwa [hfix, ← configuration.hd] at hedge
  have hcentral := eight_four_terminal_neighbor_center_le_local ctx
    hcenter configuration.d hmiddle
  obtain ⟨hCb, _, _, hCn⟩ := eight_four_edge_star_closure_local ctx w F hbase hcov hsub hformula
  have hCend : C ≤ QAt Γ cp.a' := by
    have hbound := (eight_four_fixed_closure_control_local ctx hcenter w hbranch).1
    dsimp only at hCb hbound
    rw [← hCb] at hbound
    exact hbound
  have hCd : C ≤ GAt Γ configuration.d := hCend.trans
    ((lemma_seven_three h Γ).sylow_and_core cp.a' configuration.d
      ((SevenSix.mem_neighborhood_iff_adjacent Γ).mpr hmiddle) default).2.2
  have hnorm : GAt Γ cp.firstStep ≤ Subgroup.normalizer (C : Set H) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (hCn cp.firstStep).1).mp (hCn cp.firstStep).2
  have hZP := (eight_four_source_nine_shifted_center_action_local ctx hcenter w hbranch
    F hbase hcov hsub hformula configuration hlen).2.1
  have hFP : F next configuration.d ≤ GAt Γ cp.firstStep :=
    ((hsub next configuration.d).trans inf_le_left).trans hZP
  have hDF : D ≤ Subgroup.normalizer (F next configuration.d : Set H) :=
    (le_inf inf_le_right (inf_le_left.trans hCd)).trans
      (eight_four_equivariant_edge_fixed_normalizer Γ F hcov next configuration.d)
  have hcommF : ⁅D, F next configuration.d⁆ ≤ C ⊓ F next configuration.d :=
    le_inf ((Subgroup.commutator_mono inf_le_left le_rfl).trans
      (Subgroup.le_normalizer_iff_commutator_le_left.mp (hFP.trans hnorm)))
      (Subgroup.le_normalizer_iff_commutator_le_right.mp hDF)
  have hDfix : D ≤ Subgroup.centralizer (F next configuration.d : Set H) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp
      (bot_unique (hcommF.trans_eq (eight_four_source_nine_star_inf_fixed_eq_bot_local
        ctx hcenter w hbranch F hbase hcov hsub hformula configuration hlen)))
  have hbound := eight_four_edge_fixed_centralizer_commutator_local ctx
    w F hbase hcov next configuration.d (Γ.adjacent_symm configuration.hadj)
    hcentral D inf_le_right hDfix
  have hR1 := eight_four_source_nine_r1_eq_bot_local ctx hcenter w hbranch
    F hbase hcov hsub hformula configuration hlen
  exact bot_unique ((le_inf le_rfl hbound).trans_eq hR1)


/-- Canonical specializations preserving the given witness, family and data. -/
public theorem eight_four_source_nine_star_inf_center_eq_bot
    {H : Type u} [Group H] [Finite H]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    (ctx : SectionEightContext H S0 S P1 P2)
    (hcenter : ZAt ctx.Γ ctx.criticalPath.firstStep ≤
      CenterAmbient (GAt ctx.Γ ctx.criticalPath.firstStep))
    (w : QuotientModuleWitness
      (GAt ctx.Γ ctx.criticalPath.a)
      (GAt ctx.Γ ctx.criticalPath.a ⊓
        Subgroup.centralizer (ZAt ctx.Γ ctx.criticalPath.a : Set H))
      (ZAt ctx.Γ ctx.criticalPath.a))
    (F : ctx.Γ.Vertex → ctx.Γ.Vertex → Subgroup H)
    (hsub : ∀ d l, F d l ≤ ZAt ctx.Γ d ⊓ GAt ctx.Γ l)
    (hformula : ∀ d l, F d l = ⨆ (g : H)
      (_ : ctx.Γ.act g ctx.criticalPath.a = d ∧
        ctx.Γ.act g ctx.criticalPath.firstStep = l),
      (w.oneJFixedPoints S).conjBy g⁻¹)
    (configuration : EightFourSourceNineData ctx F)
    (hlen : 2 < ctx.criticalPath.length) :
    (⨆ vertex, F vertex ctx.criticalPath.firstStep) ⊓
      ZAt ctx.Γ configuration.d = ⊥ := by
  exact eight_four_source_nine_star_inf_center_eq_bot_local ctx.toLocalContext hcenter w F hsub hformula configuration.toLocal hlen

public theorem eight_four_source_nine_star_inf_fixed_eq_bot
    {H : Type u} [Group H] [Finite H]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    (ctx : SectionEightContext H S0 S P1 P2)
    (hcenter : ZAt ctx.Γ ctx.criticalPath.firstStep ≤
      CenterAmbient (GAt ctx.Γ ctx.criticalPath.firstStep))
    (w : QuotientModuleWitness
      (GAt ctx.Γ ctx.criticalPath.a)
      (GAt ctx.Γ ctx.criticalPath.a ⊓
        Subgroup.centralizer (ZAt ctx.Γ ctx.criticalPath.a : Set H))
      (ZAt ctx.Γ ctx.criticalPath.a))
    (hbranch : (Subgroup.normalClosure
      ((w.oneJFixedPoints S).subgroupOf (GAt ctx.Γ ctx.criticalPath.firstStep) :
        Set (GAt ctx.Γ ctx.criticalPath.firstStep))).map
          (GAt ctx.Γ ctx.criticalPath.firstStep).subtype ≠ w.oneJFixedPoints S)
    (F : ctx.Γ.Vertex → ctx.Γ.Vertex → Subgroup H)
    (hbase : F ctx.criticalPath.a ctx.criticalPath.firstStep = w.oneJFixedPoints S)
    (hcov : ∀ g d l, F (ctx.Γ.act g d) (ctx.Γ.act g l) = (F d l).conjBy g⁻¹)
    (hsub : ∀ d l, F d l ≤ ZAt ctx.Γ d ⊓ GAt ctx.Γ l)
    (hformula : ∀ d l, F d l = ⨆ (g : H)
      (_ : ctx.Γ.act g ctx.criticalPath.a = d ∧
        ctx.Γ.act g ctx.criticalPath.firstStep = l),
      (w.oneJFixedPoints S).conjBy g⁻¹)
    (configuration : EightFourSourceNineData ctx F)
    (hlen : 2 < ctx.criticalPath.length) :
    (⨆ vertex, F vertex ctx.criticalPath.firstStep) ⊓
      F (ctx.Γ.act configuration.y⁻¹ ctx.criticalPath.a') configuration.d = ⊥ := by
  exact eight_four_source_nine_star_inf_fixed_eq_bot_local ctx.toLocalContext hcenter w hbranch F hbase hcov hsub hformula configuration.toLocal hlen

public theorem eight_four_source_nine_r1_eq_bot
    {H : Type u} [Group H] [Finite H]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    (ctx : SectionEightContext H S0 S P1 P2)
    (hcenter : ZAt ctx.Γ ctx.criticalPath.firstStep ≤
      CenterAmbient (GAt ctx.Γ ctx.criticalPath.firstStep))
    (w : QuotientModuleWitness
      (GAt ctx.Γ ctx.criticalPath.a)
      (GAt ctx.Γ ctx.criticalPath.a ⊓
        Subgroup.centralizer (ZAt ctx.Γ ctx.criticalPath.a : Set H))
      (ZAt ctx.Γ ctx.criticalPath.a))
    (hbranch : (Subgroup.normalClosure
      ((w.oneJFixedPoints S).subgroupOf (GAt ctx.Γ ctx.criticalPath.firstStep) :
        Set (GAt ctx.Γ ctx.criticalPath.firstStep))).map
          (GAt ctx.Γ ctx.criticalPath.firstStep).subtype ≠ w.oneJFixedPoints S)
    (F : ctx.Γ.Vertex → ctx.Γ.Vertex → Subgroup H)
    (hbase : F ctx.criticalPath.a ctx.criticalPath.firstStep = w.oneJFixedPoints S)
    (hcov : ∀ g d l, F (ctx.Γ.act g d) (ctx.Γ.act g l) = (F d l).conjBy g⁻¹)
    (hsub : ∀ d l, F d l ≤ ZAt ctx.Γ d ⊓ GAt ctx.Γ l)
    (hformula : ∀ d l, F d l = ⨆ (g : H)
      (_ : ctx.Γ.act g ctx.criticalPath.a = d ∧
        ctx.Γ.act g ctx.criticalPath.firstStep = l),
      (w.oneJFixedPoints S).conjBy g⁻¹)
    (configuration : EightFourSourceNineData ctx F)
    (hlen : 2 < ctx.criticalPath.length) :
    let next := ctx.Γ.act configuration.y⁻¹ ctx.criticalPath.a'
    let C := ⨆ vertex, F vertex ctx.criticalPath.firstStep
    ⁅C ⊓ GAt ctx.Γ next, ZAt ctx.Γ next⁆ ⊓ F next configuration.d = ⊥ := by
  exact eight_four_source_nine_r1_eq_bot_local ctx.toLocalContext hcenter w hbranch F hbase hcov hsub hformula configuration.toLocal hlen

public theorem eight_four_source_nine_restricted_commutation
    {H : Type u} [Group H] [Finite H]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    (ctx : SectionEightContext H S0 S P1 P2)
    (hcenter : ZAt ctx.Γ ctx.criticalPath.firstStep ≤
      CenterAmbient (GAt ctx.Γ ctx.criticalPath.firstStep))
    (w : QuotientModuleWitness
      (GAt ctx.Γ ctx.criticalPath.a)
      (GAt ctx.Γ ctx.criticalPath.a ⊓
        Subgroup.centralizer (ZAt ctx.Γ ctx.criticalPath.a : Set H))
      (ZAt ctx.Γ ctx.criticalPath.a))
    (hbranch : (Subgroup.normalClosure
      ((w.oneJFixedPoints S).subgroupOf (GAt ctx.Γ ctx.criticalPath.firstStep) :
        Set (GAt ctx.Γ ctx.criticalPath.firstStep))).map
          (GAt ctx.Γ ctx.criticalPath.firstStep).subtype ≠ w.oneJFixedPoints S)
    (F : ctx.Γ.Vertex → ctx.Γ.Vertex → Subgroup H)
    (hbase : F ctx.criticalPath.a ctx.criticalPath.firstStep = w.oneJFixedPoints S)
    (hcov : ∀ g d l, F (ctx.Γ.act g d) (ctx.Γ.act g l) = (F d l).conjBy g⁻¹)
    (hsub : ∀ d l, F d l ≤ ZAt ctx.Γ d ⊓ GAt ctx.Γ l)
    (hformula : ∀ d l, F d l = ⨆ (g : H)
      (_ : ctx.Γ.act g ctx.criticalPath.a = d ∧
        ctx.Γ.act g ctx.criticalPath.firstStep = l),
      (w.oneJFixedPoints S).conjBy g⁻¹)
    (configuration : EightFourSourceNineData ctx F)
    (hlen : 2 < ctx.criticalPath.length) :
    let next := ctx.Γ.act configuration.y⁻¹ ctx.criticalPath.a'
    let C := ⨆ vertex, F vertex ctx.criticalPath.firstStep
    ⁅C ⊓ GAt ctx.Γ next, ZAt ctx.Γ next⁆ = ⊥ := by
  exact eight_four_source_nine_restricted_commutation_local ctx.toLocalContext hcenter w hbranch F hbase hcov hsub hformula configuration.toLocal hlen

end Stellmacher.SectionEight
