module
public import Stellmacher.SectionNine.NineTenLongDistanceExclusion
public import Stellmacher.SectionNine.NineTenNormalIntersection
public import Stellmacher.SectionNine.NineTenFirstModuleDistanceTwo
public import Stellmacher.SectionNine.NineTenNeighborhoodDistanceTwoContainment
public import Stellmacher.SectionNine.NineTenGoodGeneratingNeighbor
public import Stellmacher.SectionNine.NineTenGoodNeighborSupport
public import Stellmacher.SectionNine.NineTenExcludedCenterLayer
public import Stellmacher.SectionNine.NineTenResidualNeighborhoodEscape
/-!
# The original distance-five packet forces the terminal center into the residual layer

Retain both original geometric extraction packets at length five. Define
W as the literal first distance-two neighborhood, Q=O₂(E_first), and C as
the commutator preimage of E_first modulo first V. Then the terminal center
lies in [W,Q]C. This eliminates the final excluded-center case of (9.10).

The actual terminal classification supplies a good generating neighbor.
Its neighborhood centralizes the third module and lies in the terminal
stabilizer. The original selected quotient action and canonical factor
therefore supply its displacement bound. Exact neighborhood inclusions,
the retained actor, and its two-group property meet every hypothesis of
the excluded-center layer theorem. If the terminal center were absent,
that theorem would give [W,Q]≤C. Source (11), transported by the same
residual conjugator, puts C∩V_third in V_first, contradicting the actual
residual-neighborhood escape theorem (12).

All classification data, coatom indices, graph vertices, and dependent
action instances are derived on the supplied path. The contained-center
contradiction is a separate final input. Source: Stellmacher (9.10),
printed pp.57–59, especially the final paragraph on p.59.
-/

namespace Stellmacher.SectionNine
open Later SectionsFiveToSeven CosetGraphContext SevenSix
universe u

public theorem nine_ten_five_terminal_center_le_residual_neighborhood
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : ctx.criticalPath.length = 5)
    (hterminalNot : ¬ ZAt ctx.Γ ctx.criticalPath.a' ≤ VAt ctx.Γ ctx.criticalPath.firstStep)
    (hfirstNot : ¬ ZAt ctx.Γ ctx.criticalPath.firstStep ≤ VAt ctx.Γ ctx.criticalPath.a')
    (neighbor second : ctx.Γ.Vertex) (actor : G) (E A0 : Subgroup G)
    (data : NineThreeGeometricData ctx.Γ ctx.criticalPath.firstStep second
      (VAt ctx.Γ ctx.criticalPath.a') E A0 actor)
    (hsecond : IsCriticalPathOffset ctx.Γ ctx.criticalPath 2 second)
    (hactorNeighbor : actor ∈ ZAt ctx.Γ neighbor)
    (hactorComm : twoResidualIn E ≤ ⁅twoResidualIn E, Subgroup.zpowers actor⁆)
    (hnew : ctx.Γ.act data.x⁻¹ second = ctx.criticalPath.a)
    (hneighbor : neighbor ∈ neighborhood ctx.Γ ctx.criticalPath.a')
    (hcenters : ⁅ZAt ctx.Γ ctx.criticalPath.a, ZAt ctx.Γ neighbor⁆ ≠ ⊥)
    (firstActor : G) (firstE firstA0 : Subgroup G)
    (firstData : NineThreeGeometricData ctx.Γ ctx.criticalPath.a'
      (ctx.criticalPath.path ⟨ctx.criticalPath.length - 1, Nat.lt_succ_of_le (Nat.sub_le _ _)⟩)
      (VAt ctx.Γ ctx.criticalPath.firstStep) firstE firstA0 firstActor)
    (hfirstNew : ctx.Γ.act firstData.x⁻¹
      (ctx.criticalPath.path ⟨ctx.criticalPath.length - 1, Nat.lt_succ_of_le (Nat.sub_le _ _)⟩) =
        neighbor)
    (hfirstActors : ∀ b : G, b ∈ VAt ctx.Γ ctx.criticalPath.firstStep → b ∉ firstA0 →
      twoResidualIn firstE ≤ ⁅twoResidualIn firstE, Subgroup.zpowers b⁆) :
    let W := DistanceTwoNeighborhoodV ctx.Γ ctx.criticalPath.firstStep
    let Q := twoCoreIn (EAt ctx.Γ ctx.criticalPath.firstStep)
    let C := Subgroup.commutatorPreimage W (EAt ctx.Γ ctx.criticalPath.firstStep)
      (VAt ctx.Γ ctx.criticalPath.firstStep)
    ZAt ctx.Γ ctx.criticalPath.a' ≤ ⁅W,Q⁆ ⊔ C := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  have hlength : cp.length = 5 := hb
  have hlong : 4 < cp.length := by omega
  have hshort : 1 < cp.length := by omega
  let third := cp.path ⟨3,by omega⟩
  let penultimate := cp.path ⟨cp.length-1,Nat.lt_succ_of_le (Nat.sub_le _ _)⟩
  let predecessor := Γ.act data.x⁻¹ third
  let P := GAt Γ cp.firstStep
  let V := VAt Γ cp.firstStep
  let W := DistanceTwoNeighborhoodV Γ cp.firstStep
  let Ef := EAt Γ cp.firstStep
  let Q := twoCoreIn Ef
  let C := Subgroup.commutatorPreimage W Ef V
  let M := ⁅W,Q⁆ ⊔ C
  change ZAt Γ cp.a' ≤ M
  by_contra hnot
  have hthird : IsCriticalPathOffset Γ cp 3 third := ⟨⟨3,by omega⟩,rfl,rfl⟩
  obtain ⟨_, hactorGeometry, hactorNotCore, _, hxFirst⟩ :=
    nine_ten_prescribed_actor_geometry ctx.toLocalContext third second neighbor
      hthird hneighbor actor E A0 data hactorNeighbor hactorComm
  have hindex : QuotientCardEq V (V ⊓ GAt Γ neighbor) 2 := by
    change Nat.card V = 2 * Nat.card (V ⊓ GAt Γ neighbor : Subgroup G)
    rw [←hfirstNew,←firstData.coatom_eq]
    exact firstData.coatom_card
  obtain ⟨hUcard,hmodel,hIcard⟩ := nine_ten_terminal_wreath_classification ctx hlong
    hterminalNot hfirstNot neighbor second actor E A0 data hsecond hactorNeighbor
      hactorComm hnew hneighbor hcenters firstActor firstE firstA0 firstData hfirstNew hfirstActors
  obtain ⟨lambda,hlambda,hgenerate,htriple⟩ := nine_ten_exists_good_generating_neighbor
    ctx hb hUcard hmodel hIcard neighbor hneighbor hterminalNot hindex actor
      hactorNeighbor hactorNotCore
  let L := GeneratedNeighborhoodV Γ lambda
  have hVW : V ≤ W := nine_ten_first_module_le_distance_two_neighborhood ctx hlong
  have hLW : L ≤ W := nine_ten_neighborhood_le_distance_two_of_self_le Γ
    cp.firstStep lambda hlambda hVW
  obtain ⟨hLthird,hLP⟩ := nine_ten_good_neighbor_neighborhood_support
    ctx hb hUcard hmodel hIcard lambda hlambda htriple
  have hgeometry := nine_ten_distance_two_neighborhood_geometry ctx.toLocalContext hlong
  have hZaV : ZAt Γ cp.a ≤ V :=
    nine_seven_neighbor_center_le_module Γ (Γ.adjacent_symm cp.firstStep_adj)
  have hLZa : L ≤ Subgroup.centralizer (ZAt Γ cp.a : Set G) :=
    (hLW.trans hgeometry.2.2.1).trans (Subgroup.centralizer_le hZaV)
  have hthirdPen : Γ.adjacent third penultimate := by
    have hpen : (⟨3,by omega⟩ : Fin cp.length).succ =
        ⟨cp.length-1,Nat.lt_succ_of_le (Nat.sub_le _ _)⟩ := by
      apply Fin.ext
      simp only [Fin.val_succ]
      omega
    have hh := cp.path_adj ⟨3,by omega⟩
    rwa [hpen] at hh
  have hLpen : ⁅L,ZAt Γ penultimate⁆ = ⊥ :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
      (hLthird.trans (Subgroup.centralizer_le
        (nine_seven_neighbor_center_le_module Γ hthirdPen)))
  obtain ⟨selected,hselected,_,hnotCore,hN,hQuotient,action,hformula,hkernel,hyp,
    hfactor,hsupport⟩ := nine_ten_selected_factor_support
      ctx hshort hterminalNot hfirstNot neighbor second actor E A0 data hnew hneighbor hcenters
        firstActor firstE firstA0 firstData hfirstNew hfirstActors
  let _ := hN
  let _ := hQuotient
  let D : Subgroup action.range :=
    ⁅SectionOne.oddCore action.range,Subgroup.zpowers (action.rangeRestrict selected)⁆ ⊔
      Subgroup.zpowers (action.rangeRestrict selected)
  have hselectedD : action.rangeRestrict selected ∈ D :=
    (show Subgroup.zpowers (action.rangeRestrict selected) ≤ D from le_sup_right)
      (Subgroup.mem_zpowers _)
  let R := ⁅VAt Γ cp.a',Subgroup.zpowers (selected:G)⁆
  have hbound := nine_ten_subgroup_displacement_bound_of_initial_center_centralization
    ctx hlong L hLZa hLP neighbor hneighbor hLpen selected hselected hnotCore
      action hformula hkernel hyp D hfactor hselectedD hsupport
  have hRnormalZ : R ≤ Subgroup.normalizer (ZAt Γ cp.a' : Set G) :=
    (Subgroup.le_normalizer_iff_commutator_le_left.mp
      ((Subgroup.zpowers_le.mpr selected.property).trans (stabilizer_le_normalizer_v Γ cp.a'))).trans
        (((nine_seven_module_le_own_core ctx.toLocalContext hshort cp.a').trans
          (show QAt Γ cp.a' ≤ GAt Γ cp.a' from by
            rw [QAt,q,Γ.twoCoreAt_def]
            exact Subgroup.map_subtype_le _)).trans (stabilizer_le_normalizer_z Γ cp.a'))
  obtain ⟨alignment,_,hterminal⟩ := lemma_seven_five_endpoint_alignment
    ctx.sectionSeven Γ cp ctx.commutator_eq
  have hZcard : Nat.card (ZAt Γ cp.a') = 2 :=
    (nine_next_center_commutator_and_kernel ctx hshort cp.a' ⟨alignment,hterminal⟩).1
  have hneighborU : ZAt Γ neighbor ≤ VAt Γ cp.a' :=
    nine_seven_neighbor_center_le_module Γ
      ((mem_neighborhood_iff_adjacent Γ).mp hneighbor)
  have hactorTwo : IsPGroup 2 (Subgroup.zpowers actor) :=
    nine_seven_subgroup_isTwoGroup_of_le_vertex_core Γ cp.a' (Subgroup.zpowers actor)
      ((Subgroup.zpowers_le.mpr (hneighborU hactorNeighbor)).trans
        (nine_seven_module_le_own_core ctx.toLocalContext hshort cp.a'))
  have hcommC : ⁅W,Q⁆ ≤ C := nine_ten_excluded_center_residual_le_normal_layer
    ctx hlong lambda neighbor hlambda hLW hVW hgenerate ⟨actor,hactorGeometry.1⟩
      hactorNeighbor hactorNotCore hactorTwo R C M rfl rfl hbound.2 hRnormalZ hbound.1 hZcard hnot
  have hMC : M ≤ C := sup_le hcommC le_rfl
  have hWV : W ≤ Subgroup.normalizer (V : Set G) :=
    hgeometry.2.2.1.trans (Subgroup.centralizer_le_normalizer _)
  have hPE : P ≤ Subgroup.normalizer (Ef : Set G) := by
    have hEeq : Ef=twoResidualIn P := Γ.twoResidualAt_def cp.firstStep
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer (hEeq ▸ twoResidualIn_le P)).mp
      (hEeq ▸ twoResidualIn_normal P)
  have hPC : P ≤ Subgroup.normalizer (C : Set G) :=
    Subgroup.commutatorPreimage_normalized W Ef V P hWV hgeometry.2.2.2.1 hPE
      (stabilizer_le_normalizer_v Γ cp.firstStep)
  have hCE : ⁅C,Ef⁆ ≤ V := Subgroup.commutator_commutatorPreimage_le W Ef V hWV
  have hCpred : C ⊓ VAt Γ predecessor ≤ V :=
    nine_ten_normal_predecessor_intersection_le_first ctx hlong hterminalNot
      neighbor second actor E A0 data hactorNeighbor hactorComm hneighbor hindex C hPC hCE
  have hxP : data.x ∈ P := by simpa only [inv_inv] using P.inv_mem hxFirst
  let equiv := MulAut.conj data.x
  have hCmap : C.map equiv.toMonoidHom = C :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (hPC hxP)
  have hVmap : V.map equiv.toMonoidHom = V :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp ((stabilizer_le_normalizer_v Γ cp.firstStep) hxP)
  have hthirdMap : (VAt Γ third).map equiv.toMonoidHom = VAt Γ predecessor := by
    change (v Γ third).map (MulAut.conj data.x).toMonoidHom = v Γ (Γ.act data.x⁻¹ third)
    rw [v_act,inv_inv]
  have hCthird : C ⊓ VAt Γ third ≤ V := by
    apply (Subgroup.map_le_map_iff_of_injective (f:=equiv.toMonoidHom) equiv.injective).mp
    rw [Subgroup.map_inf _ _ _ equiv.injective,hCmap,hthirdMap,hVmap]
    exact hCpred
  exact nine_ten_residual_neighborhood_intersection_not_le_first ctx hb hUcard hmodel hIcard
    M le_sup_left ((inf_le_inf_right (VAt Γ third) hMC).trans hCthird)

end Stellmacher.SectionNine
