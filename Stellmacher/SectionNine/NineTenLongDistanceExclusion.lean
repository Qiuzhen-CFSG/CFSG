module
public import Stellmacher.SectionNine.NineTenTerminalClassification
public import Stellmacher.SectionNine.NineTenReversedConfiguration
public import Stellmacher.SectionNine.NineTenSubgroupDisplacementBound
public import Stellmacher.SectionNine.NineTenSuppliedCoatomCentralization
public import Stellmacher.SectionNine.NineTenCenterNeighborhoodIndex
public import Stellmacher.SectionNine.NineTenLongNeighborhoodCenterExclusion
public import Stellmacher.SectionNine.NineTenCenterCommutatorCyclic
public import Stellmacher.SectionNine.NineThreeOrbitEdgeCoreCentralizer

/-!
# The long-distance exclusion in Stellmacher (9.10)

Retain both normalized geometric extraction packets on one critical path.
The distance is at most five. At greater distance the source's exact
distance-two W is abelian, has penultimate-stabilizer intersection of index
at most two, and excludes the terminal center by predecessor noncommutation.

On the same supplied reversed critical path, (9.9) makes the predecessor
intersection with the penultimate stabilizer centralize its center; the
intersection therefore lies in the penultimate core and terminal stabilizer.
The retained canonical support bounds its actor displacement by R joined
with the terminal center. W-invariance and the excluded terminal center
improve this to R in first V. The actual (9.4) then puts this at-least-half
subgroup in first V, contrary to actual (9.7).

This proves Stellmacher (9.10)(7)--(8), printed p.58. The final distance-five
contradiction in (9)--(12) remains a separate result. All witnesses and actions
in this proof belong to the original two-extraction packet. The final wrapper
obtains that packet from one normalization and returns the bound to the original
path using preservation of length.
-/
namespace Stellmacher.SectionNine
open Later SectionsFiveToSeven CosetGraphContext SevenSix
open scoped Pointwise
universe u

private theorem joined_line_intersection_le
    {G : Type u} [Group G] [Finite G]
    (R Z W : Subgroup G) (hRW : R ≤ W)
    (hRZ : R ≤ Subgroup.normalizer (Z : Set G))
    (hZcard : Nat.card Z = 2) (hZnot : ¬ Z ≤ W) :
    (R ⊔ Z) ⊓ W ≤ R := by
  have hWZ : W ⊓ Z = ⊥ := by
    by_contra hnonzero
    have heq : W ⊓ Z = Z := Subgroup.eq_of_le_of_card_ge inf_le_right (by
      rw [hZcard]
      exact (Subgroup.one_lt_card_iff_ne_bot _).mpr hnonzero)
    exact hZnot (heq ▸ inf_le_left)
  intro x hx
  have hm : x ∈ (R : Set G) * (Z : Set G) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right R Z hRZ]
    exact hx.1
  obtain ⟨r, hr, z, hz, rfl⟩ := hm
  have hzW : z ∈ W := by
    simpa only [inv_mul_cancel_left] using W.mul_mem (W.inv_mem (hRW hr)) hx.2
  have hzOne : z = 1 := by
    have hh : z ∈ W ⊓ Z := ⟨hzW, hz⟩
    rwa [hWZ, Subgroup.mem_bot] at hh
  change r ∈ R at hr
  simpa only [hzOne, mul_one] using hr

public theorem nine_ten_length_le_five_of_extraction
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : 4 < ctx.criticalPath.length)
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
    ctx.criticalPath.length ≤ 5 := by
  by_contra hlengthBound
  have hlong : 5 < ctx.criticalPath.length := by omega
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  have hlength : 4 < cp.length := hb
  have hshort : 1 < cp.length := by omega
  let third := cp.path ⟨3, by omega⟩
  let predecessor := Γ.act data.x⁻¹ third
  let penultimate := cp.path ⟨cp.length - 1, Nat.lt_succ_of_le (Nat.sub_le _ _)⟩
  let K := VAt Γ predecessor ⊓ GAt Γ penultimate
  let W := DistanceTwoNeighborhoodV Γ cp.firstStep
  have hthird : IsCriticalPathOffset Γ cp 3 third := ⟨⟨3, by omega⟩, rfl, rfl⟩
  obtain ⟨hdistance, hactorGeometry, hactorNotCore, hxComm, hxFirst⟩ :=
    nine_ten_prescribed_actor_geometry ctx.toLocalContext third second neighbor
      hthird hneighbor actor E A0 data hactorNeighbor hactorComm
  have hfix : Γ.act data.x⁻¹ cp.firstStep = cp.firstStep :=
    (Set.ext_iff.mp (Γ.stabilizer_def cp.firstStep) data.x⁻¹).mp hxFirst
  have hpredDistance : Γ.distance cp.firstStep predecessor = 2 := by
    have hh := distance_act Γ data.x⁻¹ cp.firstStep third
    rw [hfix] at hh
    rw [hh, Γ.distance_symm]
    exact hdistance
  have hpredW : VAt Γ predecessor ≤ W := v_le_distance_two_neighborhood Γ hpredDistance
  have hKW : K ≤ W := inf_le_left.trans hpredW
  have hnoncomm := nine_ten_predecessor_noncommutation ctx hb hterminalNot hfirstNot
    neighbor second actor E A0 data hsecond hactorNeighbor hactorComm hnew hneighbor
      hcenters firstActor firstE firstA0 firstData hfirstNew hfirstActors
  have hnotZ : ¬ ZAt Γ cp.a' ≤ W :=
    nine_ten_terminal_center_not_le_distance_two_neighborhood ctx hlong predecessor hpredW hnoncomm
  have hgeometry := nine_ten_distance_two_neighborhood_geometry ctx.toLocalContext hb
  have hWtwo : IsPGroup 2 W := nine_seven_subgroup_isTwoGroup_of_le_vertex_core Γ
    cp.firstStep W hgeometry.1
  have hKtwo : IsPGroup 2 K := hWtwo.to_le hKW
  obtain ⟨hcritical, hcenterComm, path, hstart, hend, _, _, hadj⟩ :=
    nine_ten_reversed_supplied_path ctx hb neighbor second actor E A0 data
      hsecond hnew hneighbor hcenters hnoncomm
  have hKcenter : ⁅K, ZAt Γ penultimate⁆ = ⊥ := by
    rw [Subgroup.commutator_comm]
    exact nine_ten_supplied_initial_center_centralizes_terminal_intersection ctx (by omega)
      penultimate predecessor hcritical hcenterComm path hstart hend hadj
  obtain ⟨alignment, halign, hterminal⟩ := lemma_seven_five_endpoint_alignment
    ctx.sectionSeven Γ cp ctx.commutator_eq
  have hpenOrbit : IsConjugateVertex Γ cp.a penultimate := ⟨alignment, halign⟩
  have hKcore : K ≤ QAt Γ penultimate :=
    nine_three_orbit_pgroup_centralizer ctx.toLocalContext penultimate hpenOrbit K hKtwo
      inf_le_right (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hKcenter)
  have hKP : K ≤ GAt Γ cp.a' := hKcore.trans
    ((lemma_seven_three ctx.sectionSeven Γ).sylow_and_core penultimate cp.a'
      ((mem_neighborhood_iff_adjacent Γ).mpr
        (nine_five_penultimate_adjacent ctx.toLocalContext)) default).2.2
  have hpred := (nine_ten_extracted_predecessor_alternative Γ cp (by omega)
    second actor E A0 data hsecond hnew).1
  have hKnear : K ≤ GeneratedNeighborhoodV Γ cp.a := inf_le_left.trans
    (nine_eight_v_le_generated_neighborhood Γ
      ((mem_neighborhood_iff_adjacent Γ).mpr hpred))
  obtain ⟨selected, hselected, _, hnotCore, hN, hQuotient, action, hformula, hkernel, hyp,
    hfactor, hsupport⟩ := nine_ten_selected_factor_support
    ctx hshort hterminalNot hfirstNot neighbor second actor E A0 data hnew hneighbor hcenters
      firstActor firstE firstA0 firstData hfirstNew hfirstActors
  let _ := hN
  let _ := hQuotient
  let D : Subgroup action.range :=
    ⁅SectionOne.oddCore action.range, Subgroup.zpowers (action.rangeRestrict selected)⁆ ⊔
      Subgroup.zpowers (action.rangeRestrict selected)
  have hselectedD : action.rangeRestrict selected ∈ D :=
    (show Subgroup.zpowers (action.rangeRestrict selected) ≤ D from le_sup_right)
      (Subgroup.mem_zpowers _)
  let R := ⁅VAt Γ cp.a', Subgroup.zpowers (selected : G)⁆
  have hbound := nine_ten_subgroup_displacement_bound ctx hb K hKnear hKP neighbor hneighbor
    hKcenter selected hselected hnotCore action hformula hkernel hyp D hfactor hselectedD hsupport
  have hRliteral : ⁅ZAt Γ cp.a, VAt Γ cp.a'⁆ = R :=
    nine_ten_initial_center_commutator_eq_cyclic ctx hshort selected hselected hnotCore
  have hWR : W ≤ Subgroup.centralizer
      ((⁅ZAt Γ cp.a, VAt Γ cp.a'⁆ : Subgroup G) : Set G) := by
    rw [hRliteral]
    exact hgeometry.2.2.1.trans (Subgroup.centralizer_le hbound.2)
  obtain ⟨hUcard, hmodel, hIcard⟩ := nine_ten_terminal_wreath_classification ctx hb
    hterminalNot hfirstNot neighbor second actor E A0 data hsecond hactorNeighbor
      hactorComm hnew hneighbor hcenters firstActor firstE firstA0 firstData hfirstNew hfirstActors
  have hcoatom : QuotientCardEq (VAt Γ cp.a') (VAt Γ cp.a' ⊓ GAt Γ cp.a) 2 := by
    change Nat.card (VAt Γ cp.a') = 2 * Nat.card (VAt Γ cp.a' ⊓ GAt Γ cp.a : Subgroup G)
    rw [← hnew, ← data.coatom_eq]
    exact data.coatom_card
  have hWindex := nine_ten_center_centralizing_two_subgroup_index_le_two ctx (by omega)
    hUcard hmodel hIcard hcoatom W hWtwo hgeometry.2.1 hWR
  have hKindex : (GAt Γ penultimate).relIndex (VAt Γ predecessor) ≤ 2 :=
    (Subgroup.relIndex_le_of_le_right hpredW Subgroup.index_ne_zero_of_finite).trans hWindex
  have hcard : Nat.card (VAt Γ predecessor) ≤ 2 * Nat.card K := by
    have hh := (K.subgroupOf (VAt Γ predecessor)).index_mul_card
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (show K ≤ VAt Γ predecessor from inf_le_left)).toEquiv] at hh
    change K.relIndex (VAt Γ predecessor) * Nat.card K = Nat.card (VAt Γ predecessor) at hh
    have hi : K.relIndex (VAt Γ predecessor) = (GAt Γ penultimate).relIndex
        (VAt Γ predecessor) := Subgroup.inf_relIndex_left _ _
    rw [hi] at hh
    nlinarith
  have hRU : R ≤ VAt Γ cp.a' := Subgroup.le_normalizer_iff_commutator_le_left.mp
    ((Subgroup.zpowers_le.mpr selected.property).trans (stabilizer_le_normalizer_v Γ cp.a'))
  have hRnormalZ : R ≤ Subgroup.normalizer (ZAt Γ cp.a' : Set G) := hRU.trans
    ((nine_seven_module_le_own_core ctx.toLocalContext hshort cp.a').trans
      ((show QAt Γ cp.a' ≤ GAt Γ cp.a' from by
        rw [QAt, q, Γ.twoCoreAt_def]
        exact Subgroup.map_subtype_le _).trans (stabilizer_le_normalizer_z Γ cp.a')))
  have hZaW : ZAt Γ cp.a ≤ W := by
    apply le_trans ?_ hpredW
    rw [VAt, v, Γ.vAt_def]
    exact le_sSup ⟨cp.a, (mem_neighborhood_iff_adjacent Γ).mpr (Γ.adjacent_symm hpred), rfl⟩
  have hRWin : R ≤ W := by
    rw [← hRliteral, Subgroup.commutator_comm]
    exact (Subgroup.commutator_mono le_rfl hZaW).trans
      (Subgroup.le_normalizer_iff_commutator_le_right.mp
        ((lemma_seven_four ctx.sectionSeven Γ cp).reverse_containment.2.trans hgeometry.2.2.2.1))
  have hZcard : Nat.card (ZAt Γ cp.a') = 2 :=
    (nine_next_center_commutator_and_kernel ctx hshort cp.a' ⟨alignment, hterminal⟩).1
  have hcommW : ⁅K, Subgroup.zpowers actor⁆ ≤ W :=
    (Subgroup.commutator_mono hKW le_rfl).trans
      (Subgroup.le_normalizer_iff_commutator_le_left.mp
        ((Subgroup.zpowers_le.mpr hactorGeometry.1).trans hgeometry.2.2.2.1))
  have hcommR : ⁅K, Subgroup.zpowers actor⁆ ≤ R :=
    (le_inf ((Subgroup.commutator_mono le_rfl (Subgroup.zpowers_le.mpr hactorNeighbor)).trans
      hbound.1) hcommW).trans
        (joined_line_intersection_le R (ZAt Γ cp.a') W hRWin hRnormalZ hZcard hnotZ)
  have hnot := nine_ten_predecessor_large_subgroup_not_le_first ctx (by omega) third hthird
    data.x⁻¹ hxFirst K inf_le_left hcard
  have hindex : QuotientCardEq (VAt Γ cp.firstStep)
      (VAt Γ cp.firstStep ⊓ GAt Γ neighbor) 2 := by
    change Nat.card (VAt Γ cp.firstStep) =
      2 * Nat.card (VAt Γ cp.firstStep ⊓ GAt Γ neighbor : Subgroup G)
    rw [← hfirstNew, ← firstData.coatom_eq]
    exact firstData.coatom_card
  have hdisplacement := (nine_ten_prescribed_actor_first_transvection ctx hshort hterminalNot
    neighbor hneighbor hindex actor hactorNeighbor hactorNotCore).2
  have hgeneration : ∀ n : Γ.Vertex,
      n ∈ Neighborhood Γ cp.firstStep → n ∈ Neighborhood Γ predecessor →
      (GAt Γ cp.firstStep ⊓ GAt Γ n) ⊔ Subgroup.zpowers actor = GAt Γ cp.firstStep :=
    nine_ten_prescribed_actor_common_neighbor_generation ctx.toLocalContext third second neighbor
      hthird hneighbor actor E A0 data hactorNeighbor
  exact hnot (lemma_nine_four_ambient ctx hshort third hdistance actor hactorGeometry
    data.x⁻¹ hxComm K inf_le_left (hcommR.trans hbound.2) hgeneration hdisplacement)

/-- The critical-distance bound through source (9.10)(8), before excluding five. -/
public theorem nine_ten_length_le_five
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B) :
    ctx.criticalPath.length ≤ 5 := by
  by_cases hb : 3 < ctx.criticalPath.length
  · obtain ⟨cp, hlen, hcomm, hterm, hfirst, neighbor, second, actor, E, A0, data,
      hsecond, hnew, hneighbor, hactor, hcenters, hactorComm,
      firstActor, firstE, firstA0, firstData, hfirstNew, hfirstActors, _⟩ :=
      nine_ten_normalized_reversed_configuration ctx hb
    let shifted : AmbientSectionNineContext H S0 S P1 P2 embedding T A B :=
      {ctx with criticalPath := cp, commutator_eq := hcomm}
    have hlength : 4 < cp.length := by
      have hfive := nine_ten_length_ge_five ctx.toLocalContext hb
      change 5 ≤ ctx.criticalPath.length at hfive
      omega
    have hbound := nine_ten_length_le_five_of_extraction shifted hlength hterm hfirst
      neighbor second actor E A0 data hsecond hactor hactorComm hnew hneighbor
        hcenters firstActor firstE firstA0 firstData hfirstNew hfirstActors
    change cp.length ≤ 5 at hbound
    omega
  · omega

end Stellmacher.SectionNine
