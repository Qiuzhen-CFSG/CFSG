module

public import Stellmacher.SectionNine.NineFivePenultimateCoreEscapeReduction
public import Stellmacher.SectionNine.NineFivePenultimateResidualGeneration
public import Stellmacher.SectionThree.ResidualImageOddPGroup
public import Theory.GroupTheory.OddIndexCoreCentralizes

/-!
# The coprime reduction for penultimate core nontriviality

If the penultimate residual core centralizes the actual commutator R,
then R lies in the penultimate center Zp. Indeed, the elementary subgroup
M = R join Zp is normalized by the penultimate residual, is contained in
Qp, and has residual commutator contained in Zp. The normal two-core has
odd index by (3.3), and (7.5)(c) makes the residual fixed subgroup trivial.
The coprime collapse therefore gives M ≤ Zp.

All local containment, odd-index, and residual-join inputs are discharged
from the original context and initial center order four. The remaining
centrality assumption is explicit: this is not the requested nontriviality
theorem, which still requires excluding R ≤ Zp for the actual transvection.

Source: Stellmacher (9.5), printed pp.52–53/PDF pp.42–43 of
`refs/files/stellmacher-n-group.pdf`.
-/

open scoped commutatorElement IsMulCommutative

namespace Stellmacher.SectionNine

open Later SectionsFiveToSeven CosetGraphContext SevenSix

universe u

public theorem nine_five_vertex_residual_core_odd_index
    {G : Type u} [Group G] [Finite G] {T A B : Subgroup G}
    (ctx : SectionNineLocalContext G T A B)
    (vertex neighbor : ctx.Γ.Vertex) (hadj : ctx.Γ.adjacent vertex neighbor) :
    Odd ((twoCoreIn (EAt ctx.Γ vertex)).subgroupOf (EAt ctx.Γ vertex)).index := by
  let localGroup := stabilizer ctx.Γ vertex
  let sylow : Sylow 2 (localGroup ⊓ stabilizer ctx.Γ neighbor : Subgroup G) := default
  let edgeSylow := sylowTwoAmbient (localGroup ⊓ stabilizer ctx.Γ neighbor) sylow
  have hdata := edge_sectionThree_data ctx.sectionSeven ctx.Γ
    ((mem_neighborhood_iff_adjacent ctx.Γ).mpr hadj) sylow
  obtain ⟨prime, hprime, hodd, himage⟩ := SectionThree.pSet_residual_image_is_odd_pGroup
    edgeSylow hdata.1 localGroup hdata.2.1 hdata.2.2.2.1
    (QuotientGroup.mk' (pCore 2 localGroup)) (by rw [QuotientGroup.ker_mk'])
  let _ : Fact prime.Prime := ⟨hprime⟩
  have himageOdd : Odd (Nat.card ((twoResidualSubgroup localGroup).map
      (QuotientGroup.mk' (pCore 2 localGroup)))) := by
    obtain ⟨exponent, hcard⟩ := himage.exists_card_eq
    rw [hcard]
    exact hodd.pow
  rw [EAt, CosetGraphContext.e, ctx.Γ.twoResidualAt_def]
  rw [residual_core_eq_inter_core]
  change Odd ((twoResidualIn localGroup ⊓ twoCoreIn localGroup).relIndex
    (twoResidualIn localGroup))
  rw [Subgroup.inf_relIndex_left]
  change Odd (((pCore 2 localGroup).map localGroup.subtype).relIndex
    ((twoResidualSubgroup localGroup).map localGroup.subtype))
  rw [Subgroup.relIndex_map_map_of_injective _ _ localGroup.subtype_injective]
  have hcard := Subgroup.relIndex_ker (twoResidualSubgroup localGroup)
    (QuotientGroup.mk' (pCore 2 localGroup))
  rw [QuotientGroup.ker_mk'] at hcard
  rwa [hcard]

public theorem nine_five_terminal_module_le_penultimate_core
    {G : Type u} [Group G] [Finite G] {T A B : Subgroup G}
    (ctx : SectionNineLocalContext G T A B)
    (hb : 1 < ctx.criticalPath.length) :
    VAt ctx.Γ ctx.criticalPath.a' ≤ QAt ctx.Γ
      (ctx.criticalPath.path ⟨ctx.criticalPath.length - 1,
        Nat.lt_succ_of_le (Nat.sub_le _ _)⟩) := by
  have hodd := (lemma_seven_five ctx.sectionSeven ctx.Γ ctx.criticalPath
    ctx.commutator_eq).odd_distance
  have hthree : 3 ≤ ctx.criticalPath.length := by
    obtain ⟨half, hhalf⟩ := hodd
    omega
  rw [VAt, v, ctx.Γ.vAt_def]
  apply sSup_le
  rintro center ⟨neighbor, hneighbor, rfl⟩
  have hdist := neighbor_reverse_path_distance_le ctx.Γ ctx.criticalPath neighbor
    (ctx.criticalPath.length - 1) ctx.criticalPath.length (Nat.sub_le _ _) le_rfl
    (by simpa [ctx.criticalPath.path_end] using (ctx.Γ.adjacent_symm
      ((mem_neighborhood_iff_adjacent ctx.Γ).mp hneighbor)))
  exact critical_minimality ctx.Γ ctx.criticalPath (lt_of_le_of_lt hdist (by omega))

public theorem nine_five_penultimate_core_centralizes_imp_le_center
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hfour : Nat.card (ZAt ctx.Γ ctx.criticalPath.a) = 4)
    (hb : 1 < ctx.criticalPath.length) (prev : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath
      (ctx.criticalPath.length - 2) prev)
    (actor : G)
    (hactor : actor ∈ VAt ctx.Γ ctx.criticalPath.firstStep ∧
      actor ∉ QAt ctx.Γ ctx.criticalPath.a')
    (hindex : QuotientCardEq
      (⁅VAt ctx.Γ ctx.criticalPath.a', Subgroup.zpowers actor⁆ ⊔
        ZAt ctx.Γ ctx.criticalPath.a') (ZAt ctx.Γ ctx.criticalPath.a') 2)
    (hcontain : ⁅VAt ctx.Γ ctx.criticalPath.a', Subgroup.zpowers actor⁆ ≤
      VAt ctx.Γ prev)
    (hcentral : ⁅twoCoreIn (EAt ctx.Γ
      (ctx.criticalPath.path ⟨ctx.criticalPath.length - 1,
        Nat.lt_succ_of_le (Nat.sub_le _ _)⟩)),
      ⁅VAt ctx.Γ ctx.criticalPath.a', Subgroup.zpowers actor⁆⁆ = ⊥) :
    ⁅VAt ctx.Γ ctx.criticalPath.a', Subgroup.zpowers actor⁆ ≤
      ZAt ctx.Γ (ctx.criticalPath.path ⟨ctx.criticalPath.length - 1,
        Nat.lt_succ_of_le (Nat.sub_le _ _)⟩) := by
  let penultimate := ctx.criticalPath.path ⟨ctx.criticalPath.length - 1,
    Nat.lt_succ_of_le (Nat.sub_le _ _)⟩
  let residual := ⁅VAt ctx.Γ ctx.criticalPath.a', Subgroup.zpowers actor⁆
  let acting := EAt ctx.Γ penultimate
  let core := twoCoreIn acting
  let center := ZAt ctx.Γ penultimate
  let moduleSubgroup := residual ⊔ center
  have hjoin := nine_five_penultimate_residual_le_join_of_initial_four
    ctx hfour hb prev hpath
  have hinputs := nine_five_transvection_inputs ctx.toLocalContext hb prev actor
    hactor hindex hcontain
  let _ : IsElementaryAbelian 2 (VAt ctx.Γ ctx.criticalPath.a') := hinputs.2.1
  have hresidualV : residual ≤ VAt ctx.Γ ctx.criticalPath.a' :=
    hinputs.2.2.2.2.1.trans inf_le_left
  have hadj := nine_five_penultimate_adjacent ctx.toLocalContext
  have hcenterV : center ≤ VAt ctx.Γ ctx.criticalPath.a' := by
    rw [VAt, v, ctx.Γ.vAt_def]
    exact le_sSup ⟨_, (mem_neighborhood_iff_adjacent ctx.Γ).mpr
      (ctx.Γ.adjacent_symm hadj), rfl⟩
  have hmoduleV : moduleSubgroup ≤ VAt ctx.Γ ctx.criticalPath.a' :=
    sup_le hresidualV hcenterV
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let _ : IsElementaryAbelian 2 (moduleSubgroup.subgroupOf
      (VAt ctx.Γ ctx.criticalPath.a')) := by
    refine { exponent_dvd_p := ?_ }
    apply Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
    intro vector
    apply Subtype.ext
    exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 (VAt ctx.Γ ctx.criticalPath.a')) vector.val
  let _ : IsElementaryAbelian 2 moduleSubgroup := by
    have hm := IsElementaryAbelian.map_subtype
      (p := 2) (K := VAt ctx.Γ ctx.criticalPath.a')
      (H := moduleSubgroup.subgroupOf (VAt ctx.Γ ctx.criticalPath.a'))
    rwa [Subgroup.map_subgroupOf_eq_of_le hmoduleV] at hm
  have hmoduleQ : moduleSubgroup ≤ QAt ctx.Γ penultimate :=
    hmoduleV.trans (nine_five_terminal_module_le_penultimate_core ctx.toLocalContext hb)
  have hcoreQ : core ≤ QAt ctx.Γ penultimate := by
    change twoCoreIn (e ctx.Γ penultimate) ≤ q ctx.Γ penultimate
    rw [CosetGraphContext.e, ctx.Γ.twoResidualAt_def, q, ctx.Γ.twoCoreAt_def,
      residual_core_eq_inter_core]
    exact inf_le_right
  have hcenterQ : center ≤ omegaOneCenter (QAt ctx.Γ penultimate) :=
    (lemma_seven_three ctx.sectionSeven ctx.Γ).center_core _ _
      ((mem_neighborhood_iff_adjacent ctx.Γ).mpr hadj)
  have hcenterCentral : center ≤ Subgroup.centralizer (core : Set G) :=
    (hcenterQ.trans ((omegaOneCenter_le_centerAmbient _).trans
      (centerAmbient_le_centralizer _))).trans (Subgroup.centralizer_le hcoreQ)
  have hcoreCentral : core ≤ Subgroup.centralizer (moduleSubgroup : Set G) := by
    apply Subgroup.le_centralizer_iff.mp
    exact sup_le (Subgroup.le_centralizer_iff.mp
      (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcentral)) hcenterCentral
  have haction := nine_five_penultimate_join_action_of_initial_four ctx hfour hb prev
    hpath residual (le_inf hcontain hresidualV)
  have hactingNormalizer : acting ≤ Subgroup.normalizer (moduleSubgroup : Set G) :=
    hjoin.trans haction.2
  have hactingCenter : acting ≤ Subgroup.normalizer (center : Set G) := by
    change e ctx.Γ penultimate ≤ Subgroup.normalizer (z ctx.Γ penultimate : Set G)
    rw [CosetGraphContext.e, ctx.Γ.twoResidualAt_def]
    exact (twoResidualIn_le _).trans (stabilizer_le_normalizer_z ctx.Γ penultimate)
  have hbound : ⁅moduleSubgroup, acting⁆ ≤ center := by
    apply nine_five_commutator_join_le residual center acting center
    · exact ((hresidualV.trans (Subgroup.le_centralizer _)).trans
        (Subgroup.centralizer_le hcenterV)).trans (Subgroup.centralizer_le_normalizer _)
    · exact Subgroup.le_normalizer
    · rw [Subgroup.commutator_comm]
      exact (Subgroup.commutator_mono hjoin le_rfl).trans haction.1
    · exact Subgroup.le_normalizer_iff_commutator_le_left.mp hactingCenter
  obtain ⟨mover, hmiddle, _⟩ := lemma_seven_five_endpoint_alignment ctx.sectionSeven
    ctx.Γ ctx.criticalPath ctx.commutator_eq
  have hfixed : moduleSubgroup ⊓ Subgroup.centralizer (acting : Set G) = ⊥ := by
    apply bot_unique
    exact (inf_le_inf_right _ hmoduleQ).trans_eq
      (nine_five_initial_orbit_residual_centralizer ctx.toLocalContext penultimate
        ⟨mover, hmiddle⟩)
  let _ : (core.subgroupOf acting).Normal := twoCoreIn_normal acting
  have hcollapse := Subgroup.le_of_odd_index_core_centralizes acting core moduleSubgroup
    center (twoCoreIn_le acting) ((pCore_isPGroup (p := 2) (G := acting)).map acting.subtype)
    (nine_five_vertex_residual_core_odd_index ctx.toLocalContext penultimate _ hadj)
    (IsElementaryAbelian.isPGroup 2 moduleSubgroup)
    (Group.isSolvable_of_comm fun first second => mul_comm first second)
    hactingNormalizer hcoreCentral hfixed hbound
  exact le_sup_left.trans hcollapse


end Stellmacher.SectionNine
