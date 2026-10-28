module

public import Stellmacher.SectionNine.GeneratedContext
public import Stellmacher.SectionNine.NineThreeOrbitModuleCentralizer
public import Stellmacher.SectionFiveToSeven.PrescribedCriticalPairNormalization

/-!
# Opening reductions for ambient Stellmacher (9.4)

Distance two supplies a common neighbor and the same vertex orbit. Residual
commutators with a local actor stay in the local stabilizer, so moving the
remote vertex preserves its distance. The remote neighbor-center subgroup
is elementary abelian by (7.5), and adjoining its intersection with the
target preserves the commutator hypothesis and the desired containment.

The conjugated actor centralizes the moved module. The existing ambient
module-centralizer theorem therefore places it in the moved vertex core.
No hypothesis on the ambient group is transferred to the embedded group.

Source: Stellmacher, Journal of Algebra 190 (1997), printed pp.50–51,
the opening of (9.4), in `refs/files/stellmacher-n-group.pdf` (PDF40–41).
These reductions do not assert the two remaining case arguments of (9.4).
-/

open scoped Pointwise IsMulCommutative

namespace Stellmacher.SectionNine

open Later SectionsFiveToSeven CosetGraphContext SevenSix

universe u

public theorem nine_four_common_neighbor
    {G : Type u} [Group G] [Finite G] {T A B : Subgroup G}
    (Γ : CosetGraphContext G T A B) (left right : Γ.Vertex)
    (hdistance : Γ.distance left right = 2) :
    ∃ neighbor, neighbor ∈ Neighborhood Γ left ∧ neighbor ∈ Neighborhood Γ right := by
  obtain ⟨path, hstart, hend, hadj⟩ := Γ.distance_path left right
  let middle : Fin (Γ.distance left right + 1) := ⟨1, by omega⟩
  refine ⟨path middle, ?_, ?_⟩
  · apply (mem_neighborhood_iff_adjacent Γ).mpr
    have hedge := hadj ⟨0, by omega⟩
    change Γ.adjacent (path 0) (path middle) at hedge
    rwa [hstart] at hedge
  · apply (mem_neighborhood_iff_adjacent Γ).mpr
    have hedge := hadj ⟨1, by omega⟩
    have hlast : (⟨1, by omega⟩ : Fin (Γ.distance left right)).succ =
        ⟨Γ.distance left right, Nat.lt_succ_self _⟩ := by
      apply Fin.ext
      simp only [Fin.val_succ]
      omega
    rw [hlast, hend] at hedge
    exact Γ.adjacent_symm hedge

public theorem nine_four_distance_two_orbit
    {G : Type u} [Group G] [Finite G] {T A B : Subgroup G}
    (h : SectionSevenHypotheses G T A B)
    (Γ : CosetGraphContext G T A B) (left right : Γ.Vertex)
    (hdistance : Γ.distance left right = 2) : IsConjugateVertex Γ left right := by
  obtain ⟨neighbor, hleft, hright⟩ := nine_four_common_neighbor Γ left right hdistance
  have hleft' : left ∈ Neighborhood Γ neighbor :=
    (mem_neighborhood_iff_adjacent Γ).mpr
      (Γ.adjacent_symm ((mem_neighborhood_iff_adjacent Γ).mp hleft))
  have hright' : right ∈ Neighborhood Γ neighbor :=
    (mem_neighborhood_iff_adjacent Γ).mpr
      (Γ.adjacent_symm ((mem_neighborhood_iff_adjacent Γ).mp hright))
  obtain ⟨actor, hactor⟩ := (lemma_seven_one h Γ).local_transitivity
    neighbor hleft' hright'
  exact ⟨actor, hactor⟩

public theorem nine_four_normalize_two_path
    {G : Type u} [Group G] [Finite G] {T A B : Subgroup G}
    (ctx : SectionNineLocalContext G T A B) (remote : ctx.Γ.Vertex)
    (hdistance : ctx.Γ.distance remote ctx.criticalPath.firstStep = 2) :
    ∃ neighbor : ctx.Γ.Vertex, ∃ actor : G,
      neighbor ∈ Neighborhood ctx.Γ ctx.criticalPath.firstStep ∧
      neighbor ∈ Neighborhood ctx.Γ remote ∧
      actor ∈ GAt ctx.Γ ctx.criticalPath.firstStep ∧
      ctx.Γ.act actor neighbor = ctx.criticalPath.a ∧
      ctx.Γ.act actor ctx.criticalPath.firstStep = ctx.criticalPath.firstStep ∧
      ctx.Γ.act actor remote ∈ Neighborhood ctx.Γ ctx.criticalPath.a ∧
      ctx.Γ.act actor remote ≠ ctx.criticalPath.firstStep := by
  obtain ⟨neighbor, hneighbor, hremote⟩ := nine_four_common_neighbor ctx.Γ
    ctx.criticalPath.firstStep remote (by rwa [ctx.Γ.distance_symm])
  have hinitial : ctx.criticalPath.a ∈ Neighborhood ctx.Γ ctx.criticalPath.firstStep :=
    (mem_neighborhood_iff_adjacent ctx.Γ).mpr
      (ctx.Γ.adjacent_symm ctx.criticalPath.firstStep_adj)
  obtain ⟨actor, hactor⟩ := (lemma_seven_one ctx.sectionSeven ctx.Γ).local_transitivity
    ctx.criticalPath.firstStep hneighbor hinitial
  have hfix : ctx.Γ.act actor ctx.criticalPath.firstStep = ctx.criticalPath.firstStep :=
    (Set.ext_iff.mp (ctx.Γ.stabilizer_def ctx.criticalPath.firstStep) actor).mp actor.property
  refine ⟨neighbor, actor, hneighbor, hremote, actor.property, hactor, hfix, ?_, ?_⟩
  · apply (mem_neighborhood_iff_adjacent ctx.Γ).mpr
    have hedge := adjacent_act ctx.Γ actor
      (ctx.Γ.adjacent_symm ((mem_neighborhood_iff_adjacent ctx.Γ).mp hremote))
    rwa [hactor] at hedge
  · intro heq
    have htwo := distance_act ctx.Γ actor remote ctx.criticalPath.firstStep
    rw [hfix, heq, hdistance] at htwo
    have hzero := (ctx.Γ.distance_zero_iff ctx.criticalPath.firstStep
      ctx.criticalPath.firstStep).mpr rfl
    omega

public theorem nine_four_conjugator_mem_stabilizer
    {G : Type u} [Group G] [Finite G] {T A B : Subgroup G}
    (Γ : CosetGraphContext G T A B) (vertex : Γ.Vertex) (actor conjugator : G)
    (hactor : actor ∈ GAt Γ vertex)
    (hconjugator : conjugator ∈ ⁅EAt Γ vertex, Subgroup.zpowers actor⁆) :
    conjugator ∈ GAt Γ vertex := by
  have hresidual : EAt Γ vertex ≤ GAt Γ vertex := by
    change Γ.twoResidualAt vertex ≤ Γ.vertexStabilizer vertex
    rw [Γ.twoResidualAt_def]
    exact twoResidualIn_le _
  have hcyclic : Subgroup.zpowers actor ≤ GAt Γ vertex :=
    (Subgroup.zpowers_le).mpr hactor
  exact ((Subgroup.commutator_le_sup _ _).trans (sup_le hresidual hcyclic)) hconjugator

public theorem nine_four_moved_distance
    {G : Type u} [Group G] [Finite G] {T A B : Subgroup G}
    (Γ : CosetGraphContext G T A B) (vertex remote : Γ.Vertex) (actor conjugator : G)
    (hactor : actor ∈ GAt Γ vertex)
    (hconjugator : conjugator ∈ ⁅EAt Γ vertex, Subgroup.zpowers actor⁆)
    (hdistance : Γ.distance remote vertex = 2) :
    Γ.distance (Γ.act conjugator remote) vertex = 2 := by
  have hfix : Γ.act conjugator vertex = vertex :=
    Set.ext_iff.mp (Γ.stabilizer_def vertex) conjugator |>.mp
      (nine_four_conjugator_mem_stabilizer Γ vertex actor conjugator hactor hconjugator)
  rw [← hfix, distance_act, hdistance]

public theorem nine_four_remote_elementary
    {G : Type u} [Group G] [Finite G] {T A B : Subgroup G}
    (ctx : SectionNineLocalContext G T A B)
    (hb : 1 < ctx.criticalPath.length) (remote : ctx.Γ.Vertex)
    (hdistance : ctx.Γ.distance remote ctx.criticalPath.firstStep = 2) :
    IsElementaryAbelian 2 (VAt ctx.Γ remote) := by
  obtain ⟨actor, hactor⟩ := nine_four_distance_two_orbit ctx.sectionSeven ctx.Γ
    ctx.criticalPath.firstStep remote (by rwa [ctx.Γ.distance_symm])
  let _ : IsElementaryAbelian 2 (VAt ctx.Γ ctx.criticalPath.firstStep) :=
    ((lemma_seven_five ctx.sectionSeven ctx.Γ ctx.criticalPath
      ctx.commutator_eq).longer_case hb).1
  rw [← hactor]
  change IsElementaryAbelian 2 (v ctx.Γ (ctx.Γ.act actor ctx.criticalPath.firstStep))
  rw [v_act]
  exact IsElementaryAbelian.map (MulAut.conj actor⁻¹).toMonoidHom

public theorem nine_four_enlarge_commutator
    {G : Type u} [Group G] (remote target subgroup actor : Subgroup G)
    [IsMulCommutative remote]
    (hsubgroup : subgroup ≤ remote)
    (hnormalizes : actor ≤ Subgroup.normalizer target)
    (hcommutator : ⁅subgroup, actor⁆ ≤ target) :
    ⁅subgroup ⊔ (remote ⊓ target), actor⁆ ≤ target := by
  have hnormalize : subgroup ≤ Subgroup.normalizer (remote ⊓ target : Subgroup G) := by
    intro mover hmover
    apply Subgroup.mem_normalizer_iff.mpr
    intro point
    constructor
    · intro hpoint
      have hcomm : mover * point = point * mover :=
        congrArg Subtype.val (mul_comm (⟨mover, hsubgroup hmover⟩ : remote)
          ⟨point, hpoint.1⟩)
      simpa only [hcomm, mul_inv_cancel_right] using hpoint
    · intro hpoint
      have hremote : point ∈ remote := by
        have hmem := remote.mul_mem
          (remote.mul_mem (remote.inv_mem (hsubgroup hmover)) hpoint.1)
          (hsubgroup hmover)
        simpa only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one] using hmem
      have hcomm : mover * point = point * mover :=
        congrArg Subtype.val (mul_comm (⟨mover, hsubgroup hmover⟩ : remote)
          ⟨point, hremote⟩)
      simpa only [hcomm, mul_inv_cancel_right] using hpoint
  apply Subgroup.commutator_le.mpr
  intro point hpoint mover hmover
  rw [sup_comm] at hpoint
  change point ∈ (↑((remote ⊓ target) ⊔ subgroup) : Set G) at hpoint
  rw [Subgroup.coe_mul_of_right_le_normalizer_left _ _ hnormalize] at hpoint
  obtain ⟨inside, hinside, original, horiginal, rfl⟩ := hpoint
  rw [commutatorElement_mul_left_eq_conj_mul]
  exact target.mul_mem
    (target.mul_mem (target.mul_mem hinside.2
      (hcommutator (Subgroup.commutator_mem_commutator horiginal hmover)))
      (target.inv_mem hinside.2))
    ((Subgroup.le_normalizer_iff_commutator_le_left.mp hnormalizes)
      (Subgroup.commutator_mem_commutator hinside.2 hmover))

public theorem nine_four_enlargement
    {G : Type u} [Group G] [Finite G] {T A B : Subgroup G}
    (ctx : SectionNineLocalContext G T A B)
    (hb : 1 < ctx.criticalPath.length) (remote : ctx.Γ.Vertex)
    (hdistance : ctx.Γ.distance remote ctx.criticalPath.firstStep = 2)
    (actor : G) (hactor : actor ∈ GAt ctx.Γ ctx.criticalPath.firstStep)
    (subgroup : Subgroup G) (hsubgroup : subgroup ≤ VAt ctx.Γ remote)
    (hcommutator : ⁅subgroup, Subgroup.zpowers actor⁆ ≤
      VAt ctx.Γ ctx.criticalPath.firstStep) :
    let enlarged := subgroup ⊔ (VAt ctx.Γ remote ⊓ VAt ctx.Γ ctx.criticalPath.firstStep)
    subgroup ≤ enlarged ∧ enlarged ≤ VAt ctx.Γ remote ∧
      VAt ctx.Γ remote ⊓ VAt ctx.Γ ctx.criticalPath.firstStep ≤ enlarged ∧
      ⁅enlarged, Subgroup.zpowers actor⁆ ≤ VAt ctx.Γ ctx.criticalPath.firstStep ∧
      (enlarged ≤ VAt ctx.Γ ctx.criticalPath.firstStep ↔
        subgroup ≤ VAt ctx.Γ ctx.criticalPath.firstStep) := by
  let _ := nine_four_remote_elementary ctx hb remote hdistance
  refine ⟨le_sup_left, sup_le hsubgroup inf_le_left, le_sup_right, ?_, ?_⟩
  · exact nine_four_enlarge_commutator _ _ _ _ hsubgroup
      ((Subgroup.zpowers_le).mpr (stabilizer_le_normalizer_v ctx.Γ
        ctx.criticalPath.firstStep hactor)) hcommutator
  · exact ⟨fun hle => le_sup_left.trans hle, fun hle => sup_le hle inf_le_right⟩

public theorem nine_four_index_two_noncontainment
    {G : Type u} [Group G] [Finite G] (moduleGroup centerGroup : Subgroup G)
    (actor : G)
    (hindex : QuotientCardEq (⁅moduleGroup, Subgroup.zpowers actor⁆ ⊔ centerGroup)
      centerGroup 2) :
    ¬ ⁅moduleGroup, Subgroup.zpowers actor⁆ ≤ centerGroup := by
  intro hle
  unfold QuotientCardEq at hindex
  rw [sup_eq_right.mpr hle] at hindex
  have hpositive := Nat.card_pos (α := centerGroup)
  omega

public theorem nine_four_neighbor_edge_proper
    {G : Type u} [Group G] [Finite G] {T A B : Subgroup G}
    (h : SectionSevenHypotheses G T A B) (Γ : CosetGraphContext G T A B)
    (vertex neighbor : Γ.Vertex) (hneighbor : neighbor ∈ Neighborhood Γ vertex) :
    GAt Γ vertex ⊓ GAt Γ neighbor ≠ GAt Γ vertex := by
  have hdata := edge_sectionThree_data h Γ hneighbor default
  have hjoin := hdata.2.2.2.2.1
  intro hequal
  have hle : GAt Γ vertex ≤ GAt Γ neighbor := hequal ▸ inf_le_right
  have htop : GAt Γ neighbor = ⊤ := by
    rwa [sup_eq_right.mpr hle] at hjoin
  have hcoreNe : QAt Γ neighbor ≠ ⊥ := by
    rw [show QAt Γ neighbor = twoCoreAmbient (GAt Γ neighbor) from Γ.twoCoreAt_def _]
    exact hdata.2.2.1.1.2.2.1
  have hcoreGroup : IsPGroup 2 (QAt Γ neighbor) := by
    rw [show QAt Γ neighbor = twoCoreAmbient (GAt Γ neighbor) from Γ.twoCoreAt_def _]
    exact (pCore_isPGroup (p := 2) (G := GAt Γ neighbor)).map (GAt Γ neighbor).subtype
  have hcoreNormal : (QAt Γ neighbor).Normal := by
    apply Subgroup.normalizer_eq_top_iff.mp
    apply top_unique
    rw [← htop]
    exact stabilizer_le_normalizer_q Γ neighbor
  have hcoreLe : QAt Γ neighbor ≤ pCore 2 G := le_sSup ⟨hcoreNormal, hcoreGroup⟩
  exact hcoreNe (bot_unique (hcoreLe.trans_eq h.twoCore_eq_bot))

public theorem nine_four_actor_not_mem_core
    {G : Type u} [Group G] [Finite G] {T A B : Subgroup G}
    (h : SectionSevenHypotheses G T A B) (Γ : CosetGraphContext G T A B)
    (vertex neighbor : Γ.Vertex) (hneighbor : neighbor ∈ Neighborhood Γ vertex)
    (actor : G)
    (hgenerate : (GAt Γ vertex ⊓ GAt Γ neighbor) ⊔ Subgroup.zpowers actor =
      GAt Γ vertex) : actor ∉ QAt Γ vertex := by
  intro hcore
  have hneighborCore := ((lemma_seven_three h Γ).sylow_and_core
    vertex neighbor hneighbor default).2.2
  have hself : QAt Γ vertex ≤ GAt Γ vertex := by
    change Γ.twoCoreAt vertex ≤ Γ.vertexStabilizer vertex
    rw [Γ.twoCoreAt_def]
    exact twoCoreIn_le _
  have hcyclic : Subgroup.zpowers actor ≤ GAt Γ vertex ⊓ GAt Γ neighbor :=
    (Subgroup.zpowers_le).mpr ⟨hself hcore, hneighborCore hcore⟩
  rw [sup_eq_left.mpr hcyclic] at hgenerate
  exact nine_four_neighbor_edge_proper h Γ vertex neighbor hneighbor hgenerate

public theorem nine_four_conjugated_actor_mem_remote_core
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (remote : ctx.Γ.Vertex)
    (hdistance : ctx.Γ.distance remote ctx.criticalPath.firstStep = 2)
    (actor : G)
    (hactor : actor ∈ GAt ctx.Γ ctx.criticalPath.firstStep ∧
      actor ∈ Subgroup.centralizer (VAt ctx.Γ remote : Set G))
    (conjugator : G)
    (hconjugator : conjugator ∈ ⁅EAt ctx.Γ ctx.criticalPath.firstStep,
      Subgroup.zpowers actor⁆) :
    conjugator⁻¹ * actor * conjugator ∈ QAt ctx.Γ (ctx.Γ.act conjugator remote) := by
  have hmoved := nine_four_moved_distance ctx.Γ ctx.criticalPath.firstStep remote
    actor conjugator hactor.1 hconjugator hdistance
  have horbit := nine_four_distance_two_orbit ctx.sectionSeven ctx.Γ
    ctx.criticalPath.firstStep (ctx.Γ.act conjugator remote)
    (by rwa [ctx.Γ.distance_symm])
  apply nine_three_module_centralizer_core_at_vertex ctx _ horbit
  have hmap := Subgroup.map_centralizer_le_centralizer_image
    (VAt ctx.Γ remote : Set G) (MulAut.conj conjugator⁻¹).toMonoidHom
      (Subgroup.mem_map_of_mem (MulAut.conj conjugator⁻¹).toMonoidHom hactor.2)
  change (MulAut.conj conjugator⁻¹) actor ∈
    Subgroup.centralizer ((VAt ctx.Γ remote).map
      (MulAut.conj conjugator⁻¹).toMonoidHom : Set G) at hmap
  change conjugator⁻¹ * actor * conjugator ∈
    Subgroup.centralizer (v ctx.Γ (ctx.Γ.act conjugator remote) : Set G)
  rw [v_act]
  simpa only [MulAut.conj_apply, inv_inv] using hmap

public theorem nine_four_actor_closure_le_remote_core
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (remote : ctx.Γ.Vertex)
    (hdistance : ctx.Γ.distance remote ctx.criticalPath.firstStep = 2)
    (actor : G)
    (hactor : actor ∈ GAt ctx.Γ ctx.criticalPath.firstStep ∧
      actor ∈ Subgroup.centralizer (VAt ctx.Γ remote : Set G))
    (conjugator : G)
    (hconjugator : conjugator ∈ ⁅EAt ctx.Γ ctx.criticalPath.firstStep,
      Subgroup.zpowers actor⁆)
    (neighbor : ctx.Γ.Vertex)
    (hneighbor : neighbor ∈ Neighborhood ctx.Γ (ctx.Γ.act conjugator remote)) :
    conjugateClosure (Subgroup.zpowers (conjugator⁻¹ * actor * conjugator))
      (QAt ctx.Γ neighbor) ≤ QAt ctx.Γ (ctx.Γ.act conjugator remote) := by
  have hreverse : ctx.Γ.act conjugator remote ∈ Neighborhood ctx.Γ neighbor :=
    (mem_neighborhood_iff_adjacent ctx.Γ).mpr
      (ctx.Γ.adjacent_symm ((mem_neighborhood_iff_adjacent ctx.Γ).mp hneighbor))
  have hcoreNeighbor := ((lemma_seven_three ctx.sectionSeven ctx.Γ).sylow_and_core
    neighbor (ctx.Γ.act conjugator remote) hreverse default).2.2
  have hnormalizes := hcoreNeighbor.trans
    (stabilizer_le_normalizer_q ctx.Γ (ctx.Γ.act conjugator remote))
  have hcyclic : Subgroup.zpowers (conjugator⁻¹ * actor * conjugator) ≤
      QAt ctx.Γ (ctx.Γ.act conjugator remote) :=
    (Subgroup.zpowers_le).mpr (nine_four_conjugated_actor_mem_remote_core ctx remote
      hdistance actor hactor conjugator hconjugator)
  apply (Subgroup.closure_le _).mpr
  rintro point ⟨mover, element, rfl⟩
  exact (Subgroup.mem_normalizer_iff.mp (hnormalizes mover.property) element).mp
    (hcyclic element.property)

end Stellmacher.SectionNine
