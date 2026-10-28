module
public import Stellmacher.SectionThree.ResidualConjugatePairSylowGeneration
public import Stellmacher.SectionNine.NineTenPrescribedActorGeometry
public import Stellmacher.SectionFiveToSeven.EdgeSylowGeneration

/-!
# The retained (9.10) actor generates every common-neighbor edge

For the actual second geometric extraction, its prescribed actor together
with any edge at the first vertex whose other endpoint also neighbors the
extracted third vertex generates the entire first stabilizer. The actor,
conjugator, and extraction group are kept unchanged. Only the local context,
a third path offset, and membership in a terminal-neighbor center are needed.

Critical minimality puts the terminal module in the third core, hence its
conjugate in each indicated edge. The recorded actor-generation equation
therefore puts E in the edge joined with the actor. To promote this to the
whole stabilizer, first replace the extracted full edge by its Sylow subgroup.
The conjugated terminal module lies in the extracted core, hence in that
Sylow subgroup. The inverse residual conjugator writes the same E as this
seed and its conjugate. The residual conjugate-pair theorem now supplies
generation with every edge Sylow, including the required edge.

This supplies the universal generation premise of (9.4) for the same actor
used in Stellmacher (9.10), Journal of Algebra 190 (1997), printed p.57.
It does not replace E by the smaller center-generated subgroup in the source,
and it does not assume a full edge is a Sylow subgroup.
-/

namespace Stellmacher.SectionNine
open Later SectionsFiveToSeven CosetGraphContext SevenSix

private theorem extracted_sup_every_edge_sylow
    {G : Type*} [Group G] [Finite G] {T A B : Subgroup G}
    (h : SectionSevenHypotheses G T A B) (Γ : CosetGraphContext G T A B)
    (vertex second : Γ.Vertex) (V E A0 : Subgroup G) (actor : G)
    (data : NineThreeGeometricData Γ vertex second V E A0 actor)
    (W : Subgroup G) (hW : IsSylowSubgroupIn W (GAt Γ vertex)) :
    E ⊔ W = GAt Γ vertex := by
  let extracted := Γ.act data.x⁻¹ second
  let edge := GAt Γ vertex ⊓ GAt Γ extracted
  let sylow : Sylow 2 edge := default
  let S := sylowTwoAmbient edge sylow
  have hd := edge_sectionThree_data h Γ data.neighbor sylow
  have hcore : QAt Γ extracted ≤ S := by
    obtain ⟨U, hU⟩ := hd.2.2.1.1.2.1
    change Γ.twoCoreAt extracted ≤ S
    rw [Γ.twoCoreAt_def]
    change twoCoreIn (GAt Γ extracted) ≤ S
    change (↑U : Subgroup (GAt Γ extracted)).map (GAt Γ extracted).subtype = S at hU
    rw [← hU]
    exact Subgroup.map_mono (pCore_isPGroup.le_sylow_of_normal U)
  have hseed : V.conjBy data.x ≤ S := data.conjugate_core_le.trans hcore
  have hxE : data.x ∈ E := twoResidualIn_le E data.residual_mem
  have hxR : data.x⁻¹ ∈ twoResidualAmbient (GAt Γ vertex) :=
    (twoResidualIn (GAt Γ vertex)).inv_mem
      (twoResidualIn_mono E (GAt Γ vertex) data.group_le data.residual_mem)
  have hpair : E = V.conjBy data.x ⊔ (V.conjBy data.x).conjBy data.x⁻¹ := by
    rw [Subgroup.conjBy_inv, sup_comm]
    exact data.generated
  have hgenerate : E ⊔ S = GAt Γ vertex :=
    edge_sylow_generation h Γ vertex extracted
      ((mem_neighborhood_iff_adjacent Γ).mp data.neighbor) E data.edge_generated sylow
  exact SectionThree.residual_conjugate_pair_sup_sylow_eq
    (GAt Γ vertex) S (V.conjBy data.x) E hd.2.1 hd.2.2.2.1 hseed data.group_le
    data.x⁻¹ (E.inv_mem hxE) hxR hpair hgenerate W hW

public theorem nine_ten_prescribed_actor_common_neighbor_generation
    {G : Type*} [Group G] [Finite G] {T A B : Subgroup G}
    (ctx : SectionNineLocalContext G T A B)
    (third second neighbor : ctx.Γ.Vertex)
    (hthird : IsCriticalPathOffset ctx.Γ ctx.criticalPath 3 third)
    (hneighbor : neighbor ∈ neighborhood ctx.Γ ctx.criticalPath.a')
    (actor : G) (E A0 : Subgroup G)
    (data : NineThreeGeometricData ctx.Γ ctx.criticalPath.firstStep second
      (VAt ctx.Γ ctx.criticalPath.a') E A0 actor)
    (hactor : actor ∈ ZAt ctx.Γ neighbor)
    (n : ctx.Γ.Vertex)
    (hn : n ∈ neighborhood ctx.Γ ctx.criticalPath.firstStep)
    (hn' : n ∈ neighborhood ctx.Γ (ctx.Γ.act data.x⁻¹ third)) :
    (GAt ctx.Γ ctx.criticalPath.firstStep ⊓ GAt ctx.Γ n) ⊔
      Subgroup.zpowers actor = GAt ctx.Γ ctx.criticalPath.firstStep := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let V := VAt Γ cp.a'
  let P := GAt Γ cp.firstStep
  let predecessor := Γ.act data.x⁻¹ third
  let edge := P ⊓ GAt Γ n
  let joined := edge ⊔ Subgroup.zpowers actor
  change IsCriticalPathOffset Γ cp 3 third at hthird
  have hVthird : V ≤ QAt Γ third := by
    change VAt Γ cp.a' ≤ _
    rw [VAt, v, Γ.vAt_def]
    apply sSup_le
    rintro center ⟨vertex, hvertex, rfl⟩
    obtain ⟨index, hindex, rfl⟩ := hthird
    have hlength : 3 ≤ cp.length := by omega
    have hindexEq : index = ⟨3, by omega⟩ := Fin.ext hindex
    have hpath := path_distance_le Γ cp 3 cp.length hlength le_rfl
    rw [cp.path_end, ← hindexEq] at hpath
    have hadj := Γ.adjacent_symm ((mem_neighborhood_iff_adjacent Γ).mp hvertex)
    have hstep := nine_eight_adjacent_distance_le Γ (target := cp.path index) hadj
    rw [Γ.distance_symm cp.a' (cp.path index)] at hstep
    exact critical_minimality Γ cp (by omega)
  have hconjCore : V.conjBy data.x ≤ QAt Γ predecessor := by
    change V.map (MulAut.conj data.x).toMonoidHom ≤ q Γ (Γ.act data.x⁻¹ third)
    rw [q_act, inv_inv]
    exact Subgroup.map_mono hVthird
  have hVE : V ≤ E := by
    rw [data.generated]
    exact le_sup_left
  have hconjE : V.conjBy data.x ≤ E := le_sup_right.trans_eq data.generated.symm
  have hconjP : V.conjBy data.x ≤ P := hconjE.trans data.group_le
  have hconjN : V.conjBy data.x ≤ GAt Γ n :=
    hconjCore.trans
      ((lemma_seven_three ctx.sectionSeven Γ).sylow_and_core predecessor n hn' default).2.2
  have hactorV : actor ∈ V := by
    have hZ : ZAt Γ neighbor ≤ V := by
      change ZAt Γ neighbor ≤ VAt Γ cp.a'
      rw [VAt, v, Γ.vAt_def]
      exact le_sSup ⟨neighbor, hneighbor, rfl⟩
    exact hZ hactor
  have hactorP : actor ∈ P :=
    data.group_le (hVE hactorV)
  have hEjoined : E ≤ joined := by
    rw [data.actor_generated actor hactorV data.actor_outside]
    exact sup_le (by rw [← Subgroup.zpowers_eq_closure]; exact le_sup_right)
      ((le_inf hconjP hconjN).trans le_sup_left)
  let sylow : Sylow 2 edge := default
  let W := sylowTwoAmbient edge sylow
  have hW : IsSylowSubgroupIn W P :=
    (edge_sectionThree_data ctx.sectionSeven Γ hn sylow).2.1.1.2.1
  have hgen : E ⊔ W = P := extracted_sup_every_edge_sylow ctx.sectionSeven Γ
    cp.firstStep second V E A0 actor data W hW
  change joined = P
  apply le_antisymm
  · exact sup_le inf_le_left (Subgroup.zpowers_le.mpr hactorP)
  · rw [← hgen]
    exact sup_le hEjoined ((Subgroup.map_subtype_le _).trans le_sup_left)

end Stellmacher.SectionNine
