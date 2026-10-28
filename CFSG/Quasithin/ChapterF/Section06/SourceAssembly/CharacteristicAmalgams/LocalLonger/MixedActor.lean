module
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.CharacteristicAmalgams.LocalLonger.MixedRelations
public import Stellmacher.SectionFiveToSeven.Result7_8.GeometricCoatomCoreJoin

/-!
# The normalized mixed actor lies in the actual Sylow and moves the center

The second coatom/core containment places the other-center actor inside T.
Mutual quadraticity is preserved by the common normalizing actor. The
first extraction's exact inner index prevents this actor from centralizing
the initial center: such centralization would fix the selected conjugator
and collapse that inner index.

This is the local geometric actor in Stellmacher (9.3)(4), Journal of
Algebra 190 (1997), pp.49--50, with the actual normalized witnesses.
-/
namespace Stellmacher.SectionNine.LocalLonger
open Later SectionsFiveToSeven CosetGraphContext SevenSix
universe u

public theorem mixed_actor_quadratic
    {G : Type u} [Group G] [Finite G] {T A B : Subgroup G}
    (ctx : SectionNineLocalContext G T A B)
    (hb : 1 < ctx.criticalPath.length)
    (first : FirstConfigurationData ctx)
    (second : SecondConfigurationData ctx first)
    (config : NormalizedGeometry ctx first second) :
    let m := ctx.Γ.act config.g (ctx.Γ.act first.extraction.x⁻¹ first.l)
    let actor := ZAt ctx.Γ m ⊓ GAt ctx.Γ ctx.criticalPath.a
    actor ≤ T ∧ ⁅⁅ZAt ctx.Γ ctx.criticalPath.a, actor⁆, actor⁆ = ⊥ := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let m := Γ.act config.g (Γ.act first.extraction.x⁻¹ first.l)
  let terminal := VAt Γ (Γ.act config.g cp.a')
  let actor := ZAt Γ m ⊓ GAt Γ cp.a
  have hcenter : ZAt Γ m ≤ terminal := by
    change z Γ (Γ.act config.g (Γ.act first.extraction.x⁻¹ first.l)) ≤
      v Γ (Γ.act config.g cp.a')
    rw [z_act, v_act]
    apply Subgroup.map_mono
    rw [v, Γ.vAt_def]
    exact le_sSup ⟨_, first.extraction.neighbor, rfl⟩
  have hcoatom := geometric_coatom_le_core_join Γ cp.firstStep
    (Γ.act config.g second.l) _ _ _ _ config.second_geometry
  rw [config.second_new_vertex] at hcoatom
  have hcoatomEq := config.second_geometry.coatom_eq
  rw [config.second_new_vertex] at hcoatomEq
  rw [hcoatomEq] at hcoatom
  have hterminal : terminal ⊓ GAt Γ cp.a ≤ T :=
    hcoatom.trans (sup_le (local_cores_le_edge_sylow ctx.sectionSeven Γ cp).2
      (local_cores_le_edge_sylow ctx.sectionSeven Γ cp).1)
  have hactor : actor ≤ terminal := inf_le_left.trans hcenter
  refine ⟨(le_inf hactor inf_le_right).trans hterminal, ?_⟩
  have hquadratic :=
    ((lemma_seven_five ctx.sectionSeven Γ cp ctx.commutator_eq).longer_case hb).2.2
  change ⁅⁅v Γ cp.firstStep, v Γ cp.a'⁆, v Γ cp.a'⁆ = ⊥ at hquadratic
  have hnormalized := congrArg
    (fun subgroup : Subgroup G => subgroup.map (MulAut.conj config.g⁻¹).toMonoidHom)
    hquadratic
  rw [Subgroup.map_commutator, Subgroup.map_commutator, ← v_act,
    config.fixes_firstStep, ← v_act, Subgroup.map_bot] at hnormalized
  exact le_bot_iff.mp ((Subgroup.commutator_mono (Subgroup.commutator_mono
    (lemma_seven_four ctx.sectionSeven Γ cp).first_containment.1 hactor)
    hactor).trans_eq hnormalized)

private theorem extracted_actor_not_centralized
    {G : Type u} [Group G] [Finite G] {T A B : Subgroup G}
    (h : SectionSevenHypotheses G T A B) (Γ : CosetGraphContext G T A B)
    (initial terminal old : Γ.Vertex) (moduleGroup extracted coatom : Subgroup G)
    (generator : G) (hcenter : generator ∈ ZAt Γ initial)
    (hmodule : generator ∈ moduleGroup)
    (data : NineThreeGeometricData Γ terminal old moduleGroup extracted coatom generator)
    (hnot : ¬ ZAt Γ (Γ.act data.x⁻¹ old) ⊓ GAt Γ initial ≤ ZAt Γ old) :
    ¬ ZAt Γ initial ≤ Subgroup.centralizer
      (ZAt Γ (Γ.act data.x⁻¹ old) ⊓ GAt Γ initial : Set G) := by
  let newVertex := Γ.act data.x⁻¹ old
  let actor := ZAt Γ newVertex ⊓ GAt Γ initial
  have hneighbor : terminal ∈ neighborhood Γ newVertex :=
    (mem_neighborhood_iff_adjacent Γ).mpr
      (Γ.adjacent_symm ((mem_neighborhood_iff_adjacent Γ).mp data.neighbor))
  have hcore := ((lemma_seven_three h Γ).center_core newVertex terminal hneighbor).trans
    ((omegaOneCenter_le_centerAmbient _).trans (centerAmbient_le_centralizer _))
  intro hcentral
  have hextracted : extracted ≤ Subgroup.centralizer (actor : Set G) := by
    rw [data.actor_generated generator hmodule data.actor_outside]
    refine sup_le ((Subgroup.closure_le _).mpr
      (Set.singleton_subset_iff.mpr (hcentral hcenter))) ?_
    exact data.conjugate_core_le.trans ((Subgroup.le_centralizer_iff.mp hcore).trans
      (Subgroup.centralizer_le inf_le_left))
  apply hnot
  intro vector hvector
  have hconjugator : data.x ∈ extracted := Subgroup.map_subtype_le _ data.residual_mem
  have hcomm := Subgroup.mem_centralizer_iff.mp (hextracted hconjugator) vector hvector
  have hnew := hvector.1
  change vector ∈ z Γ (Γ.act data.x⁻¹ old) at hnew
  rw [z_act, inv_inv] at hnew
  have hback := Subgroup.mem_map_equiv.mp hnew
  change data.x⁻¹ * vector * data.x ∈ ZAt Γ old at hback
  rwa [mul_assoc, hcomm, inv_mul_cancel_left] at hback

public theorem mixed_actor_nontrivial_action
    {G : Type u} [Group G] [Finite G] {T A B : Subgroup G}
    (ctx : SectionNineLocalContext G T A B)
    (e : ((stabilizer ctx.Γ ctx.criticalPath.a) ⧸
      pCore 2 (stabilizer ctx.Γ ctx.criticalPath.a)) ≃* Equiv.Perm (Fin 3))
    (hb : 1 < ctx.criticalPath.length)
    (hlarge : 4 < Nat.card (ZAt ctx.Γ ctx.criticalPath.a))
    (first : FirstConfigurationData ctx)
    (second : SecondConfigurationData ctx first)
    (config : NormalizedGeometry ctx first second) :
    let m := ctx.Γ.act config.g (ctx.Γ.act first.extraction.x⁻¹ first.l)
    let actor := ZAt ctx.Γ m ⊓ GAt ctx.Γ ctx.criticalPath.a
    ¬ ZAt ctx.Γ ctx.criticalPath.a ≤ Subgroup.centralizer (actor : Set G) := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let conjugation := MulAut.conj config.g⁻¹
  let oldFirst := Γ.act first.extraction.x⁻¹ first.l
  let oldSecond := Γ.act second.extraction.x⁻¹ second.l
  let m := Γ.act config.g oldFirst
  let old := Γ.act config.g first.l
  have hsecondGroup : (GAt Γ oldSecond).map conjugation.toMonoidHom = GAt Γ cp.a := by
    change conjugateBy (stabilizer Γ oldSecond) config.g⁻¹ = _
    rw [← stabilizer_act, config.maps_new_vertex]
  have hfirstCenter : (ZAt Γ oldFirst).map conjugation.toMonoidHom = ZAt Γ m := by
    change (z Γ oldFirst).map (MulAut.conj config.g⁻¹).toMonoidHom = _
    rw [← z_act]
  have holdCenter : (ZAt Γ first.l).map conjugation.toMonoidHom = ZAt Γ old := by
    change (z Γ first.l).map (MulAut.conj config.g⁻¹).toMonoidHom = _
    rw [← z_act]
  have hinner : Nat.card (ZAt Γ m ⊓ GAt Γ cp.a : Subgroup G) =
      2 * Nat.card (ZAt Γ m ⊓ ZAt Γ old : Subgroup G) := by
    rw [← hfirstCenter, ← hsecondGroup, ← holdCenter,
      ← Subgroup.map_inf _ _ _ conjugation.injective,
      ← Subgroup.map_inf _ _ _ conjugation.injective,
      Subgroup.card_map_of_injective conjugation.injective,
      Subgroup.card_map_of_injective conjugation.injective]
    exact (four_center_indices ctx e hb hlarge first second).2.1
  have hnot : ¬ ZAt Γ m ⊓ GAt Γ cp.a ≤ ZAt Γ old := by
    intro hle
    have hbound := Subgroup.card_le_of_le (le_inf inf_le_left hle)
    have hpositive : 0 < Nat.card (ZAt Γ m ⊓ ZAt Γ old : Subgroup G) := Nat.card_pos
    omega
  have hresult := extracted_actor_not_centralized ctx.sectionSeven Γ cp.a
    (Γ.act config.g cp.a') old (VAt Γ cp.firstStep)
    (first.E.map conjugation.toMonoidHom) (first.A0.map conjugation.toMonoidHom)
    config.first_actor config.first_actor_initial
    ((lemma_seven_four ctx.sectionSeven Γ cp).first_containment.1 config.first_actor_initial)
    config.first_geometry
  rw [config.first_new_vertex] at hresult
  exact hresult hnot

end Stellmacher.SectionNine.LocalLonger
