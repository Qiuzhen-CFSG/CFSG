module
public import Stellmacher.SectionNine.NineThreeSecondCenterRelations
public import Stellmacher.SectionNine.NineThreeSelectedEdgeNormalization
public import Stellmacher.SectionFiveToSeven.Result7_8.GeometricConjugation
public import Stellmacher.BaumannMap

/-!
# Both geometric extractions with the selected edge normalized

Retain the actual first and second configurations of (9.3). A single graph
actor fixing the first step carries the second new vertex to the initial
vertex and its selected edge Sylow to the distinguished subgroup. The
record retains this actor, both mapped geometric configurations, their
exact mapped conjugators and new vertices, the first prescribed actor in
the initial center, and the second prescribed actor in the first new center.
The second residual satisfies the original selected Baumann bound with T.

Select a first actor in the second new center outside the first new
stabilizer, using the proved second center relations. Change only that
actor in the first extraction. Selected-edge normalization supplies the
common graph actor. Apply geometric conjugation to both extractions, and
use its fixed first step to identify the mapped first actor module with
the original one. Center covariance gives both prescribed-actor memberships;
residual and injective Baumann covariance transport the selected bound.

This makes the normalization before (9.3)(4) explicit without replacing the
ambient context or critical path. Source: Stellmacher, Journal of Algebra
190 (1997), p.49, `refs/files/stellmacher-n-group.pdf`.
-/

namespace Stellmacher.SectionNine
open Later SectionsFiveToSeven CosetGraphContext SevenSix
universe u

/-- Both actual geometric extractions normalized by the same graph actor,
including the exact selected Sylow and mapped-conjugator equations. -/
public structure NineThreeNormalizedGeometry
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (first : NineThreeFirstConfigurationData ctx)
    (second : NineThreeSecondConfigurationData ctx first) where
  g : G
  g_mem : g ∈ GAt ctx.Γ ctx.criticalPath.firstStep
  fixes_firstStep : ctx.Γ.act g ctx.criticalPath.firstStep = ctx.criticalPath.firstStep
  maps_new_vertex : ctx.Γ.act g (ctx.Γ.act second.extraction.x⁻¹ second.l) = ctx.criticalPath.a
  maps_sylow : (sylowTwoAmbient (GAt ctx.Γ ctx.criticalPath.firstStep ⊓
      GAt ctx.Γ (ctx.Γ.act second.extraction.x⁻¹ second.l)) second.new_sylow).map
        (MulAut.conj g⁻¹).toMonoidHom = T
  first_actor : G
  first_actor_initial : first_actor ∈ ZAt ctx.Γ ctx.criticalPath.a
  first_geometry : NineThreeGeometricData ctx.Γ
    (ctx.Γ.act g ctx.criticalPath.a') (ctx.Γ.act g first.l)
    (VAt ctx.Γ ctx.criticalPath.firstStep)
    (first.E.map (MulAut.conj g⁻¹).toMonoidHom)
    (first.A0.map (MulAut.conj g⁻¹).toMonoidHom) first_actor
  first_x : first_geometry.x = (MulAut.conj g⁻¹) first.extraction.x
  first_new_vertex : ctx.Γ.act first_geometry.x⁻¹ (ctx.Γ.act g first.l) =
    ctx.Γ.act g (ctx.Γ.act first.extraction.x⁻¹ first.l)
  second_geometry : NineThreeGeometricData ctx.Γ ctx.criticalPath.firstStep
    (ctx.Γ.act g second.l) (VAt ctx.Γ (ctx.Γ.act g ctx.criticalPath.a'))
    (second.E.map (MulAut.conj g⁻¹).toMonoidHom)
    (second.A0.map (MulAut.conj g⁻¹).toMonoidHom) ((MulAut.conj g⁻¹) second.actor)
  second_x : second_geometry.x = (MulAut.conj g⁻¹) second.extraction.x
  second_new_vertex : ctx.Γ.act second_geometry.x⁻¹ (ctx.Γ.act g second.l) = ctx.criticalPath.a
  second_actor_center : (MulAut.conj g⁻¹) second.actor ∈
    ZAt ctx.Γ (ctx.Γ.act g (ctx.Γ.act first.extraction.x⁻¹ first.l))
  residual_baumann : twoResidualIn (second.E.map (MulAut.conj g⁻¹).toMonoidHom) ≤
    ⁅twoResidualIn (second.E.map (MulAut.conj g⁻¹).toMonoidHom), baumannIn T⁆

/-- Normalize both supplied configurations while preserving their selected
residual and all exact mapped witnesses. -/
public theorem nine_three_normalized_geometry
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : 1 < ctx.criticalPath.length)
    (hlarge : 4 < Nat.card (ZAt ctx.Γ ctx.criticalPath.a))
    (first : NineThreeFirstConfigurationData ctx)
    (second : NineThreeSecondConfigurationData ctx first) :
    Nonempty (NineThreeNormalizedGeometry ctx first second) := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let m := Γ.act first.extraction.x⁻¹ first.l
  let n := Γ.act second.extraction.x⁻¹ second.l
  obtain ⟨g, hg, hgn, hSyl⟩ := nine_three_selected_edge_normalization
    ctx.toLocalContext n second.extraction.neighbor second.new_sylow
  change g ∈ GAt Γ cp.firstStep at hg
  change Γ.act g n = cp.a at hgn
  change (sylowTwoAmbient (GAt Γ cp.firstStep ⊓ GAt Γ n) second.new_sylow).map
    (MulAut.conj g⁻¹).toMonoidHom = T at hSyl
  let c := MulAut.conj g⁻¹
  have hfix : Γ.act g cp.firstStep = cp.firstStep :=
    (Set.ext_iff.mp (Γ.stabilizer_def cp.firstStep) g).mp hg
  have hVfirst : (VAt Γ cp.firstStep).map c.toMonoidHom = VAt Γ cp.firstStep := by
    change (v Γ cp.firstStep).map (MulAut.conj g⁻¹).toMonoidHom = _
    rw [← v_act, hfix]
  have hVend : (VAt Γ cp.a').map c.toMonoidHom = VAt Γ (Γ.act g cp.a') := by
    change (v Γ cp.a').map (MulAut.conj g⁻¹).toMonoidHom = v Γ (Γ.act g cp.a')
    rw [v_act]
  have hnot : ¬ ZAt Γ n ≤ GAt Γ m :=
    (nine_three_second_center_relations ctx hb hlarge first second).2.2
  obtain ⟨actor, ha, haNot⟩ := Set.not_subset.mp hnot
  let oldFirst : NineThreeGeometricData Γ cp.a' first.l
      (VAt Γ cp.firstStep) first.E first.A0 actor :=
    { first.extraction with actor_outside := haNot }
  have hfirst := geometric_extraction_conjugation Γ cp.a' first.l
    (VAt Γ cp.firstStep) first.E first.A0 actor oldFirst g
  change ∃ data : NineThreeGeometricData Γ (Γ.act g cp.a') (Γ.act g first.l)
      ((VAt Γ cp.firstStep).map c.toMonoidHom) (first.E.map c.toMonoidHom)
      (first.A0.map c.toMonoidHom) (c actor),
      data.x = c first.extraction.x ∧
        Γ.act data.x⁻¹ (Γ.act g first.l) = Γ.act g m at hfirst
  rw [hVfirst] at hfirst
  obtain ⟨firstNew, hx, hm⟩ := hfirst
  have hsecond := geometric_extraction_conjugation Γ cp.firstStep second.l
    (VAt Γ cp.a') second.E second.A0 second.actor second.extraction g
  change ∃ data : NineThreeGeometricData Γ (Γ.act g cp.firstStep) (Γ.act g second.l)
      ((VAt Γ cp.a').map c.toMonoidHom) (second.E.map c.toMonoidHom)
      (second.A0.map c.toMonoidHom) (c second.actor),
      data.x = c second.extraction.x ∧
        Γ.act data.x⁻¹ (Γ.act g second.l) = Γ.act g n at hsecond
  rw [hfix, hVend, hgn] at hsecond
  obtain ⟨secondNew, hy, hn⟩ := hsecond
  have haInitial : c actor ∈ ZAt Γ cp.a := by
    rw [← hgn]
    change c actor ∈ z Γ (Γ.act g n)
    rw [z_act]
    exact Subgroup.mem_map_of_mem c.toMonoidHom ha
  have haSecond : c second.actor ∈ ZAt Γ (Γ.act g m) := by
    change c second.actor ∈ z Γ (Γ.act g m)
    rw [z_act]
    exact Subgroup.mem_map_of_mem c.toMonoidHom second.actor_first_center
  let W := sylowTwoAmbient (GAt Γ cp.firstStep ⊓ GAt Γ n) second.new_sylow
  have hRmap : (twoResidualIn second.E).map c.toMonoidHom =
      twoResidualIn (second.E.map c.toMonoidHom) :=
    map_twoResidualAmbient_of_subgroup_image second.E c.toMonoidHom _ rfl
  have hBmap : (baumannIn W).map c.toMonoidHom = baumannIn T := by
    rw [show (baumannIn W).map c.toMonoidHom = baumannIn (W.map c.toMonoidHom) from
      baumann_map_injective c.toMonoidHom c.injective W, hSyl]
  have hres : twoResidualIn (second.E.map c.toMonoidHom) ≤
      ⁅twoResidualIn (second.E.map c.toMonoidHom), baumannIn T⁆ := by
    have hh := Subgroup.map_mono (f := c.toMonoidHom) second.residual_baumann
    change (twoResidualIn second.E).map c.toMonoidHom ≤
      (⁅twoResidualIn second.E, baumannIn W⁆).map c.toMonoidHom at hh
    rwa [Subgroup.map_commutator, hRmap, hBmap] at hh
  exact ⟨{ g := g
           g_mem := hg
           fixes_firstStep := hfix
           maps_new_vertex := hgn
           maps_sylow := hSyl
           first_actor := c actor
           first_actor_initial := haInitial
           first_geometry := firstNew
           first_x := hx
           first_new_vertex := hm
           second_geometry := secondNew
           second_x := hy
           second_new_vertex := hn
           second_actor_center := haSecond
           residual_baumann := hres }⟩

end Stellmacher.SectionNine
