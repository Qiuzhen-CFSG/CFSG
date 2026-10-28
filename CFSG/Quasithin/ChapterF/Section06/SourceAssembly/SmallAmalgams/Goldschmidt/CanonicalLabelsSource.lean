module
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.Goldschmidt.EdgeCenterSource

/-!
# Canonical labels from the original large source action

The centered intervals and neighbor product are constructed from the original
first singular arc. Radius one is impossible, and every edge center is cyclic.
These theorems supply every field of the canonical-label record. If the first
singular arc starts in the other vertex orbit, the same equivariant coset-graph
isomorphism transports its labels and literal track interval back.

Source: Goldschmidt, *Automorphisms of trivalent graphs* (1980), (6.4)--(6.8),
printed pp.397--400.
-/

public section
open Subgroup SimpleGraph Theory.GroupAction.CubicTree Subgroup.CosetGeometry
namespace CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt
variable {G : Type*} [Group G] {F : Bool → Subgroup G} {s : ℕ}

/-- Canonical data in the orientation of the first singular arc. -/
theorem LargeTreeSource.canonicalLabels_of_first_singular
    (h : LargeTreeSource F s) {v : RankTwo.Vertex F}
    (p : BasedWalk (RankTwo.graph F) s v) (hp : p.Nonbacktracking)
    (hn : ¬ RightRegular (A := G) p) (hv : v.type=false) :
    Nonempty (CanonicalLabelSetup F s) := by
  obtain ⟨t,z,d,c,r,f,hL,hR,hFL,hFR,hr,hfz,ho,hc,he,hb,hm,hp'⟩ :=
    h.exists_centered_source_labels p hp hn hv
  subst z
  have hr' : r=2 ∨ Odd r ∧ 3≤r := by
    rcases hr with hr | hr
    · subst r
      exact (h.radius_one_impossible p hp hn hv (t.vertex c).type f ho hc he
        (fun a ha b hb' => hb a ha b hb' (by have := h.five_le; omega))
        (fun a ha b hb' => hm a ha (by have := h.five_le; omega) b hb')).elim
    · exact hr
  exact ⟨⟨(t.vertex c).type,r,f,ho,hc,he,hr',hb,hm,hp',
    h.edge_center_cyclic p hp hn hv,t,c,rfl,d,hL,hR,hFL,hFR⟩⟩

private theorem swap_fixed_iff (g : G) (v : RankTwo.Vertex F) :
    g • RankTwo.swapGraphIso F v = RankTwo.swapGraphIso F v ↔ g • v=v := by
  change g • RankTwo.swapVertex F v = RankTwo.swapVertex F v ↔ g • v=v
  rw [← RankTwo.swapVertex_smul]
  exact (RankTwo.swapGraphIso F).injective.eq_iff

private theorem swap_stabilizer (v : RankTwo.Vertex F) :
    RankTwo.stabilizer (RankTwo.swapFamily F) (RankTwo.swapGraphIso F v) =
      RankTwo.stabilizer F v := by
  ext g
  exact swap_fixed_iff g v

private theorem swap_symm_smul (g : G) (v : RankTwo.Vertex (RankTwo.swapFamily F)) :
    (RankTwo.swapGraphIso F).symm (g • v) = g • (RankTwo.swapGraphIso F).symm v := by
  apply (RankTwo.swapGraphIso F).injective
  rw [RelIso.apply_symm_apply]
  change g • v = RankTwo.swapVertex F (g • (RankTwo.swapGraphIso F).symm v)
  rw [RankTwo.swapVertex_smul]
  exact congrArg (g • ·) ((RankTwo.swapGraphIso F).apply_symm_apply v).symm

private theorem swap_symm_type (v : RankTwo.Vertex (RankTwo.swapFamily F)) :
    ((RankTwo.swapGraphIso F).symm v).type = !v.type := by
  have h := RankTwo.swapVertex_type F ((RankTwo.swapGraphIso F).symm v)
  have he := (RankTwo.swapGraphIso F).apply_symm_apply v
  change (RankTwo.swapVertex F ((RankTwo.swapGraphIso F).symm v)).type =
    !((RankTwo.swapGraphIso F).symm v).type at h
  change ((RankTwo.swapGraphIso F) ((RankTwo.swapGraphIso F).symm v)).type =
    !((RankTwo.swapGraphIso F).symm v).type at h
  rw [he] at h
  simpa only [Bool.not_not] using congrArg Bool.not h.symm

private theorem swap_dist (h : CubicTreeAction F) (v w : RankTwo.Vertex F) :
    (RankTwo.graph (RankTwo.swapFamily F)).dist
      (RankTwo.swapGraphIso F v) (RankTwo.swapGraphIso F w) = (RankTwo.graph F).dist v w := by
  let e := RankTwo.swapGraphIso F
  apply le_antisymm
  · obtain ⟨p,hp⟩ := (h.tree.connected v w).exists_walk_length_eq_dist
    calc
      _ ≤ (p.map e.toHom).length := SimpleGraph.dist_le _
      _ = _ := (SimpleGraph.Walk.length_map _ _).trans hp
  · obtain ⟨p,hp⟩ := (h.swap.tree.connected (e v) (e w)).exists_walk_length_eq_dist
    have hh := SimpleGraph.dist_le (p.map e.symm.toHom)
    change (RankTwo.graph F).dist (e.symm (e v)) (e.symm (e w)) ≤ (p.map e.symm.toHom).length at hh
    simpa only [RelIso.symm_apply_apply, SimpleGraph.Walk.length_map, hp] using hh

private def pullbackTrack (t : Track (RankTwo.graph (RankTwo.swapFamily F)) G) :
    Track (RankTwo.graph F) G where
  vertex i := (RankTwo.swapGraphIso F).symm (t.vertex i)
  injective := (RankTwo.swapGraphIso F).symm.injective.comp t.injective
  adjacent i := (RankTwo.swapGraphIso F).symm.map_rel_iff.mpr (t.adjacent i)
  translation := t.translation
  translate i := by rw [← swap_symm_smul, t.translate]

private theorem pullback_edge (t : Track (RankTwo.graph (RankTwo.swapFamily F)) G) (i : ℤ) :
    (pullbackTrack t).edgeStabilizer i = t.edgeStabilizer i := by
  change RankTwo.stabilizer F ((RankTwo.swapGraphIso F).symm (t.vertex i)) ⊓
    RankTwo.stabilizer F ((RankTwo.swapGraphIso F).symm (t.vertex (i+1))) = _
  rw [← swap_stabilizer (F:=F) ((RankTwo.swapGraphIso F).symm (t.vertex i)),
    ← swap_stabilizer (F:=F) ((RankTwo.swapGraphIso F).symm (t.vertex (i+1)))]
  simp only [RelIso.apply_symm_apply]
  rfl

private def pullbackInterval (t : Track (RankTwo.graph (RankTwo.swapFamily F)) G)
    {z : G} (d : t.CentralInterval z) : (pullbackTrack t).CentralInterval z where
  fixedLeft := d.fixedLeft
  fixedRight := d.fixedRight
  centralLeft := d.centralLeft
  centralRight := d.centralRight
  fixed_iff i := by
    change z • (RankTwo.swapGraphIso F).symm (t.vertex i) =
      (RankTwo.swapGraphIso F).symm (t.vertex i) ↔ _
    rw [← swap_symm_smul, (RankTwo.swapGraphIso F).symm.injective.eq_iff]
    exact d.fixed_iff i
  central_lt := d.central_lt
  central i hi hj := by
    unfold Track.CentralEdge
    rw [pullback_edge]
    exact d.central i hi hj
  maximal a b hab hc := d.maximal a b hab (by
    intro i hi hj
    have hh := hc i hi hj
    unfold Track.CentralEdge at hh
    rw [pullback_edge] at hh
    exact hh)

/-- Changing the vertex-type orientation preserves all canonical source data. -/
private def canonicalLabels_of_swap (h : CubicTreeAction F)
    (d : CanonicalLabelSetup (RankTwo.swapFamily F) s) : CanonicalLabelSetup F s := by
  let e := RankTwo.swapGraphIso F
  have ht (v : RankTwo.Vertex F) (hv : v.type = !d.side) : (e v).type=d.side := by
    change (RankTwo.swapVertex F v).type=d.side
    rw [RankTwo.swapVertex_type,hv,Bool.not_not]
  let t := pullbackTrack d.track
  have hlabel : d.label (e (t.vertex d.center)) = d.label (d.track.vertex d.center) := by
    exact congrArg d.label (e.apply_symm_apply _)
  refine {
    side := !d.side
    radius := d.radius
    label := fun v => d.label (e v)
    order_two := fun v hv => d.order_two (e v) (ht v hv)
    central := ?_
    conjugate := ?_
    radius_cases := d.radius_cases
    fixes_ball := ?_
    moves_sphere := ?_
    neighbor_product := ?_
    edge_center_cyclic := ?_
    track := t
    center := d.center
    center_type := ?_
    interval := {
      fixedLeft := d.interval.fixedLeft
      fixedRight := d.interval.fixedRight
      centralLeft := d.interval.centralLeft
      centralRight := d.interval.centralRight
      fixed_iff := by
        intro i
        rw [hlabel]
        exact (pullbackInterval d.track d.interval).fixed_iff i
      central_lt := d.interval.central_lt
      central := by
        intro i hi hj
        rw [hlabel]
        exact (pullbackInterval d.track d.interval).central i hi hj
      maximal := by
        intro a b hab hc
        apply (pullbackInterval d.track d.interval).maximal a b hab
        intro i hi hj
        have hh := hc i hi hj
        rw [hlabel] at hh
        exact hh }
    central_left := ?_
    central_right := ?_
    fixed_left := ?_
    fixed_right := ?_ }
  · intro v hv
    simpa only [e, swap_stabilizer] using d.central (e v) (ht v hv)
  · intro g v hv
    exact (congrArg d.label (RankTwo.swapVertex_smul F g v)).trans (d.conjugate g (e v) (ht v hv))
  · intro v hv w hr hs
    exact (swap_fixed_iff _ _).mp (d.fixes_ball (e v) (ht v hv) (e w)
      ((swap_dist h v w).symm ▸ hr) ((swap_dist h v w).symm ▸ hs))
  · intro v hv hr w hw hh
    apply d.moves_sphere (e v) (ht v hv) hr (e w) ((swap_dist h v w).trans hw)
    exact (swap_fixed_iff _ _).mpr hh
  · intro v a b c hva hvb hvc hab hac hbc ha
    exact d.neighbor_product (e v) (e a) (e b) (e c)
      (e.map_rel_iff.mpr hva) (e.map_rel_iff.mpr hvb) (e.map_rel_iff.mpr hvc)
      (fun he => hab (e.injective he)) (fun he => hac (e.injective he))
      (fun he => hbc (e.injective he)) (ht a ha)
  · intro v w hvw
    have hS : RankTwo.stabilizer (RankTwo.swapFamily F) (e v) ⊓
        RankTwo.stabilizer (RankTwo.swapFamily F) (e w) =
        RankTwo.stabilizer F v ⊓ RankTwo.stabilizer F w :=
      congrArg₂ (fun A B : Subgroup G => A ⊓ B) (swap_stabilizer v) (swap_stabilizer w)
    exact (centerCongr (MulEquiv.subgroupCongr hS)).isCyclic.mp
      (d.edge_center_cyclic (e v) (e w) (e.map_rel_iff.mpr hvw))
  · exact (swap_symm_type _).trans (congrArg Bool.not d.center_type)
  · simpa only using d.central_left
  · simpa only using d.central_right
  · simpa only using d.fixed_left
  · simpa only using d.fixed_right

/-- Goldschmidt (6.4)--(6.8), for the actual original source in either orientation. -/
theorem canonicalLabelsInput : CanonicalLabelsInput := by
  intro G _ F s h
  obtain ⟨v,p,hp,hn⟩ := h.singular
  cases hv : v.type with
  | false => exact h.canonicalLabels_of_first_singular p hp hn hv
  | true =>
    obtain ⟨w,q,hw,hq,hqn⟩ := singular_swap p hv hp hn
    obtain ⟨d⟩ := h.swap.canonicalLabels_of_first_singular q hq hqn hw
    exact ⟨canonicalLabels_of_swap h.action.toCubicTreeAction d⟩

end CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt
