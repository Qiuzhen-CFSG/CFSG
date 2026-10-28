module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Higher.OrbitGeometry.Replacement.Source

/-!
# Separating regular critical windows and preserving their midpoint

At the last turn, the critical endpoint is a moving neighbor. If the two
incident Z-layers agreed, relative normality would identify the endpoint's
Z-layer with the vertex four steps earlier, contradicting reversed
criticality. Reversal gives the first separation. The actual prescribed
replacement shifts the middle turn to the last turn and gives the middle
separation without changing the original vertices.

Three right extensions now embed any regular critical eight-window into
the original source-path format while retaining its midpoint at index four
and its endpoint at index eight. The source orbit-containment theorem thus
applies to that endpoint under the exact midpoint stabilizer. In particular
this interface accepts the already constructed delta critical window.

Source: Meierfrankenfeld--Stellmacher (1993), (4.4.4), (4.5.2)(i), and
(4.5.4)(ii), printed pp.894, 897--899.
-/

public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Higher.OrbitGeometry.Replacement.Regularity
open PathCentrality PathCentrality.RegularPaths Early.Orbit.Source Early.PathExtension
variable {M : Type*} [Group M] [Finite M] {R L : Subgroup M}
  {geometry : Geometry R} {source : LocalSource L R}

omit [Finite M] in
include geometry in
private theorem common_neighbor_unique {a c t u : Vertex R}
    (h : (cosetGraph R).dist a c = 2)
    (hat : Adjacent R a t) (hct : Adjacent R c t)
    (hau : Adjacent R a u) (hcu : Adjacent R c u) : t = u := by
  let p : (cosetGraph R).Walk a c :=
    .cons ((cosetGraph_adj R _ _).mpr hat) (.cons ((cosetGraph_adj R _ _).mpr hct).symm .nil)
  let q : (cosetGraph R).Walk a c :=
    .cons ((cosetGraph_adj R _ _).mpr hau) (.cons ((cosetGraph_adj R _ _).mpr hcu).symm .nil)
  have hp : p.IsPath := p.isPath_of_length_eq_dist (by change 2 = _; exact h.symm)
  have hq : q.IsPath := q.isPath_of_length_eq_dist (by change 2 = _; exact h.symm)
  have he : p = q := Subtype.mk.inj
    (geometry.tree.isAcyclic.subsingleton_path _ _ |>.elim ⟨p,hp⟩ ⟨q,hq⟩)
  exact congrArg (fun w => w.getVert 1) he

private theorem seed_eq_across_turn (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) {x c y t u : Vertex R}
    (hx : color R x = false) (hc : color R c = false)
    (hxt : Adjacent R x t) (hct : Adjacent R c t)
    (hyu : Adjacent R y u) (hcu : Adjacent R c u)
    (hm : x ∈ Escape.movingNeighbors geometry c)
    (g : FreeAmalgam R) (hg : g ∈ stabilizer R c) (hgy : act R g x = y)
    (heq : Z R t = Z R u) : Z R x = Z R y := by
  have hgc : act R g c = c := hg
  have hgt : act R g t = u := by
    apply common_neighbor_unique (geometry := geometry)
      (a := y) (c := c) (by
        rw [← hgy, ← hgc, dist_act]
        rw [SimpleGraph.dist_comm]
        exact hm.1)
    · simpa only [hgy] using (adjacent_act_iff R g _ _).mpr hxt
    · simpa only [hgc] using (adjacent_act_iff R g _ _).mpr hct
    · exact hyu
    · exact hcu
  have hgi : g⁻¹ ∈ normalizer (Z R t : Set (FreeAmalgam R)) := by
    rw [mem_normalizer_iff_map_conj_eq]
    change (Z R t).map (MulAut.conj g⁻¹).toMonoidHom = _
    rw [← Z_act,hgt]
    exact heq.symm
  have hgn := (normalizer (Z R t : Set (FreeAmalgam R))).inv_mem hgi
  simp only [inv_inv] at hgn
  have hgP : g ∈ relativeNormalizer R c t :=
    Unequal.edge_Z_normalizer_le common earlier hc hct ⟨hg,hgn⟩
  have hgZ := Z_normalized_by_relativeNormalizer_of_moving common earlier hx hc hxt hct hm hgP
  have hmap := mem_normalizer_iff_map_conj_eq.mp
    ((normalizer (Z R x : Set (FreeAmalgam R))).inv_mem hgZ)
  change (Z R x).map (MulAut.conj g⁻¹).toMonoidHom = _ at hmap
  rw [← Z_act,hgy] at hmap
  exact hmap.symm

/-- Equal edge layers at the last turn contradict the original critical pair. -/
theorem last_separation (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) {a a' : Vertex R}
    (p : CriticalPath R geometry a a') (hp : HasTurnConjugators R p) :
    Z R (p.walk.getVert 5) ≠ Z R (p.walk.getVert 7) := by
  have hl : p.walk.length = 8 := p.length_eq_b.trans earlier.distance
  have h8 : p.walk.getVert 8 = a' := by rw [← hl,SimpleGraph.Walk.getVert_length]
  have hc : color R (p.walk.getVert 6) = false :=
    (p.vertex_color (i := 6) (by omega)).mpr (by decide)
  have h76 : Adjacent R (p.walk.getVert 6) (p.walk.getVert 7) :=
    (cosetGraph_adj R _ _).mp (p.walk.adj_getVert_succ (i := 6) (by omega))
  have h87 : Adjacent R a' (p.walk.getVert 7) := by
    simpa only [h8] using adjacent_symm R
      ((cosetGraph_adj R _ _).mp (p.walk.adj_getVert_succ (i := 7) (by omega)))
  have h45 : Adjacent R (p.walk.getVert 4) (p.walk.getVert 5) :=
    (cosetGraph_adj R _ _).mp (p.walk.adj_getVert_succ (i := 4) (by omega))
  have h65 : Adjacent R (p.walk.getVert 6) (p.walk.getVert 5) := adjacent_symm R
    ((cosetGraph_adj R _ _).mp (p.walk.adj_getVert_succ (i := 5) (by omega)))
  have hm : a' ∈ Escape.movingNeighbors geometry (p.walk.getVert 6) := by
    apply Escape.Propagation.RadiusFour.Forward.Reversal.critical_endpoint_moving
      source (by rw [earlier.distance]; decide) p.start_color p.critical
    constructor
    · rw [p.dist_end,hl]
    · rw [p.dist_start (by omega : 6 ≤ p.walk.length), ← p.shortest,hl]
  obtain ⟨g,hg,hgturn⟩ := hp 6 (by decide) (by decide) (by omega)
  change act R g (p.walk.getVert 8) = p.walk.getVert 4 at hgturn
  rw [h8] at hgturn
  intro heq
  have he := seed_eq_across_turn common earlier p.end_color hc h87 h76 h45 h65
    hm g hg hgturn heq.symm
  have hQ : Z R a' ≤ Q R a := by
    rw [he]
    have h4c : color R (p.walk.getVert 4) = false :=
      (p.vertex_color (i := 4) (by omega)).mpr (by decide)
    apply Z_le_Q_of_dist_lt R _ (geometry.exists_critical _
      h4c)
    rw [SimpleGraph.dist_comm,p.dist_start (by omega : 4 ≤ p.walk.length),geometry.distance_constant _ h4c]
    change 4 < geometry.b R
    rw [earlier.distance]
    decide
  exact (common.critical_reverse _ p.start_color _ p.end_color p.critical).2 hQ

/-- All three turns of the supplied regular critical window are separated. -/
theorem regular_separated (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) {a a' : Vertex R}
    (p : CriticalPath R geometry a a') (hp : HasTurnConjugators R p) :
    ∀ i, Even i → 2 ≤ i → i + 2 ≤ p.walk.length →
      Z R (p.walk.getVert (i-1)) ≠ Z R (p.walk.getVert (i+1)) := by
  have hl : p.walk.length = 8 := p.length_eq_b.trans earlier.distance
  have hlast := last_separation common earlier p hp
  have hfirst : Z R (p.walk.getVert 1) ≠ Z R (p.walk.getVert 3) := by
    have h := last_separation common earlier (p.reverse common) (hp.reverse R common)
    simpa only [CriticalPath.reverse,SimpleGraph.Walk.getVert_reverse,hl,Nat.reduceSub] using h.symm
  have hmiddle : Z R (p.walk.getVert 3) ≠ Z R (p.walk.getVert 5) := by
    obtain ⟨g,hg,hn,_⟩ := exists_replacement common earlier p hp
    let q := p.conjugateShift (by rw [earlier.distance]; decide) g hg hn
    have hq : HasTurnConjugators R q := hasTurnConjugators_conjugateShift p
      (by rw [earlier.distance]; decide) hp g hg hn
    have overlap (i : ℕ) (hi : i ≤ 6) : q.walk.getVert (i+2) = p.walk.getVert i := by
      unfold q CriticalPath.conjugateShift
      exact p.prepend_two_overlap _ _ _ _ _ (by omega)
    simpa only [overlap 3 (by decide),overlap 5 (by decide)] using last_separation common earlier q hq
  intro i hi hi2 hiend
  rw [hl] at hiend
  have hic : i = 2 ∨ i = 4 ∨ i = 6 := by rw [Nat.even_iff] at hi; omega
  rcases hic with rfl | rfl | rfl
  · exact hfirst
  · exact hmiddle
  · exact hlast

private theorem append_right (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) {n : ℕ} (w : RegularSegment R n) :
    Nonempty (Σ' v : RegularSegment R (n+1),
      ∀ i, i ≤ w.walk.length → v.walk.getVert i = w.walk.getVert i) := by
  obtain ⟨⟨v,hv⟩⟩ := prepend earlier.distance
    (fun _ _ p hp => exists_replacement common earlier p hp) (w.reverse common earlier.distance)
  refine ⟨⟨v.reverse common earlier.distance, ?_⟩⟩
  intro i hi
  rw [w.length_eq] at hi
  rw [RegularSegment.reverse_getVert,
    show 8 + 2 * (n+1) - i = (8 + 2*n-i) + 2 by omega,
    hv,RegularSegment.reverse_getVert,
    show 8 + 2*n-(8+2*n-i)=i by omega]

/-- Three right extensions preserve every vertex of the given eight-window. -/
theorem sourcePath_preserving_start_window (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) {a a' : Vertex R}
    (p : CriticalPath R geometry a a') (hp : HasTurnConjugators R p) :
    Nonempty (Σ' q : Early.SourcePath R (p.walk.getVert 4),
      ∀ i, i ≤ 8 → q.walk.getVert i = p.walk.getVert i) := by
  have hl : p.walk.length = 8 := p.length_eq_b.trans earlier.distance
  let w : RegularSegment R 0 := {
    first := a
    last := a'
    walk := p.walk
    start_color := p.start_color
    length_eq := by simpa using hl
    isPath := p.isPath
    turns := hp
    separated := regular_separated common earlier p hp
    critical := by
      intro i _ hi
      have hi0 : i = 0 := by omega
      subst i
      simp only [Nat.zero_add,SimpleGraph.Walk.getVert_zero, ← hl,SimpleGraph.Walk.getVert_length]
      exact ⟨p.shortest.symm,p.critical.2⟩ }
  obtain ⟨⟨w₁,h₁⟩⟩ := append_right common earlier w
  obtain ⟨⟨w₂,h₂⟩⟩ := append_right common earlier w₁
  obtain ⟨⟨w₃,h₃⟩⟩ := append_right common earlier w₂
  have hw (i : ℕ) (hi : i ≤ 8) : w₃.walk.getVert i = p.walk.getVert i := by
    rw [h₃ i (by rw [w₂.length_eq]; omega),h₂ i (by rw [w₁.length_eq]; omega),
      h₁ i (by change i ≤ p.walk.length; omega)]
  obtain ⟨⟨q,hq⟩⟩ := sourcePath_of_segment common earlier w₃
  refine ⟨⟨{ q with center_eq := q.center_eq.trans (hw 4 (by decide)) }, ?_⟩⟩
  intro i hi
  exact (hq i).trans (hw i hi)

/-- Apply source (4.5.4)(ii) to the actual endpoint and midpoint stabilizer. -/
theorem endpoint_orbit_le_Q (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) {a a' : Vertex R}
    (p : CriticalPath R geometry a a') (hp : HasTurnConjugators R p) :
    NormalizerTransfer.conjugatesIn (Z R a') (stabilizer R (p.walk.getVert 4)) ≤ Q R a' := by
  obtain ⟨⟨q,hq⟩⟩ := sourcePath_preserving_start_window common earlier p hp
  have h8 : q.walk.getVert 8 = a' := (hq 8 (by decide)).trans (by
    rw [← p.length_eq_b.trans earlier.distance,SimpleGraph.Walk.getVert_length])
  simpa only [h8] using Source.source_orbit_le_Q common earlier q

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Higher.OrbitGeometry.Replacement.Regularity
