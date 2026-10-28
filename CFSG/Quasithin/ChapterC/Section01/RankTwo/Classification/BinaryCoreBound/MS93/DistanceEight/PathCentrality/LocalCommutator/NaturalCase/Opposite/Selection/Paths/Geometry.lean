module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.LocalCommutator.NaturalCase.Opposite.Selection.Paths.Source
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.Geometry.Paths

/-!
# Critical placement from the actual local orbit

An escaping conjugate of the original Z-layer supplies a two-edge prefix,
with the original common neighbor transported by the same element of G_c.
Append a shortest tail of length b-2. Critical minimality proves that this
walk is shortest and critical, and explicit vertex equations retain c and
its following vertex.

The orbit-escape condition is equivalent to existence of such a critical
placement before centralizer selection. Given a proved cover by the good
conjugates and the incident radius group, some good conjugate still escapes:
the incident radius group lies in the far kernel by critical minimality.
This constructs every field of PathPlacement. The source-only orbit escape
and local span cover remain separate mathematical obligations.

Source: Meierfrankenfeld--Stellmacher (1993), (4.4.1)(1), printed p.891.
-/

@[expose] public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.LocalCommutator.NaturalCase.Opposite.Selection
variable {M : Type*} [Group M] {R : Subgroup M} {geometry : Geometry R}

theorem incident_radius_le_kernel {c u e : Vertex R}
    (hc : color R c = false) (hcu : Adjacent R c u)
    (hd : (cosetGraph R).dist u e + 1 < geometry.b R) : V R u ≤ Q R e := by
  apply Escape.PairingControl.Geometry.V_le_of_h_neighbors hc hcu
  intro d hdu
  have hdc : color R d = false := by
    have h₁ := adjacent_color_ne R hcu
    have h₂ := adjacent_color_ne R hdu
    cases h : color R d <;> cases h' : color R u <;> simp_all
  apply Z_le_Q_of_dist_lt R d (geometry.exists_critical d hdc)
  rw [geometry.distance_constant d hdc]
  change (cosetGraph R).dist d e < geometry.b R
  have htri := (cosetGraph_connected R).dist_triangle (u := d) (v := u) (w := e)
  rw [SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj R _ _).mpr hdu)] at htri
  omega

/-- Append the conjugated original two-edge walk to a prescribed tail.
Critical minimality proves that the result is shortest. -/
noncomputable def criticalPathOfConjugate {a c e : Vertex R}
    (ha : color R a = false) (s : MovingSeed a c)
    (tail : (cosetGraph R).Walk c e) (hlen : tail.length + 2 = geometry.b R)
    (g : stabilizer R c) (hcrit : ¬ Z R (act R g a) ≤ Q R e) :
    CriticalPath R geometry (act R g a) e := by
  have hfix : act R (g : FreeAmalgam R) c = c := g.property
  have hadj : Adjacent R (act R g a) (act R g s.neighbor) :=
    (adjacent_act_iff R g _ _).mpr s.adjacent_start
  have hcenter : Adjacent R (act R g s.neighbor) c := by
    simpa only [hfix] using
      (adjacent_act_iff R g _ _).mpr (adjacent_symm R s.adjacent_center)
  let q : (cosetGraph R).Walk (act R g a) c :=
    .cons ((cosetGraph_adj R _ _).mpr hadj)
      (.cons ((cosetGraph_adj R _ _).mpr hcenter) .nil)
  let w := q.append tail
  have hw : w.length = geometry.b R := by
    simpa only [w, q, SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_cons,
      SimpleGraph.Walk.length_nil, Nat.add_comm] using hlen
  have hcolor : color R (act R g a) = false := (action_preserves_color R g a).trans ha
  have hmin := criticalDistance_le R (act R g a) (geometry.exists_critical _ hcolor) hcrit
  rw [geometry.distance_constant _ hcolor] at hmin
  change geometry.b R ≤ _ at hmin
  have hmax := SimpleGraph.dist_le w
  have hdist : (cosetGraph R).dist (act R g a) e = geometry.b R := by omega
  exact ⟨hcolor, w, hw.trans hdist.symm,
    hdist.trans (geometry.distance_constant _ hcolor).symm, hcrit⟩

/-- The prescribed two-edge prefix places c at position two. -/
theorem criticalPathOfConjugate_center {a c e : Vertex R}
    (ha : color R a = false) (s : MovingSeed a c)
    (tail : (cosetGraph R).Walk c e) (hlen : tail.length + 2 = geometry.b R)
    (g : stabilizer R c) (hcrit : ¬ Z R (act R g a) ≤ Q R e) :
    (criticalPathOfConjugate ha s tail hlen g hcrit).walk.getVert 2 = c := by
  change tail.getVert 0 = c
  exact SimpleGraph.Walk.getVert_zero tail

/-- The first vertex remains the image of the original common neighbor. -/
theorem criticalPathOfConjugate_first {a c e : Vertex R}
    (ha : color R a = false) (s : MovingSeed a c)
    (tail : (cosetGraph R).Walk c e) (hlen : tail.length + 2 = geometry.b R)
    (g : stabilizer R c) (hcrit : ¬ Z R (act R g a) ≤ Q R e) :
    (criticalPathOfConjugate ha s tail hlen g hcrit).walk.getVert 1 =
      act R g s.neighbor := rfl

/-- The third vertex is the first vertex of the unchanged tail. -/
theorem criticalPathOfConjugate_third {a c e : Vertex R}
    (ha : color R a = false) (s : MovingSeed a c)
    (tail : (cosetGraph R).Walk c e) (hlen : tail.length + 2 = geometry.b R)
    (g : stabilizer R c) (hcrit : ¬ Z R (act R g a) ≤ Q R e) :
    (criticalPathOfConjugate ha s tail hlen g hcrit).walk.getVert 3 =
      tail.getVert 1 := rfl

/-- Orbit escape is exactly the existence of an initial critical placement,
including the original common neighbor, before any centralizer selection. -/
theorem spanEscape_iff_critical_placement {a c : Vertex R}
    (ha : color R a = false) (hb : 2 ≤ geometry.b R) (s : MovingSeed a c) :
    SpanEscape geometry a c ↔
      ∃ (e : Vertex R) (g : stabilizer R c)
        (p : CriticalPath R geometry (act R g a) e),
        p.walk.getVert 2 = c ∧ p.walk.getVert 1 = act R g s.neighbor := by
  classical
  constructor
  · rintro ⟨e, hd, hn⟩
    obtain ⟨g, hg⟩ : ∃ g : stabilizer R c, ¬ Z R (act R g a) ≤ Q R e := by
      by_contra! h
      exact hn (iSup_le h)
    obtain ⟨tail, ht⟩ := (cosetGraph_connected R).exists_walk_length_eq_dist c e
    have hl : tail.length + 2 = geometry.b R := by rwa [ht]
    exact ⟨e, g, criticalPathOfConjugate ha s tail hl g hg,
      criticalPathOfConjugate_center ha s tail hl g hg,
      criticalPathOfConjugate_first ha s tail hl g hg⟩
  · rintro ⟨e, g, p, hc, _⟩
    refine ⟨e, ?_, ?_⟩
    · rw [← hc, p.dist_end, p.length_eq_b]
      omega
    · intro h
      exact p.critical.2 ((le_iSup (fun k : stabilizer R c => Z R (act R k a)) g).trans h)

/-- Add the selected centralizer bound to the explicitly constructed path. -/
noncomputable def pathPlacementOfConjugate {a c e : Vertex R}
    (ha : color R a = false) (s : MovingSeed a c)
    (tail : (cosetGraph R).Walk c e) (hlen : tail.length + 2 = geometry.b R)
    (g : stabilizer R c) (hcrit : ¬ Z R (act R g a) ≤ Q R e)
    (hgood : GoodConjugate a c s.neighbor (tail.getVert 1) g) :
    PathPlacement geometry a c s.neighbor where
  start := act R g a
  endpoint := e
  path := criticalPathOfConjugate ha s tail hlen g hcrit
  conjugator := g
  local_conjugator := g.property
  start_image := rfl
  center_eq := criticalPathOfConjugate_center ha s tail hlen g hcrit
  first_image := (criticalPathOfConjugate_first ha s tail hlen g hcrit).symm
  centralizer_selection := by
    rw [criticalPathOfConjugate_third]
    exact hgood

/-- A proved cover by the good conjugates supplies one that still escapes
at the far endpoint. The incident radius term is killed by minimality. -/
theorem pathPlacement_of_spanEscape_and_cover {a c : Vertex R}
    (ha : color R a = false) (hc : color R c = false)
    (hb : 4 < geometry.b R) (s : MovingSeed a c)
    (escape : SpanEscape geometry a c)
    (cover : ∀ u : Vertex R, Adjacent R c u →
      localZSpan R a c ≤ goodConjugateSpan a c s.neighbor u ⊔ V R u) :
    Nonempty (PathPlacement geometry a c s.neighbor) := by
  classical
  obtain ⟨e, hdist, hout⟩ := escape
  obtain ⟨tail, htail⟩ := (cosetGraph_connected R).exists_walk_length_eq_dist c e
  have hlen : tail.length + 2 = geometry.b R := by rwa [htail]
  have hcu : Adjacent R c (tail.getVert 1) := by
    simpa only [SimpleGraph.Walk.getVert_zero, Nat.zero_add] using
      (cosetGraph_adj R _ _).mp (tail.adj_getVert_succ (i := 0) (by omega))
  have hremaining : (cosetGraph R).dist (tail.getVert 1) e = tail.length - 1 := by
    have h := SimpleGraph.length_eq_dist_of_subwalk htail (tail.isSubwalk_drop 1)
    simpa only [SimpleGraph.Walk.drop_length] using h.symm
  have hV : V R (tail.getVert 1) ≤ Q R e :=
    incident_radius_le_kernel hc hcu (by rw [hremaining]; omega)
  obtain ⟨g, hgood, hcrit⟩ : ∃ g : stabilizer R c,
      GoodConjugate a c s.neighbor (tail.getVert 1) g ∧
      ¬ Z R (act R g a) ≤ Q R e := by
    by_contra! h
    apply hout
    apply (cover _ hcu).trans
    refine sup_le ?_ hV
    exact iSup_le fun g => iSup_le fun hg => h g hg
  exact ⟨pathPlacementOfConjugate ha s tail hlen g hcrit hgood⟩

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.LocalCommutator.NaturalCase.Opposite.Selection
