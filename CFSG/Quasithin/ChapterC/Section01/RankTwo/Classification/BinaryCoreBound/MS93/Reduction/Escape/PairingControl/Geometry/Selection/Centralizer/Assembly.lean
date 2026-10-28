module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.Geometry.Selection.Centralizer.Endpoint
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.Geometry.Selection.Centralizer.Source

/-!
# Constructing the centralizer-selected critical path

The reverse critical pair puts the old endpoint's Z-layer outside Q_alpha.
The local neighbor-generation identity therefore supplies a good neighbor s
of c and then an M-neighbor d of s whose Z-layer is outside Q_alpha.
Minimality of b and the triangle inequalities make (alpha,d) critical, with
the same second predecessor c and the same trapped containment. They also
place the original third predecessor and the new last predecessor on the
new geodesic. Endpoint movement and step (3) identify the new R₀ with the
selected displacement, giving the required relative centralizer equality.

The local neighbor-generation theorem remains an explicit input here.
This is the geometric deduction of (4), not its source-only assembly.

Source: Meierfrankenfeld--Stellmacher (1993), (4.3.2)(4), printed p.884.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl.Geometry.Selection.Centralizer
variable {M : Type*} [Group M] {L R : Subgroup M} {geometry : MS93.Geometry R}

/-- Every neighboring H-ball is contained in the M-ball at its incident vertex. -/
theorem neighbor_V_le {c s : Vertex R} (hc : color R c = false)
    (hcs : Adjacent R c s) : V R s ≤ V R c := by
  apply V_le_of_h_neighbors hc hcs
  intro d hds
  have hdc : (cosetGraph R).dist d c ≤ 2 := by
    have htri := (cosetGraph_connected R).dist_triangle (u := d) (v := s) (w := c)
    rw [SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj R _ _).mpr hds),
      SimpleGraph.dist_eq_one_iff_adj.mpr
        ((cosetGraph_adj R _ _).mpr (adjacent_symm R hcs))] at htri
    exact htri
  exact le_iSup_of_le d (le_iSup_of_le hdc le_rfl)

theorem centralizingNeighborSpan_le {c t : Vertex R} (hc : color R c = false) :
    centralizingNeighborSpan c t ≤ V R c := by
  apply iSup_le
  intro s
  apply iSup_le
  intro hcs
  apply iSup_le
  intro _
  exact neighbor_V_le hc hcs

/-- The explicit contract is precisely the printed equality, rather than
an assertion that the eventual centralizer choice already exists. -/
theorem neighborGeneration_iff : NeighborGeneration R ↔
    ∀ c t : Vertex R, color R c = false → Adjacent R c t →
      V R c = centralizingNeighborSpan c t := by
  constructor
  · intro h c t hc hct
    exact le_antisymm (h c t hc hct) (centralizingNeighborSpan_le hc)
  · intro h c t hc hct
    exact (h c t hc hct).le

variable [Finite M]

/-- Extract a new critical endpoint from the source's local neighbor span.
The start and the trapped second predecessor are preserved explicitly. -/
theorem exists_centralizerChoice_of_span
    (source : LocalSource L R) (hb : 2 < geometry.b R)
    (initial : ∀ q : Counterexample geometry, Nonempty (InitialFacts q))
    (facts : ContraryLocalFacts geometry) (p : Counterexample geometry)
    {t : Vertex R} (ht : Before p.a p.a' t 3)
    (generation : V R p.c ≤ centralizingNeighborSpan p.c t) :
    ∃ q : Counterexample geometry, q.a = p.a ∧ q.c = p.c ∧
      Nonempty (CentralizerChoice q) := by
  classical
  have htc : Adjacent R t p.c := ht.adjacent (geometry := geometry) p.before
  have hV : ¬ V R p.c ≤ Q R p.a := by
    intro h
    apply (source.critical_reverse geometry p.a p.color_a p.a' p.end_color p.critical).2
    apply le_trans _ h
    exact le_iSup_of_le p.a' (le_iSup_of_le
      (show (cosetGraph R).dist p.a' p.c ≤ 2 by
        rw [SimpleGraph.dist_comm, p.before.1]) le_rfl)
  obtain ⟨s, hcs, hcentral, hsQ⟩ : ∃ s, Adjacent R p.c s ∧
      Q R t ⊓ centralizer (edgeDisplacement p.c s : Set (FreeAmalgam R)) = Q R p.c ∧
      ¬ V R s ≤ Q R p.a := by
    by_contra! hn
    apply hV
    apply generation.trans
    apply iSup_le
    intro s
    apply iSup_le
    intro hcs
    apply iSup_le
    intro hc
    exact hn s hcs hc
  obtain ⟨d, hds, hdQ⟩ : ∃ d, Adjacent R d s ∧ ¬ Z R d ≤ Q R p.a := by
    by_contra! hn
    exact hsQ (V_le_of_h_neighbors p.before_color hcs (Q R p.a) hn)
  have hds_dist : (cosetGraph R).dist d s = 1 :=
    SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj R _ _).mpr hds)
  have hcs_dist : (cosetGraph R).dist p.c s = 1 :=
    SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj R _ _).mpr hcs)
  have hdc : (cosetGraph R).dist d p.c ≤ 2 := by
    have htri := (cosetGraph_connected R).dist_triangle (u := d) (v := s) (w := p.c)
    rw [hds_dist, SimpleGraph.dist_comm (u := s), hcs_dist] at htri
    exact htri
  have hdcolor : color R d = false := by
    have hcol₁ := adjacent_color_ne R hcs
    have hcol₂ := adjacent_color_ne R hds
    cases h : color R d <;> cases h' : color R s <;> simp_all [p.before_color]
  have hda_lower : geometry.b R ≤ (cosetGraph R).dist d p.a := by
    by_contra! h
    apply hdQ
    apply Z_le_Q_of_dist_lt R d (geometry.exists_critical d hdcolor)
    rwa [geometry.distance_constant d hdcolor]
  have hda : (cosetGraph R).dist d p.a = geometry.b R := by
    have htri := (cosetGraph_connected R).dist_triangle (u := d) (v := p.c) (w := p.a)
    have hpath := p.before.2
    rw [p.distance_eq_b, SimpleGraph.dist_comm (u := p.a)] at hpath
    omega
  have had : (cosetGraph R).dist p.a d = geometry.b R := by
    rwa [SimpleGraph.dist_comm]
  have hdcrit : CriticalPair R d p.a (geometry.exists_critical d hdcolor) :=
    ⟨hda.trans (geometry.distance_constant d hdcolor).symm, hdQ⟩
  have hcrit := source.critical_reverse geometry d hdcolor p.a p.color_a hdcrit
  have hcd : (cosetGraph R).dist p.c d = 2 := by
    have htri := (cosetGraph_connected R).dist_triangle (u := p.a) (v := p.c) (w := d)
    have hpath := p.before.2
    rw [p.distance_eq_b] at hpath
    rw [had] at htri
    rw [SimpleGraph.dist_comm] at hdc
    omega
  let q : Counterexample geometry :=
    { a := p.a
      a' := d
      c := p.c
      color_a := p.color_a
      critical := hcrit
      before := ⟨hcd, p.before.2.trans (p.distance_eq_b.trans had.symm)⟩
      trapped := p.trapped }
  have hs : Before q.a q.a' s 1 := by
    refine ⟨?_, ?_⟩
    · change (cosetGraph R).dist s d = 1
      rwa [SimpleGraph.dist_comm]
    · change (cosetGraph R).dist p.a s + 1 = (cosetGraph R).dist p.a d
      have htri₁ := (cosetGraph_connected R).dist_triangle (u := p.a) (v := p.c) (w := s)
      have htri₂ := (cosetGraph_connected R).dist_triangle (u := p.a) (v := s) (w := d)
      have hpath := p.before.2
      rw [p.distance_eq_b] at hpath
      rw [hcs_dist] at htri₁
      rw [had, SimpleGraph.dist_comm (u := s), hds_dist] at htri₂
      omega
  have htq : Before q.a q.a' t 3 := by
    have htc_dist : (cosetGraph R).dist t p.c = 1 :=
      SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj R _ _).mpr htc)
    have htri₁ := (cosetGraph_connected R).dist_triangle (u := t) (v := p.c) (w := d)
    have htri₂ := (cosetGraph_connected R).dist_triangle (u := p.a) (v := t) (w := d)
    have hpath := ht.2
    rw [p.distance_eq_b] at hpath
    rw [htc_dist, hcd] at htri₁
    rw [had] at htri₂
    change (cosetGraph R).dist t d = 3 ∧
      (cosetGraph R).dist p.a t + 3 = (cosetGraph R).dist p.a d
    constructor <;> omega
  obtain ⟨hq⟩ := initial q
  refine ⟨q, rfl, rfl, ⟨⟨t, htq, ?_⟩⟩⟩
  rw [radius_eq_edge source hb q hq facts hs]
  exact hcentral

/-- A universal local generation theorem supplies the single instance used
in the selected critical configuration. No bound b > 6 is required. -/
theorem exists_centralizerChoice_of_neighborGeneration
    (source : LocalSource L R) (hb : 2 < geometry.b R)
    (initial : ∀ q : Counterexample geometry, Nonempty (InitialFacts q))
    (facts : ContraryLocalFacts geometry) (p : Counterexample geometry)
    (generation : NeighborGeneration R) :
    ∃ q : Counterexample geometry, q.a = p.a ∧ q.c = p.c ∧
      Nonempty (CentralizerChoice q) := by
  obtain ⟨t, ht⟩ := p.exists_before (show 3 ≤ geometry.b R by omega)
  exact exists_centralizerChoice_of_span source hb initial facts p ht
    (generation p.c t p.before_color
      (adjacent_symm R (ht.adjacent (geometry := geometry) p.before)))

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl.Geometry.Selection.Centralizer
