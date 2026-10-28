module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Setup.Critical
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Setup.CommonFacts

/-!
# Critical paths and two-edge replacement for MS93

A critical path retains the actual graph walk, its shortest length and its
noncontainment in the terminal neighborhood kernel. Minimality controls every
shorter subwalk. Reversal uses the common critical-pair reversal theorem;
conjugation uses the original right action and its inverse-conjugation formula.

At an M-vertex, the odd-colored vertices in the radius-two ball add no extra
Z-generators. Thus the shared escape theorem selects an M-vertex at distance
exactly two. Prepending its two-edge walk to the old path with its last two
edges removed gives another shortest critical path. The overlap equation
retains every vertex of the common subwalk. The prescribed-conjugator version
also constructs the walk, with its essential noncontainment left explicit.

These are path tools for MS93 (4.4), printed pp.890--895. They do not establish
(4.4.1), the regular-path choice (4.4.2), or the noncontainment in (4.4.4).
In particular they assert neither b = 8 nor local centrality.
-/

@[expose] public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
variable {M : Type*} [Group M] (R : Subgroup M)

/-- Act directly on a walk, with its actual action vertices in the public type.
This avoids any reliance on the hidden body of Setup's graph-homomorphism helper. -/
def actWalk (g : FreeAmalgam R) {a a' : Vertex R} :
    (cosetGraph R).Walk a a' → (cosetGraph R).Walk
      (Stellmacher.PushingUp.AmalgamGraph.act R g a)
      (Stellmacher.PushingUp.AmalgamGraph.act R g a')
  | .nil => .nil
  | .cons h p => .cons ((cosetGraph_adj R _ _).mpr
      ((adjacent_act_iff R g _ _).mpr ((cosetGraph_adj R _ _).mp h))) (actWalk g p)

theorem actWalk_length (g : FreeAmalgam R) {a a' : Vertex R}
    (p : (cosetGraph R).Walk a a') : (actWalk R g p).length = p.length := by
  induction p with
  | nil => rfl
  | cons h p ih => exact congrArg (fun n => n + 1) ih

theorem actWalk_getVert (g : FreeAmalgam R) {a a' : Vertex R}
    (p : (cosetGraph R).Walk a a') (i : ℕ) :
    (actWalk R g p).getVert i =
      Stellmacher.PushingUp.AmalgamGraph.act R g (p.getVert i) := by
  induction p generalizing i with
  | nil => rfl
  | cons h p ih =>
    cases i with
    | zero => rfl
    | succ i => exact ih i

/-- A shortest walk with its genuine critical-pair noncontainment. -/
structure CriticalPath (geometry : Geometry R) (a a' : Vertex R) where
  start_color : color R a = false
  walk : (cosetGraph R).Walk a a'
  shortest : walk.length = (cosetGraph R).dist a a'
  critical : CriticalPair R a a' (geometry.exists_critical a start_color)

namespace CriticalPath
variable {R} {geometry : Geometry R} {a a' : Vertex R}

theorem length_eq_b (p : CriticalPath R geometry a a') : p.walk.length = geometry.b R :=
  p.shortest.trans (p.critical.1.trans (geometry.distance_constant a p.start_color))

theorem isPath (p : CriticalPath R geometry a a') : p.walk.IsPath :=
  p.walk.isPath_of_length_eq_dist p.shortest

theorem end_color (p : CriticalPath R geometry a a') : color R a' = false := by
  have he : Even p.walk.length := by
    rw [p.shortest, p.critical.1]
    exact geometry.even a p.start_color
  exact ((walk_even_iff_color_eq R p.walk).mp he).symm.trans p.start_color

noncomputable def ofPair (ha : color R a = false)
    (hc : CriticalPair R a a' (geometry.exists_critical a ha)) :
    CriticalPath R geometry a a' := by
  classical
  let p := (cosetGraph_connected R).exists_walk_length_eq_dist a a'
  exact ⟨ha, p.choose, p.choose_spec, hc⟩

theorem exists_from (ha : color R a = false) :
    ∃ a', Nonempty (CriticalPath R geometry a a') := by
  obtain ⟨a', hc⟩ := criticalPair_exists R a (geometry.exists_critical a ha)
  exact ⟨a', ⟨ofPair ha hc⟩⟩

theorem dist_start (p : CriticalPath R geometry a a') {i : ℕ}
    (hi : i ≤ p.walk.length) : (cosetGraph R).dist a (p.walk.getVert i) = i := by
  have hh := SimpleGraph.length_eq_dist_of_subwalk p.shortest (p.walk.isSubwalk_take i)
  simpa only [SimpleGraph.Walk.take_length, inf_eq_left.mpr hi] using hh.symm

theorem dist_end (p : CriticalPath R geometry a a') (i : ℕ) :
    (cosetGraph R).dist (p.walk.getVert i) a' = p.walk.length - i := by
  have hh := SimpleGraph.length_eq_dist_of_subwalk p.shortest (p.walk.isSubwalk_drop i)
  simpa only [SimpleGraph.Walk.drop_length] using hh.symm

theorem vertex_color (p : CriticalPath R geometry a a') {i : ℕ}
    (hi : i ≤ p.walk.length) : color R (p.walk.getVert i) = false ↔ Even i := by
  have hh := walk_even_iff_color_eq R (p.walk.take i)
  simpa only [SimpleGraph.Walk.take_length, inf_eq_left.mpr hi, p.start_color, eq_comm]
    using hh.symm

def reverse {L : Subgroup M} {source : LocalSource L R}
    (common : CommonFacts R source geometry) (p : CriticalPath R geometry a a') :
    CriticalPath R geometry a' a where
  start_color := p.end_color
  walk := p.walk.reverse
  shortest := by rw [SimpleGraph.Walk.length_reverse, p.shortest, SimpleGraph.dist_comm]
  critical := common.critical_reverse a p.start_color a' p.end_color p.critical

def act (g : FreeAmalgam R) (p : CriticalPath R geometry a a') :
    CriticalPath R geometry
      (Stellmacher.PushingUp.AmalgamGraph.act R g a)
      (Stellmacher.PushingUp.AmalgamGraph.act R g a') where
  start_color := (action_preserves_color R g a).trans p.start_color
  walk := actWalk R g p.walk
  shortest := (actWalk_length R g p.walk).trans
    (p.shortest.trans (dist_act R g a a').symm)
  critical := by
    constructor
    · rw [dist_act, p.critical.1]
      exact (criticalDistance_act R g a _ _).symm
    · rw [Z_act, Q_act]
      exact fun h => p.critical.2
        ((map_le_map_iff_of_injective (MulAut.conj g⁻¹).injective).mp h)
end CriticalPath

-- Odd-colored vertices within radius two add no extra Z-generators.
theorem adjacent_Z_le {a t : Vertex R} (ha : color R a = false)
    (hat : Adjacent R a t) : Z R t ≤ Z R a := by
  have ht : color R t ≠ false := by
    intro ht
    exact adjacent_color_ne R hat (ha.trans ht.symm)
  rw [Z, if_neg ht, Z, if_pos ha]
  exact le_iSup_of_le t (le_iSup_of_le hat le_rfl)

theorem V_le_iff {a : Vertex R} (ha : color R a = false)
    (K : Subgroup (FreeAmalgam R)) :
    V R a ≤ K ↔ ∀ d, color R d = false → (cosetGraph R).dist d a ≤ 2 → Z R d ≤ K := by
  constructor
  · intro h d _ hd
    have hz : Z R d ≤ V R a := le_iSup_of_le d (le_iSup_of_le hd le_rfl)
    exact hz.trans h
  · intro h
    apply iSup_le
    intro d
    apply iSup_le
    intro hd
    by_cases hc : color R d = false
    · exact h d hc hd
    · obtain ⟨p, hp⟩ := (cosetGraph_connected R).exists_walk_length_eq_dist d a
      have hn : ¬ Even ((cosetGraph R).dist d a) := by
        rw [← hp, walk_even_iff_color_eq, ha]
        exact hc
      rw [Nat.even_iff] at hn
      have hd' : (cosetGraph R).dist d a = 1 := by omega
      have hadj : Adjacent R a d := adjacent_symm R
        ((cosetGraph_adj R _ _).mp (SimpleGraph.dist_eq_one_iff_adj.mp hd'))
      exact (adjacent_Z_le R ha hadj).trans (h a ha (by simp))

variable {geometry : Geometry R}

theorem exists_critical_shift {a c : Vertex R} (ha : color R a = false)
    (hd : (cosetGraph R).dist a c + 2 = geometry.b R)
    (he : ¬ V R a ≤ Q R c) :
    ∃ d, ∃ hdc : color R d = false, (cosetGraph R).dist d a = 2 ∧
      CriticalPair R d c (geometry.exists_critical d hdc) := by
  classical
  obtain ⟨d, hdc, hda, hn⟩ : ∃ d, color R d = false ∧
      (cosetGraph R).dist d a ≤ 2 ∧ ¬ Z R d ≤ Q R c := by
    simpa only [V_le_iff R ha, not_forall, exists_prop] using he
  have hmin := criticalDistance_le R d (geometry.exists_critical d hdc) hn
  rw [geometry.distance_constant d hdc] at hmin
  change geometry.b R ≤ _ at hmin
  have htri : (cosetGraph R).dist d c ≤
      (cosetGraph R).dist d a + (cosetGraph R).dist a c :=
    (cosetGraph_connected R).dist_triangle
  refine ⟨d, hdc, by omega, ?_, hn⟩
  rw [geometry.distance_constant d hdc]
  change _ = geometry.b R
  omega


theorem V_le_Q_of_dist_add_two_lt {a c : Vertex R} (ha : color R a = false)
    (hd : (cosetGraph R).dist a c + 2 < geometry.b R) : V R a ≤ Q R c := by
  apply (V_le_iff R ha _).mpr
  intro d hdc hda
  apply Z_le_Q_of_dist_lt R d (geometry.exists_critical d hdc)
  rw [geometry.distance_constant d hdc]
  change (cosetGraph R).dist d c < geometry.b R
  have htri : (cosetGraph R).dist d c ≤
      (cosetGraph R).dist d a + (cosetGraph R).dist a c :=
    (cosetGraph_connected R).dist_triangle
  omega

theorem V_le_Q {a : Vertex R} (ha : color R a = false)
    (hb : 2 < geometry.b R) : V R a ≤ Q R a :=
  V_le_Q_of_dist_add_two_lt R ha (by simpa using hb)

namespace CriticalPath
variable {R} {geometry : Geometry R} {a a' : Vertex R}

def prepend_two (p : CriticalPath R geometry a a')
    (hb : 2 ≤ geometry.b R) {d : Vertex R} (hdc : color R d = false)
    (q : (cosetGraph R).Walk d a) (hq : q.length = 2)
    (hn : ¬ Z R d ≤ Q R (p.walk.getVert (p.walk.length - 2))) :
    CriticalPath R geometry d (p.walk.getVert (p.walk.length - 2)) := by
  let w := q.append (p.walk.take (p.walk.length - 2))
  have hw : w.length = geometry.b R := by
    simp only [w, SimpleGraph.Walk.length_append, SimpleGraph.Walk.take_length,
      inf_eq_left.mpr (Nat.sub_le _ _), hq]
    have hl := p.length_eq_b
    omega
  have hmin := criticalDistance_le R d (geometry.exists_critical d hdc) hn
  rw [geometry.distance_constant d hdc] at hmin
  change geometry.b R ≤ _ at hmin
  have hmax := SimpleGraph.dist_le w
  have hdist : (cosetGraph R).dist d (p.walk.getVert (p.walk.length - 2)) =
      geometry.b R := by omega
  exact ⟨hdc, w, hw.trans hdist.symm,
    ⟨hdist.trans (geometry.distance_constant d hdc).symm, hn⟩⟩

theorem prepend_two_walk (p : CriticalPath R geometry a a')
    (hb : 2 ≤ geometry.b R) {d : Vertex R} (hdc : color R d = false)
    (q : (cosetGraph R).Walk d a) (hq : q.length = 2)
    (hn : ¬ Z R d ≤ Q R (p.walk.getVert (p.walk.length - 2))) :
    (p.prepend_two hb hdc q hq hn).walk =
      q.append (p.walk.take (p.walk.length - 2)) := rfl

theorem prepend_two_overlap (p : CriticalPath R geometry a a')
    (hb : 2 ≤ geometry.b R) {d : Vertex R} (hdc : color R d = false)
    (q : (cosetGraph R).Walk d a) (hq : q.length = 2)
    (hn : ¬ Z R d ≤ Q R (p.walk.getVert (p.walk.length - 2)))
    {i : ℕ} (hi : i ≤ p.walk.length - 2) :
    (p.prepend_two hb hdc q hq hn).walk.getVert (i + 2) = p.walk.getVert i := by
  rw [prepend_two_walk, SimpleGraph.Walk.getVert_append, hq, if_neg (by omega),
    Nat.add_sub_cancel, SimpleGraph.Walk.take_getVert, inf_eq_right.mpr hi]

theorem exists_shift {L : Subgroup M} {source : LocalSource L R}
    (common : CommonFacts R source geometry) (p : CriticalPath R geometry a a') :
    ∃ d, ∃ q : (cosetGraph R).Walk d a, ∃ shifted :
      CriticalPath R geometry d (p.walk.getVert (p.walk.length - 2)),
      q.length = 2 ∧ shifted.walk = q.append (p.walk.take (p.walk.length - 2)) := by
  have hb := common.large_distance
  have hl := p.length_eq_b
  have hc : (cosetGraph R).dist (p.walk.getVert (p.walk.length - 2)) a' = 2 := by
    rw [p.dist_end]
    omega
  have hstart : (cosetGraph R).dist a (p.walk.getVert (p.walk.length - 2)) + 2 =
      (cosetGraph R).dist a a' := by
    rw [p.dist_start (Nat.sub_le _ _), ← p.shortest]
    omega
  have he := common.escape a p.start_color a' p.critical _ hc hstart
  have hd : (cosetGraph R).dist a (p.walk.getVert (p.walk.length - 2)) + 2 =
      geometry.b R := hstart.trans (p.shortest.symm.trans hl)
  obtain ⟨d, hdc, hda, hn⟩ := exists_critical_shift R p.start_color hd he
  obtain ⟨q, hq⟩ := (cosetGraph_connected R).exists_walk_length_eq_dist d a
  exact ⟨d, q, p.prepend_two (by omega) hdc q (hq.trans hda) hn.2,
    hq.trans hda, rfl⟩

end CriticalPath

namespace CriticalPath
variable {R} {geometry : Geometry R} {a a' : Vertex R}

theorem endpoint_Z_le_start_stabilizer (p : CriticalPath R geometry a a')
    (hb : 0 < geometry.b R) : Z R a' ≤ stabilizer R a := by
  have hlen := p.length_eq_b
  have hn : ¬ p.walk.Nil := by
    intro hn
    have hz := hn.length_eq_zero
    omega
  have hZQ : Z R a' ≤ Q R (p.walk.getVert 1) := by
    apply Z_le_Q_of_dist_lt R a' (geometry.exists_critical a' p.end_color)
    rw [SimpleGraph.dist_comm, p.dist_end, geometry.distance_constant a' p.end_color]
    change p.walk.length - 1 < geometry.b R
    omega
  have hadj : Adjacent R (p.walk.getVert 1) a :=
    adjacent_symm R ((cosetGraph_adj R _ _).mp (p.walk.adj_snd hn))
  exact fun _ hz => (hZQ hz).2 a hadj

-- The caller provides the substantive noncontainment from (4.4.4).
-- This constructs the actual replacement path from its conjugating element.
def conjugateShift (p : CriticalPath R geometry a a') (hb : 2 ≤ geometry.b R)
    (g : FreeAmalgam R) (hg : g ∈ stabilizer R a)
    (hn : ¬ (Z R (p.walk.getVert 2)).map (MulAut.conj g⁻¹).toMonoidHom ≤
      Q R (p.walk.getVert (p.walk.length - 2))) :
    CriticalPath R geometry
      (Stellmacher.PushingUp.AmalgamGraph.act R g (p.walk.getVert 2))
      (p.walk.getVert (p.walk.length - 2)) := by
  have htwo : 2 ≤ p.walk.length := by rw [p.length_eq_b]; exact hb
  have hc := (p.vertex_color htwo).mpr (show Even 2 by decide)
  have hgfix : Stellmacher.PushingUp.AmalgamGraph.act R g a = a := hg
  let q : (cosetGraph R).Walk
      (Stellmacher.PushingUp.AmalgamGraph.act R g (p.walk.getVert 2)) a :=
    (actWalk R g (p.walk.take 2).reverse).copy rfl hgfix
  have hq : q.length = 2 :=
    (SimpleGraph.Walk.length_copy _ _ _).trans
      ((actWalk_length R g _).trans
        ((SimpleGraph.Walk.length_reverse _).trans
          ((SimpleGraph.Walk.take_length _ _).trans (inf_eq_left.mpr htwo))))
  apply p.prepend_two hb ((action_preserves_color R g _).trans hc) q hq
  rwa [Z_act]

end CriticalPath

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
