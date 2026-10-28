module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Early.Orbit.Source.HatIdentity.Preliminary.Algebra

/-!
# Transport and the remaining source-path rechoice for the first D containment

The relative normalizer preserves the preceding Z-layer and the incident
edge Z-layer, even though it may move their vertices. This retains the
preceding critical window, the turn at the splice and the required edge
inequality, in both orientations of the actual source path.

A full rechosen path must still be constructed. RechosenWindow records
that geometric output, including every SourcePath clause, while allowing
any of the indices where (4.5.1)(iii) is already proved. RechoicesOnPath
requests it only for an escaping right conjugate under the printed contrary
assumption and the supplied seed estimates. The conditional application
transports the fixed seed to that actual vertex and applies (4.5.1)(iii).
It does not infer control of conjugates from containment of the original seed.

Source: Meierfrankenfeld--Stellmacher (1993), (4.5.3)(i), claim (1), p.897;
path and turn conventions on pp.895--896.
-/

@[expose] public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped Pointwise
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Early.Orbit.Source.HatIdentity.Preliminary.Kernels
open PathCentrality NormalizerTransfer
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}

omit [Finite M] in
/-- Right conjugation transports the full residual-fixed seed to its actual vertex. -/
theorem conjugate_fixedSeed_le (b : Vertex R) (g : FreeAmalgam R) :
    rightConjugate (fixedSeed R b) g ≤ fixedSeed R (act R g b) := by
  change (fixedSeed R b).map (MulAut.conj g⁻¹).toMonoidHom ≤
    V R (act R g b) ⊓ centralizer (Ltilde R (act R g b) : Set (FreeAmalgam R))
  rw [V_act, Ltilde_act]
  apply le_inf (map_mono inf_le_left)
  exact (map_mono (show fixedSeed R b ≤ centralizer (Ltilde R b : Set (FreeAmalgam R)) from
    inf_le_right)).trans (map_centralizer_le_centralizer_image _ _)

/-- A genuine rechoice retains a complete source path, the conjugated seed
vertex and the original target kernel. The path carries all critical windows,
turns and edge inequalities required by (4.5.1)(iii). -/
structure RechosenWindow (R : Subgroup M) (b d : Vertex R) (g : FreeAmalgam R) where
  center : Vertex R
  path : SourcePath R center
  index : ℕ
  even_index : Even index
  lower : 2 ≤ index
  upper : index ≤ 6
  seed_vertex : path.walk.getVert index = act R g b
  kernel_vertex : path.walk.getVert (index + 6) = d

/-- The geometric rechoice needed for claim (1), with the contrary assumption
and the exact seed estimates retained. No existence is asserted by this contract. -/
structure RechoicesOnPath (R : Subgroup M) {a : Vertex R} (p : SourcePath R a) where
  forward : ∀ i : ℕ, Even i → 4 ≤ i → i ≤ 6 →
    hatV R (p.walk.getVert (i - 2)) (p.walk.getVert i) ≠
      Vcirc R (p.walk.getVert (i - 2)) ⊔ Z R (p.walk.getVert (i - 2)) →
    SeedEstimates R (p.walk.getVert i) (p.walk.getVert (i - 2))
      (p.walk.getVert (i - 1)) →
    ∀ g ∈ relativeNormalizer R (p.walk.getVert i) (p.walk.getVert (i - 1)),
      ¬ rightConjugate (fixedSeed R (p.walk.getVert (i - 2))) g ≤
        Q R (p.walk.getVert (i + 4)) →
      Nonempty (RechosenWindow R (p.walk.getVert (i - 2))
        (p.walk.getVert (i + 4)) g)
  backward : ∀ i : ℕ, Even i → 8 ≤ i → i ≤ 10 →
    hatV R (p.walk.getVert (i + 2)) (p.walk.getVert i) ≠
      Vcirc R (p.walk.getVert (i + 2)) ⊔ Z R (p.walk.getVert (i + 2)) →
    SeedEstimates R (p.walk.getVert i) (p.walk.getVert (i + 2))
      (p.walk.getVert (i + 1)) →
    ∀ g ∈ relativeNormalizer R (p.walk.getVert i) (p.walk.getVert (i + 1)),
      ¬ rightConjugate (fixedSeed R (p.walk.getVert (i + 2))) g ≤
        Q R (p.walk.getVert (i - 4)) →
      Nonempty (RechosenWindow R (p.walk.getVert (i + 2))
        (p.walk.getVert (i - 4)) g)

/-- Apply the already proved (4.5.1)(iii) to the genuine rechoice, not to the
original seed. This compares literal right conjugates with the fixed target. -/
theorem conjugate_fixedSeed_le_of_rechosenWindow
    (common : CommonFacts R source geometry) (earlier : Earlier R geometry)
    {b d : Vertex R} {g : FreeAmalgam R} (w : RechosenWindow R b d g) :
    rightConjugate (fixedSeed R b) g ≤ Q R d := by
  have h := (firstFactsOnPath source common earlier w.path).forward w.index
    w.even_index w.lower w.upper
  have hseed := fixedSeed_le_B common
    (w.path.even_color w.even_index (by have := w.upper; omega))
  have hle := hseed.trans h.B_le
  rw [w.seed_vertex, w.kernel_vertex] at hle
  exact (conjugate_fixedSeed_le b g).trans hle

/-- Claim (1), once the escaping conjugate has been placed on a valid source
window. No distant-kernel normalization is assumed. -/
theorem span_le_four_of_rechoices
    (common : CommonFacts R source geometry) (earlier : Earlier R geometry)
    {a b t d : Vertex R}
    (rechoose : ∀ g ∈ relativeNormalizer R a t,
      ¬ rightConjugate (fixedSeed R b) g ≤ Q R d → Nonempty (RechosenWindow R b d g)) :
    normalizerSpan R a b t ≤ Q R d := by
  apply iSup_le
  intro g
  by_contra hn
  obtain ⟨w⟩ := rechoose g g.property hn
  exact hn (conjugate_fixedSeed_le_of_rechosenWindow common earlier w)

/-- The relative normalizer preserves the odd edge's Z-layer, even when it
moves the odd vertex itself. -/
theorem relativeNormalizer_preserves_edge_Z
    (common : CommonFacts R source geometry)
    {a t : Vertex R} (ha : color R a = false) (hat : Adjacent R a t)
    {g : FreeAmalgam R} (hg : g ∈ relativeNormalizer R a t) :
    Z R (act R g t) = Z R t := by
  have hga : act R g a = a := hg.1
  have hat' : Adjacent R a (act R g t) := by
    simpa only [hga] using (adjacent_act_iff R g a t).mpr hat
  have hQ : (Q R t).map (MulAut.conj g⁻¹).toMonoidHom = Q R t :=
    mem_normalizer_iff_map_conj_eq.mp ((normalizer _).inv_mem hg.2)
  rw [Escape.EdgeTransfer.edge_Z_eq_fixed common.large_distance
      (LocalCommutator.moduleFacts common) a (act R g t) ha hat', Q_act, hQ,
    ← Escape.EdgeTransfer.edge_Z_eq_fixed common.large_distance
      (LocalCommutator.moduleFacts common) a t ha hat]

/-- The unchanged preceding Z-layer retains critical noncontainment against
the unchanged far endpoint. Distance through the fixed center is exactly eight. -/
theorem conjugated_preceding_critical
    (common : CommonFacts R source geometry) (earlier : Earlier R geometry)
    {a b t e : Vertex R} (ha : color R a = false) (hb : color R b = false)
    (hat : Adjacent R a t) (hbt : Adjacent R b t)
    (hmove : b ∈ Escape.movingNeighbors geometry a)
    (hae : (cosetGraph R).dist a e = 6) (hne : ¬ Z R b ≤ Q R e)
    {g : FreeAmalgam R} (hg : g ∈ relativeNormalizer R a t) :
    (cosetGraph R).dist (act R g b) e = 8 ∧ ¬ Z R (act R g b) ≤ Q R e := by
  have hZ : Z R (act R g b) = Z R b := by
    rw [Z_act]
    exact mem_normalizer_iff_map_conj_eq.mp
      (Z_normalized_by_relativeNormalizer_of_moving common earlier hb ha hbt hat hmove
        ((relativeNormalizer R a t).inv_mem hg))
  have hn : ¬ Z R (act R g b) ≤ Q R e := by rwa [hZ]
  have hgb : color R (act R g b) = false := (action_preserves_color R g b).trans hb
  have hmin := criticalDistance_le R _ (geometry.exists_critical _ hgb) hn
  rw [geometry.distance_constant _ hgb] at hmin
  change geometry.b R ≤ _ at hmin
  rw [earlier.distance] at hmin
  have hga : act R g a = a := hg.1
  have hba : (cosetGraph R).dist (act R g b) a = 2 := by
    rw [← hga, dist_act, SimpleGraph.dist_comm]
    exact hmove.1
  have hmax := (cosetGraph_connected R).dist_triangle (u := act R g b) (v := a) (w := e)
  rw [hba, hae] at hmax
  exact ⟨by omega, hn⟩

/-- The preceding critical window and its incident edge Z-layer survive every
relative-normalizer rechoice at either forward source configuration. This is
only the transported window; the complete rechosen path remains to construct. -/
theorem forward_rechoice_geometry
    (common : CommonFacts R source geometry) (earlier : Earlier R geometry)
    {a : Vertex R} (p : SourcePath R a) {i : ℕ} (hi : Even i) (hi4 : 4 ≤ i) (hi6 : i ≤ 6)
    {g : FreeAmalgam R}
    (hg : g ∈ relativeNormalizer R (p.walk.getVert i) (p.walk.getVert (i - 1))) :
    ((cosetGraph R).dist (act R g (p.walk.getVert (i - 2))) (p.walk.getVert (i + 6)) = 8 ∧
      ¬ Z R (act R g (p.walk.getVert (i - 2))) ≤ Q R (p.walk.getVert (i + 6))) ∧
    Z R (act R g (p.walk.getVert (i - 1))) ≠ Z R (p.walk.getVert (i + 1)) ∧
    ∃ k ∈ stabilizer R (p.walk.getVert i),
      act R k (p.walk.getVert (i + 2)) = act R g (p.walk.getVert (i - 2)) := by
  have hib : Even (i - 2) := by rw [Nat.even_iff] at hi ⊢; omega
  have ha := p.even_color hi (by omega)
  have hat : Adjacent R (p.walk.getVert i) (p.walk.getVert (i - 1)) := by
    exact adjacent_symm R (by
      simpa only [Nat.sub_add_cancel (by omega : 1 ≤ i)] using
        p.adjacent (i := i - 1) (by omega))
  constructor
  · apply conjugated_preceding_critical common earlier ha (p.even_color hib (by omega)) hat
      (t := p.walk.getVert (i - 1))
    · simpa only [show i - 2 + 1 = i - 1 by omega] using
        p.adjacent (i := i - 2) (by omega)
    · exact (p.moving_neighbors source common earlier hi (by omega) (by omega)).1
    · rw [p.distance (geometry := geometry) (by omega) (by omega)]; omega
    · simpa only [show i - 2 + 8 = i + 6 by omega] using
        (p.critical (i - 2) hib (by omega)).2
    · exact hg
  · constructor
    · rw [relativeNormalizer_preserves_edge_Z common ha hat hg]
      exact p.edge_Z_ne i hi (by omega) (by omega)
    · obtain ⟨k, hk, ht⟩ := p.turns i hi (by omega) (by omega)
      exact ⟨k * g, (stabilizer R _).mul_mem hk hg.1, by rw [act_mul, ht]⟩

/-- The corresponding transported critical window and edge inequality at the
two reflected source configurations, retaining the original distant endpoint. -/
theorem backward_rechoice_geometry
    (common : CommonFacts R source geometry) (earlier : Earlier R geometry)
    {a : Vertex R} (p : SourcePath R a) {i : ℕ} (hi : Even i) (hi8 : 8 ≤ i) (hi10 : i ≤ 10)
    {g : FreeAmalgam R}
    (hg : g ∈ relativeNormalizer R (p.walk.getVert i) (p.walk.getVert (i + 1))) :
    ((cosetGraph R).dist (act R g (p.walk.getVert (i + 2))) (p.walk.getVert (i - 6)) = 8 ∧
      ¬ Z R (act R g (p.walk.getVert (i + 2))) ≤ Q R (p.walk.getVert (i - 6))) ∧
    Z R (act R g (p.walk.getVert (i + 1))) ≠ Z R (p.walk.getVert (i - 1)) ∧
    ∃ k ∈ stabilizer R (p.walk.getVert i),
      act R k (p.walk.getVert (i - 2)) = act R g (p.walk.getVert (i + 2)) := by
  have hib : Even (i + 2) := hi.add (by decide)
  have hie : Even (i - 6) := by rw [Nat.even_iff] at hi ⊢; omega
  have ha := p.even_color hi (by omega)
  have hat := p.adjacent (i := i) (by omega)
  constructor
  · apply conjugated_preceding_critical common earlier ha (p.even_color hib (by omega)) hat
      (t := p.walk.getVert (i + 1))
    · exact adjacent_symm R (by
        simpa only [Nat.add_assoc] using p.adjacent (i := i + 1) (by omega))
    · exact (p.moving_neighbors source common earlier hi (by omega) (by omega)).2
    · rw [SimpleGraph.dist_comm, p.distance (geometry := geometry) (by omega) (by omega)]; omega
    · have hcrit := p.critical_pair earlier hie (by omega)
      rw [show i - 6 + 8 = i + 2 by omega] at hcrit
      exact (common.critical_reverse _ (p.even_color hie (by omega)) _
        (p.even_color hib (by omega)) hcrit).2
    · exact hg
  · constructor
    · rw [relativeNormalizer_preserves_edge_Z common ha hat hg]
      exact (p.edge_Z_ne i hi (by omega) (by omega)).symm
    · obtain ⟨k, hk, ht⟩ := p.turns i hi (by omega) (by omega)
      refine ⟨k⁻¹ * g, (stabilizer R _).mul_mem ((stabilizer R _).inv_mem hk) hg.1, ?_⟩
      rw [act_mul, ← ht, ← act_mul R k k⁻¹, mul_inv_cancel, act_one]

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Early.Orbit.Source.HatIdentity.Preliminary.Kernels
