module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Early.Orbit.Source.HatIdentity.Preliminary.Decomposition.HatSplit
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Early.Orbit.Source.HatIdentity.Third.NaturalPropagation

/-!
# Actual preliminary estimates for the smaller hat-fixed seed

The proved hat decomposition uses its own residual-fixed subgroup. This seed
is contained in the old full-radius fixed subgroup, so the checked rechoice
gives the first kernel bound. Its intrinsic containment in the hat gives
the small commutator; the disjoint moving planes then give the second kernel
bound. Both forward and reflected estimates are derived on the original
SourcePath from CommonFacts and Earlier, without a splitting premise.

Source: Meierfrankenfeld--Stellmacher (1993), (4.5.3)(i), claims (1)--(2),
printed p.897. The old full-radius interfaces remain unchanged.
-/

@[expose] public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped Pointwise
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Early.Orbit.Source.HatIdentity.SmallSeed
open PathCentrality NormalizerTransfer Preliminary
open Preliminary.Decomposition Preliminary.Kernels
variable {M : Type*} [Group M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}

noncomputable def seed (R : Subgroup M) (b a : Vertex R) : Subgroup (FreeAmalgam R) :=
  hatV R b a ⊓ centralizer (Ltilde R b : Set (FreeAmalgam R))
noncomputable def span (R : Subgroup M) (a b t : Vertex R) : Subgroup (FreeAmalgam R) :=
  conjugatesIn (seed R b a) (relativeNormalizer R a t)

theorem seed_le_fixedSeed {a b : Vertex R} (hba : (cosetGraph R).dist b a = 2) :
    seed R b a ≤ fixedSeed R b :=
  inf_le_inf_right _ (hatV_le_radius R (by rw [SimpleGraph.dist_comm,hba]))

theorem span_le_full {a b t : Vertex R} (hba : (cosetGraph R).dist b a = 2) :
    span R a b t ≤ normalizerSpan R a b t := by
  apply iSup_le
  intro g
  exact (map_mono (seed_le_fixedSeed hba)).trans
    (le_iSup (fun k : relativeNormalizer R a t => rightConjugate (fixedSeed R b) k) g)

theorem H_le_seed [Finite M] (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) {a b : Vertex R} (hb : color R b = false)
    (hba : (cosetGraph R).dist b a = 2) : H R b ≤ seed R b a :=
  le_inf ((H_le_Z_of_central common hb (earlier.centrality b hb)).trans (Z_le_hatV hb hba))
    ((Third.H_le_fixedSeed common earlier hb).trans inf_le_right)

theorem seed_le_span (a b t : Vertex R) : seed R b a ≤ span R a b t :=
  Escape.Initial.Natural.conjugatesIn_contains _ _

private theorem H_normalized (a : Vertex R) :
    stabilizer R a ≤ normalizer (H R a : Set (FreeAmalgam R)) := by
  intro g hg
  rw [mem_normalizer_iff_map_conj_eq]
  change (⁅Vcirc R a, Q R a⁆ : Subgroup (FreeAmalgam R)).map _ = _
  rw [map_commutator, mem_normalizer_iff_map_conj_eq.mp (Vcirc_normalized a hg),
    mem_normalizer_iff_map_conj_eq.mp (Q_normalized R a hg)]
  rfl

private theorem conjugatesIn_le {G : Type*} [Group G] {A P K : Subgroup G}
    (hA : A ≤ K) (hn : P ≤ normalizer K) : conjugatesIn A P ≤ K := by
  apply iSup_le
  intro g
  exact (map_mono hA).trans
    (mem_normalizer_iff_map_conj_eq.mp (hn (P.inv_mem g.property))).le

/-- The smaller seed has the source displacement without any decomposition premise. -/
theorem seed_commutator [Finite M]
    (common : CommonFacts R source geometry) (earlier : Earlier R geometry)
    {a b t : Vertex R} (w : Window geometry a b t) :
    ⁅seed R b a, stabilizer R b⁆ ≤ H R b := by
  have hQ : ⁅seed R b a, Q R b⁆ ≤ H R b :=
    (commutator_mono inf_le_left le_rfl).trans
      (hatV_commutator_le_H common earlier w.color_a w.color_b w.adjacent_a w.adjacent_b w.moving)
  have hL : ⁅Ltilde R b, seed R b a⁆ = ⊥ := by
    rw [commutator_comm]
    exact commutator_eq_bot_iff_le_centralizer.mpr inf_le_right
  have hpre : stabilizer R b ≤
      commutatorPreimage (stabilizer R b) (seed R b a) (H R b) := by
    conv_lhs => rw [← source.local_generation b w.color_b]
    exact sup_le
      (le_commutatorPreimage (Ltilde_le_stabilizer b) (hL.le.trans bot_le))
      (le_commutatorPreimage (fun _ hx => hx.1) (by rwa [commutator_comm]))
  rw [commutator_comm]
  exact (commutator_mono hpre le_rfl).trans
    (commutator_commutatorPreimage_le _ _ _ (H_normalized b))

/-- The smaller span inherits the actual relative-normalizer commutator bound. -/
theorem span_commutator [Finite M]
    (common : CommonFacts R source geometry) (earlier : Earlier R geometry)
    {a b t : Vertex R} (w : Window geometry a b t) :
    ⁅span R a b t, Q R a⁆ ≤ H R b := by
  have hD : seed R b a ≤ Q R a :=
    (seed_le_fixedSeed w.moving.1).trans (show fixedSeed R b ≤ V R b from inf_le_left) |>.trans
      (V_le_Q_of_dist_add_two_lt R w.color_b (by rw [w.moving.1,earlier.distance]; decide))
  rw [span, Escape.PairingControl.commutator_conjugatesIn _ _ _ hD
    ((show relativeNormalizer R a t ≤ stabilizer R a from inf_le_left).trans (Q_normalized R a))]
  apply conjugatesIn_le _ (H_normalized_by_relativeNormalizer common earlier
    w.color_a w.color_b w.adjacent_a w.adjacent_b w.moving)
  exact (commutator_mono le_rfl
    (Q_le_stabilizer_of_dist_two R a b w.color_a (by rw [SimpleGraph.dist_comm]; exact w.moving.1))).trans
      (seed_commutator common earlier w)

theorem subgroup_le_six_of_le_four [Finite M]
    (common : CommonFacts R source geometry) (earlier : Earlier R geometry)
    {a b c d e s : Vertex R} (D : Subgroup (FreeAmalgam R))
    (ha : color R a = false) (hb : color R b = false) (hc : color R c = false)
    (hd : color R d = false) (he : color R e = false)
    (hba : a ∈ Escape.movingNeighbors geometry b)
    (hca : a ∈ Escape.movingNeighbors geometry c)
    (hdc : c ∈ Escape.movingNeighbors geometry d)
    (hde : e ∈ Escape.movingNeighbors geometry d)
    (hds : Adjacent R d s) (hes : Adjacent R e s)
    (hZe : Z R e ≤ Q R a)
    (hsmall : ⁅D, Q R a⁆ ≤ H R b)
    (hfour : D ≤ Q R d) :
    D ≤ Q R e := by
  have hs : color R s = true := by
    have hn := adjacent_color_ne R hds
    cases h : color R s <;> simp_all
  have hedge := moving_edge_displacement_eq_H common earlier he hd hes hds hde
  have hzero : ⁅D, Z R e⁆ = ⊥ := by
    apply le_bot_iff.mp
    rw [← H_inf_eq_bot_of_moving_chain common earlier ha hb hc hd hba hca hdc]
    refine le_inf ((commutator_mono le_rfl hZe).trans hsmall) ?_
    rw [commutator_comm]
    exact (commutator_mono le_rfl (hfour.trans (Q_le_adjacent_h R hs hds))).trans hedge.le
  rw [← common.centralizer e s he hes]
  exact le_inf (hfour.trans (Q_le_adjacent_h R hs hds))
    (commutator_eq_bot_iff_le_centralizer.mp hzero)

/-- Actual preliminary data for the smaller hat-fixed seed. -/
structure Estimates (R : Subgroup M) (a b t d e : Vertex R) : Prop where
  product : (hatV R b a : Set (FreeAmalgam R)) =
    (Vcirc R b : Set (FreeAmalgam R)) * (seed R b a : Set (FreeAmalgam R))
  seed_comm : ⁅seed R b a, stabilizer R b⁆ ≤ H R b
  span_comm : ⁅span R a b t, Q R a⁆ ≤ H R b
  span_four : span R a b t ≤ Q R d
  span_six : span R a b t ≤ Q R e

private theorem forward_six_of_four [Finite M]
    (common : CommonFacts R source geometry) (earlier : Earlier R geometry)
    {a : Vertex R} (p : SourcePath R a) {i : ℕ} (hi : Even i) (hi4 : 4 ≤ i) (hi6 : i ≤ 6)
    (hsmall : ⁅span R (p.walk.getVert i) (p.walk.getVert (i - 2))
      (p.walk.getVert (i - 1)), Q R (p.walk.getVert i)⁆ ≤ H R (p.walk.getVert (i - 2)))
    (hfour : span R (p.walk.getVert i) (p.walk.getVert (i - 2))
      (p.walk.getVert (i - 1)) ≤ Q R (p.walk.getVert (i + 4))) :
    span R (p.walk.getVert i) (p.walk.getVert (i - 2))
      (p.walk.getVert (i - 1)) ≤ Q R (p.walk.getVert (i + 6)) := by
  have hib : Even (i - 2) := by rw [Nat.even_iff] at hi ⊢; omega
  have hic : Even (i + 2) := hi.add (by decide)
  have hid : Even (i + 4) := hi.add (by decide)
  have hie : Even (i + 6) := hi.add (by decide)
  apply subgroup_le_six_of_le_four common earlier _
    (c := p.walk.getVert (i + 2)) (s := p.walk.getVert (i + 5))
    (p.even_color hi (by omega)) (p.even_color hib (by omega))
    (p.even_color hic (by omega)) (p.even_color hid (by omega))
    (p.even_color hie (by omega))
  · simpa only [Nat.sub_add_cancel (by omega : 2 ≤ i)] using
      (p.moving_neighbors source common earlier hib (by omega) (by omega)).2
  · simpa only [Nat.add_sub_cancel] using
      (p.moving_neighbors source common earlier hic (by omega) (by omega)).1
  · simpa only [show i + 4 - 2 = i + 2 by omega] using
      (p.moving_neighbors source common earlier hid (by omega) (by omega)).1
  · simpa only [Nat.add_assoc] using
      (p.moving_neighbors source common earlier hid (by omega) (by omega)).2
  · simpa only [Nat.add_assoc] using p.adjacent (i := i + 4) (by omega)
  · exact adjacent_symm R (by
      simpa only [Nat.add_assoc] using p.adjacent (i := i + 5) (by omega))
  · apply Z_le_Q_of_dist_lt R _ (geometry.exists_critical _ (p.even_color hie (by omega)))
    rw [geometry.distance_constant _ (p.even_color hie (by omega))]
    change _ < geometry.b R
    rw [earlier.distance, SimpleGraph.dist_comm, p.distance (geometry := geometry) (by omega) (by omega)]
    omega
  · exact hsmall
  · exact hfour

/-- All forward estimates now follow from common/earlier on the same path. -/
theorem estimates_forward [Finite M]
    (common : CommonFacts R source geometry) (earlier : Earlier R geometry)
    {a : Vertex R} (p : SourcePath R a) {i : ℕ}
    (hi : Even i) (hi4 : 4 ≤ i) (hi6 : i ≤ 6) :
    Estimates R (p.walk.getVert i) (p.walk.getVert (i-2)) (p.walk.getVert (i-1))
      (p.walk.getVert (i+4)) (p.walk.getVert (i+6)) := by
  let w := forwardWindow common earlier p hi hi4 hi6
  have hsmall := span_commutator common earlier w
  have hfour := (span_le_full w.moving.1).trans
    (PathExtension.forward_span_le_four common earlier p hi hi4 hi6)
  exact ⟨hat_split_forward common earlier p hi hi4 hi6,
    seed_commutator common earlier w,hsmall,hfour,
    forward_six_of_four common earlier p hi hi4 hi6 hsmall hfour⟩

private theorem backward_six_of_four [Finite M]
    (common : CommonFacts R source geometry) (earlier : Earlier R geometry)
    {a : Vertex R} (p : SourcePath R a) {i : ℕ} (hi : Even i) (hi8 : 8 ≤ i) (hi10 : i ≤ 10)
    (hsmall : ⁅span R (p.walk.getVert i) (p.walk.getVert (i + 2))
      (p.walk.getVert (i + 1)), Q R (p.walk.getVert i)⁆ ≤ H R (p.walk.getVert (i + 2)))
    (hfour : span R (p.walk.getVert i) (p.walk.getVert (i + 2))
      (p.walk.getVert (i + 1)) ≤ Q R (p.walk.getVert (i - 4))) :
    span R (p.walk.getVert i) (p.walk.getVert (i + 2))
      (p.walk.getVert (i + 1)) ≤ Q R (p.walk.getVert (i - 6)) := by
  have hib : Even (i + 2) := hi.add (by decide)
  have hic : Even (i - 2) := by rw [Nat.even_iff] at hi ⊢; omega
  have hid : Even (i - 4) := by rw [Nat.even_iff] at hi ⊢; omega
  have hie : Even (i - 6) := by rw [Nat.even_iff] at hi ⊢; omega
  apply subgroup_le_six_of_le_four common earlier _
    (c := p.walk.getVert (i - 2)) (s := p.walk.getVert (i - 5))
    (p.even_color hi (by omega)) (p.even_color hib (by omega))
    (p.even_color hic (by omega)) (p.even_color hid (by omega))
    (p.even_color hie (by omega))
  · simpa only [Nat.add_sub_cancel] using
      (p.moving_neighbors source common earlier hib (by omega) (by omega)).1
  · simpa only [Nat.sub_add_cancel (by omega : 2 ≤ i)] using
      (p.moving_neighbors source common earlier hic (by omega) (by omega)).2
  · simpa only [show i - 4 + 2 = i - 2 by omega] using
      (p.moving_neighbors source common earlier hid (by omega) (by omega)).2
  · simpa only [Nat.sub_sub] using
      (p.moving_neighbors source common earlier hid (by omega) (by omega)).1
  · exact adjacent_symm R (by
      simpa only [show i - 5 + 1 = i - 4 by omega] using p.adjacent (i := i - 5) (by omega))
  · simpa only [show i - 6 + 1 = i - 5 by omega] using
      p.adjacent (i := i - 6) (by omega)
  · apply Z_le_Q_of_dist_lt R _ (geometry.exists_critical _ (p.even_color hie (by omega)))
    rw [geometry.distance_constant _ (p.even_color hie (by omega))]
    change _ < geometry.b R
    rw [earlier.distance, p.distance (geometry := geometry) (by omega) (by omega)]
    omega
  · exact hsmall
  · exact hfour
/-- All reflected estimates follow on the same supplied source path. -/
theorem estimates_backward [Finite M]
    (common : CommonFacts R source geometry) (earlier : Earlier R geometry)
    {a : Vertex R} (p : SourcePath R a) {i : ℕ}
    (hi : Even i) (hi8 : 8 ≤ i) (hi10 : i ≤ 10) :
    Estimates R (p.walk.getVert i) (p.walk.getVert (i+2)) (p.walk.getVert (i+1))
      (p.walk.getVert (i-4)) (p.walk.getVert (i-6)) := by
  let w := backwardWindow common earlier p hi hi8 hi10
  have hsmall := span_commutator common earlier w
  have hfour := (span_le_full w.moving.1).trans
    (PathExtension.backward_span_le_four common earlier p hi hi8 hi10)
  exact ⟨hat_split_backward common earlier p hi hi8 hi10,
    seed_commutator common earlier w,hsmall,hfour,
    backward_six_of_four common earlier p hi hi8 hi10 hsmall hfour⟩

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Early.Orbit.Source.HatIdentity.SmallSeed
