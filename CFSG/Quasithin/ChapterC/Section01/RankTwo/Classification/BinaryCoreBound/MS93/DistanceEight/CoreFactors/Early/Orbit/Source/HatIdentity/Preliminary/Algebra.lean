module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Early.Orbit.Source.HatIdentity.Preliminary.Contracts

/-!
# Seed and span commutators in the preliminary D calculation

The moving-edge identity gives H_b = [Z_a,Q_t]. It both bounds the first
hat layer's Q_b-displacement and makes H_b invariant under the literal
relative normalizer at a. The decomposition then puts the full fixed seed
in that layer. Local generation bounds its commutator with G_b; taking
right conjugates bounds the span's commutator with Q_a. No conjugator is
assumed to fix b or to normalize a distant kernel.

Source: Meierfrankenfeld--Stellmacher (1993), (4.5.3)(i), printed p.897.
-/

@[expose] public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped Pointwise
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Early.Orbit.Source.HatIdentity.Preliminary
open PathCentrality NormalizerTransfer
variable {M : Type*} [Group M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}

private theorem conjugatesIn_le {G : Type*} [Group G] {A P K : Subgroup G}
    (hA : A ≤ K) (hn : P ≤ normalizer K) : conjugatesIn A P ≤ K := by
  apply iSup_le
  intro g
  exact (map_mono hA).trans
    (mem_normalizer_iff_map_conj_eq.mp (hn (P.inv_mem g.property))).le

private theorem H_normalized (a : Vertex R) :
    stabilizer R a ≤ normalizer (H R a : Set (FreeAmalgam R)) := by
  intro g hg
  rw [mem_normalizer_iff_map_conj_eq]
  change (⁅Vcirc R a, Q R a⁆ : Subgroup (FreeAmalgam R)).map _ = _
  rw [map_commutator, mem_normalizer_iff_map_conj_eq.mp (Vcirc_normalized a hg),
    mem_normalizer_iff_map_conj_eq.mp (Q_normalized R a hg)]
  rfl

/-- The moving edge identifies H_b with [Z_a,Q_t], so the literal relative
normalizer at a normalizes H_b without fixing b. -/
theorem H_normalized_by_relativeNormalizer [Finite M]
    (common : CommonFacts R source geometry) (earlier : Earlier R geometry)
    {a b t : Vertex R} (ha : color R a = false) (hb : color R b = false)
    (hat : Adjacent R a t) (hbt : Adjacent R b t)
    (hmove : a ∈ Escape.movingNeighbors geometry b) :
    relativeNormalizer R a t ≤ normalizer (H R b : Set (FreeAmalgam R)) := by
  rw [← moving_edge_displacement_eq_H common earlier ha hb hat hbt hmove]
  intro g hg
  rw [mem_normalizer_iff_map_conj_eq, map_commutator,
    mem_normalizer_iff_map_conj_eq.mp (Z_normalized R a hg.1),
    mem_normalizer_iff_map_conj_eq.mp hg.2]

/-- The first hat layer has displacement in H_b under Q_b. This supplies
its quotient action before the natural-section decomposition is proved. -/
theorem hatV_commutator_le_H [Finite M]
    (common : CommonFacts R source geometry) (earlier : Earlier R geometry)
    {a b t : Vertex R} (ha : color R a = false) (hb : color R b = false)
    (hat : Adjacent R a t) (hbt : Adjacent R b t)
    (hmove : a ∈ Escape.movingNeighbors geometry b) :
    ⁅hatV R b a, Q R b⁆ ≤ H R b := by
  have ht : color R t = true := by
    have hn := adjacent_color_ne R hat
    cases h : color R t <;> simp_all
  have hZQ : Z R a ≤ Q R b := by
    apply Z_le_Q_of_dist_lt R a (geometry.exists_critical a ha)
    rw [geometry.distance_constant a ha]
    change (cosetGraph R).dist a b < geometry.b R
    rw [SimpleGraph.dist_comm, hmove.1, earlier.distance]
    decide
  rw [hatV_eq_conjugatesIn,
    Escape.PairingControl.commutator_conjugatesIn _ _ _ hZQ (Q_normalized R b)]
  apply conjugatesIn_le _ (H_normalized b)
  exact (commutator_mono le_rfl (Q_le_adjacent_h R ht hbt)).trans
    (moving_edge_displacement_eq_H common earlier ha hb hat hbt hmove).le

/-- Once the natural decomposition includes D₀ in the first hat layer,
its commutator with the entire local group lies in the printed H_b. -/
theorem seed_commutator_of_le_hatV [Finite M]
    (common : CommonFacts R source geometry) (earlier : Earlier R geometry)
    {a b t : Vertex R} (ha : color R a = false) (hb : color R b = false)
    (hat : Adjacent R a t) (hbt : Adjacent R b t)
    (hmove : a ∈ Escape.movingNeighbors geometry b)
    (hseed : fixedSeed R b ≤ hatV R b a) :
    ⁅fixedSeed R b, stabilizer R b⁆ ≤ H R b := by
  have hhat := hatV_commutator_le_H common earlier ha hb hat hbt hmove
  have hQ : ⁅fixedSeed R b, Q R b⁆ ≤ H R b :=
    (commutator_mono hseed le_rfl).trans hhat
  have hL : ⁅Ltilde R b, fixedSeed R b⁆ = ⊥ := by
    rw [commutator_comm]
    exact commutator_eq_bot_iff_le_centralizer.mpr inf_le_right
  have hpre : stabilizer R b ≤
      commutatorPreimage (stabilizer R b) (fixedSeed R b) (H R b) := by
    conv_lhs => rw [← source.local_generation b hb]
    exact sup_le
      (le_commutatorPreimage (Ltilde_le_stabilizer b) (hL.le.trans bot_le))
      (le_commutatorPreimage (fun _ hx => hx.1) (by rwa [commutator_comm]))
  rw [commutator_comm]
  exact (commutator_mono hpre le_rfl).trans
    (commutator_commutatorPreimage_le _ _ _ (H_normalized b))

/-- Conjugating the seed bound uses normalization of Q_a and H_b, not
normalization of the preceding vertex or of a distant kernel. -/
theorem span_commutator_of_seed_bound [Finite M]
    (common : CommonFacts R source geometry) (earlier : Earlier R geometry)
    {a b t : Vertex R} (ha : color R a = false) (hb : color R b = false)
    (hat : Adjacent R a t) (hbt : Adjacent R b t)
    (hmove : a ∈ Escape.movingNeighbors geometry b)
    (hseed : ⁅fixedSeed R b, stabilizer R b⁆ ≤ H R b) :
    ⁅normalizerSpan R a b t, Q R a⁆ ≤ H R b := by
  have hD : fixedSeed R b ≤ Q R a :=
    (show fixedSeed R b ≤ V R b from inf_le_left).trans
      (V_le_Q_of_dist_add_two_lt R hb (by rw [hmove.1, earlier.distance]; decide))
  rw [normalizerSpan, Escape.PairingControl.commutator_conjugatesIn _ _ _ hD
    ((show relativeNormalizer R a t ≤ stabilizer R a from inf_le_left).trans
      (Q_normalized R a))]
  apply conjugatesIn_le _
    (H_normalized_by_relativeNormalizer common earlier ha hb hat hbt hmove)
  exact (commutator_mono le_rfl
    (Q_le_stabilizer_of_dist_two R a b ha (by rw [SimpleGraph.dist_comm]; exact hmove.1))).trans hseed

/-- The natural product supplies both commutator fields by the preceding
algebra; its source proof is the only premise retained here. -/
theorem seedEstimates_of_product [Finite M]
    (common : CommonFacts R source geometry) (earlier : Earlier R geometry)
    {a b t : Vertex R} (ha : color R a = false) (hb : color R b = false)
    (hat : Adjacent R a t) (hbt : Adjacent R b t)
    (hmove : a ∈ Escape.movingNeighbors geometry b)
    (hprod : (hatV R b a : Set (FreeAmalgam R)) =
      (Vcirc R b : Set (FreeAmalgam R)) * (fixedSeed R b : Set (FreeAmalgam R))) :
    SeedEstimates R a b t := by
  have hseed : fixedSeed R b ≤ hatV R b a := by
    intro x hx
    change x ∈ (hatV R b a : Set (FreeAmalgam R))
    rw [hprod]
    exact ⟨1, (Vcirc R b).one_mem, x, hx, one_mul x⟩
  have hcomm := seed_commutator_of_le_hatV common earlier ha hb hat hbt hmove hseed
  exact ⟨hprod, hcomm,
    span_commutator_of_seed_bound common earlier ha hb hat hbt hmove hcomm⟩


end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Early.Orbit.Source.HatIdentity.Preliminary
