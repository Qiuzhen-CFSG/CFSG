module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Early.First.Geometry
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.RegularPaths.Construction
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.RegularPaths.CommutatorPropagation.Neighbor
public import Theory.GroupTheory.Commutator.NormalizedIndexTwo

/-!
# The complete chosen path for MS93 (4.5)

The regular critical window supplied by `Earlier.extended` is a seed. At
its first vertex choose an edge not normalized by the critical endpoint,
then apply `Earlier.replacement` with that edge. The same conjugator gives
a new critical window and a turn at the join. The two edge indices identify
the edge commutator with the natural subgroup intersected with its edge
Z-layer, so this choice also separates the two edge Z-layers.

Six such extensions put all required turns and separations in the first
fourteen edges. Criticality prevents backtracking at each join, and the
amalgam tree makes the whole walk simple. Truncation retains the four critical
windows; one more nonnormalizing edge supplies the outside predecessor.
Finally the original right action moves the fourth vertex to the requested
center. No extra geometric hypothesis is used, and each replacement keeps
the same conjugator in its criticality and edge-displacement clauses.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), (4.4.4) and the choice preceding (4.5.1), printed pp.894--896.
-/

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Early
open PathCentrality PathCentrality.RegularPaths
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}

-- The fixed index two makes the action quadratic; evaluation computes its displacement.
private theorem edge_natural (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) {a t : Vertex R} (ha : color R a = false)
    (hat : Adjacent R a t) : edgeCommutator R a t = U R a ⊓ Z R t := by
  have hloc : Q R t ≤ stabilizer R a := fun _ hx => hx.2 a (adjacent_symm R hat)
  have hE : ⁅Z R a, Q R t⁆ ≤ Z R t :=
    commutator_le_of_normalized_index_two _ _ _
      (Escape.EdgeTransfer.edge_Z_le a t ha hat) (earlier.edge_Z_index a t ha hat)
      (hloc.trans (Z_normalized R a))
      ((show Q R t ≤ stabilizer R t from fun _ hx => hx.1).trans (Z_normalized R t))
  have hfixed := Escape.EdgeTransfer.edge_Z_eq_fixed common.large_distance (moduleFacts common) a t ha hat
  let := geometry.Z_elementary (lt_trans (by decide : 0 < 2) common.large_distance) a ha
  have hcard := DistanceFour.Early.actor_index_eq_displacement_card_of_fixed_index_two
    (Z R a) (Q R t) (hloc.trans (Z_normalized R a))
    (hE.trans (hfixed.le.trans inf_le_right))
    (by rw [← hfixed]; exact earlier.edge_Z_index a t ha hat)
  have hc : (centralizer (Z R a : Set (FreeAmalgam R))).relIndex (Q R t) = 4 := by
    rw [← inf_relIndex_right, inf_comm, common.centralizer a t ha hat]
    exact earlier.edge_Q_index a t ha hat
  exact (Escape.Propagation.edge_fixed_natural_eq_commutator common.large_distance
    (moduleFacts common) a t ha hat hE (hcard.symm.trans hc)).symm

omit [Finite M] in
private theorem endpoint_normalizes_first (common : CommonFacts R source geometry)
    {a a' : Vertex R} (p : CriticalPath R geometry a a') :
    Z R a' ≤ stabilizer R a ⊓
      normalizer (edgeCommutator R a (p.walk.getVert 1) : Set (FreeAmalgam R)) := by
  have hlocal := p.endpoint_Z_le_start_stabilizer (by have := common.large_distance; omega)
  have hQ : Z R a' ≤ Q R (p.walk.getVert 1) := by
    apply Z_le_Q_of_dist_lt R a' (geometry.exists_critical a' p.end_color)
    rw [SimpleGraph.dist_comm, p.dist_end, geometry.distance_constant a' p.end_color]
    change p.walk.length - 1 < geometry.b R
    have := p.length_eq_b
    have := common.large_distance
    omega
  exact le_inf hlocal (hQ.trans (normalizer_commutator_ge_right _ _))

private theorem edge_ne_of_nonnormalizing (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) {a a' t : Vertex R}
    (p : CriticalPath R geometry a a') (hat : Adjacent R a t)
    (hn : ¬ Z R a' ≤ stabilizer R a ⊓
      normalizer (edgeCommutator R a t : Set (FreeAmalgam R))) :
    Z R t ≠ Z R (p.walk.getVert 1) := by
  have hl := p.length_eq_b
  have hb := common.large_distance
  have hfirst : Adjacent R a (p.walk.getVert 1) := by
    simpa using (cosetGraph_adj R _ _).mp (p.walk.adj_getVert_succ (i := 0) (by omega))
  intro heq
  apply hn
  rw [edge_natural common earlier p.start_color hat, heq,
    ← edge_natural common earlier p.start_color hfirst]
  exact endpoint_normalizes_first common p

private theorem exists_replacement (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) {a a' : Vertex R}
    (p : CriticalPath R geometry a a') (hp : HasTurnConjugators R p) :
    ∃ g ∈ stabilizer R a,
      ¬ (Z R (p.walk.getVert 2)).map (MulAut.conj g⁻¹).toMonoidHom ≤
        Q R (p.walk.getVert (p.walk.length - 2)) ∧
      Z R (act R g (p.walk.getVert 1)) ≠ Z R (p.walk.getVert 1) := by
  obtain ⟨t, ht, hn⟩ := CommutatorPropagation.exists_nonnormalizing_neighbor common p
  obtain ⟨g, hg, hE, hcrit⟩ := earlier.replacement _ _ p hp t ht hn
  refine ⟨g, hg, hcrit, ?_⟩
  have hga : act R g a = a := hg
  have hl := p.length_eq_b
  have hb := common.large_distance
  have hfirst : Adjacent R a (p.walk.getVert 1) := by
    simpa using (cosetGraph_adj R _ _).mp (p.walk.adj_getVert_succ (i := 0) (by omega))
  have hnew : Adjacent R a (act R g (p.walk.getVert 1)) := by
    simpa only [hga] using (adjacent_act_iff R g _ _).mpr hfirst
  apply edge_ne_of_nonnormalizing common earlier p hnew
  rw [← edgeCommutator_act, hga] at hE
  rwa [hE]

private theorem path_of_no_backtracking {V : Type*} {G : SimpleGraph V}
    (hG : G.IsAcyclic) {a b : V} (w : G.Walk a b)
    (h : ∀ i, i + 2 ≤ w.length → w.getVert i ≠ w.getVert (i + 2)) : w.IsPath := by
  apply (hG.isPath_iff_isChain w).mpr
  induction w with
  | nil => simp
  | @cons a b c hab w ih =>
    have hw := ih (fun i hi => by simpa using h (i + 1) (by simpa using hi))
    cases w with
    | nil => simp
    | @cons b d c hbd w =>
      simp only [SimpleGraph.Walk.edges_cons, List.isChain_cons_cons]
      refine ⟨?_, hw⟩
      have hne := h 0 (by simp)
      simpa [hab.ne] using hne

-- After n replacements, the first 2n interior even positions are separated.
-- Every critical window and every turn is retained along the longer walk.
private structure GrowingPath (R : Subgroup M) (n : ℕ) where
  first : Vertex R
  last : Vertex R
  walk : (cosetGraph R).Walk first last
  start_color : color R first = false
  length_eq : walk.length = 8 + 2 * n
  isPath : walk.IsPath
  critical : ∀ i, Even i → i ≤ 2 * n →
    (cosetGraph R).dist (walk.getVert i) (walk.getVert (i + 8)) = 8 ∧
      ¬ Z R (walk.getVert i) ≤ Q R (walk.getVert (i + 8))
  turns : ∀ i, Even i → 2 ≤ i → i + 2 ≤ walk.length →
    ∃ g ∈ stabilizer R (walk.getVert i),
      act R g (walk.getVert (i + 2)) = walk.getVert (i - 2)
  separated : ∀ i, Even i → 2 ≤ i → i ≤ 2 * n →
    Z R (walk.getVert (i - 1)) ≠ Z R (walk.getVert (i + 1))

private def GrowingPath.prefix (earlier : Earlier R geometry) {n : ℕ} (w : GrowingPath R n) :
    CriticalPath R geometry w.first (w.walk.getVert 8) where
  start_color := w.start_color
  walk := w.walk.take 8
  shortest := by
    have h := w.critical 0 (by decide) (by omega)
    simpa only [SimpleGraph.Walk.take_length, w.length_eq, Nat.min_eq_left (show 8 ≤ 8 + 2 * n by omega),
      SimpleGraph.Walk.getVert_zero, Nat.zero_add] using h.1.symm
  critical := by
    have h := w.critical 0 (by decide) (by omega)
    change (cosetGraph R).dist w.first (w.walk.getVert 8) =
      criticalDistance R w.first (geometry.exists_critical _ w.start_color) ∧ _
    simp only [SimpleGraph.Walk.getVert_zero, Nat.zero_add] at h
    exact ⟨h.1.trans (earlier.distance.symm.trans
      (geometry.distance_constant _ w.start_color).symm), h.2⟩

omit [Finite M] in
private theorem GrowingPath.prefix_getVert (earlier : Earlier R geometry) {n : ℕ}
    (w : GrowingPath R n) {i : ℕ} (hi : i ≤ 8) :
    (w.prefix earlier).walk.getVert i = w.walk.getVert i := by
  exact (SimpleGraph.Walk.take_getVert _ _ _).trans (congrArg w.walk.getVert (Nat.min_eq_right hi))

omit [Finite M] in
private theorem GrowingPath.prefix_regular (earlier : Earlier R geometry) {n : ℕ}
    (w : GrowingPath R n) : HasTurnConjugators R (w.prefix earlier) := by
  intro i hi hi2 hil
  have hl : (w.prefix earlier).walk.length = 8 :=
    (w.prefix earlier).length_eq_b.trans earlier.distance
  obtain ⟨g, hg, ht⟩ := w.turns i hi hi2 (by rw [w.length_eq]; omega)
  exact ⟨g, by rwa [w.prefix_getVert earlier (by omega)], by
    rw [w.prefix_getVert earlier (by omega), w.prefix_getVert earlier (by omega)]
    exact ht⟩

omit [Finite M] in
private theorem growing_zero (earlier : Earlier R geometry) {a a' : Vertex R}
    (p : CriticalPath R geometry a a') (hp : HasTurnConjugators R p) :
    Nonempty (GrowingPath R 0) := by
  refine ⟨{
    first := a
    last := a'
    walk := p.walk
    start_color := p.start_color
    length_eq := by simpa using p.length_eq_b.trans earlier.distance
    isPath := p.isPath
    turns := hp
    critical := ?_
    separated := ?_ }⟩
  · intro i _ hi
    have hi0 : i = 0 := by omega
    subst i
    have hl : p.walk.length = 8 := p.length_eq_b.trans earlier.distance
    rw [Nat.zero_add, SimpleGraph.Walk.getVert_zero, ← hl, SimpleGraph.Walk.getVert_length]
    exact ⟨p.shortest.symm, p.critical.2⟩
  · intro i _ hi hlim
    omega

-- Prepend the same conjugated two-edge segment used by conjugateShift.
private theorem growing_step (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) {n : ℕ} (w : GrowingPath R n) :
    Nonempty (GrowingPath R (n + 1)) := by
  let p := w.prefix earlier
  have hp := w.prefix_regular earlier
  have hl : p.walk.length = 8 := p.length_eq_b.trans earlier.distance
  have hb : 4 ≤ geometry.b R := by rw [earlier.distance]; decide
  obtain ⟨g, hg, hn, hne⟩ := exists_replacement common earlier p hp
  have hga : act R g w.first = w.first := hg
  let q : (cosetGraph R).Walk (act R g (p.walk.getVert 2)) w.first :=
    (actWalk R g (p.walk.take 2).reverse).copy rfl hga
  have hq : q.length = 2 := by
    simp only [q, SimpleGraph.Walk.length_copy, actWalk_length,
      SimpleGraph.Walk.length_reverse, SimpleGraph.Walk.take_length, hl]
    decide
  let v := q.append w.walk
  have hv : v.length = 8 + 2 * (n + 1) := by
    simp only [v, SimpleGraph.Walk.length_append, hq, w.length_eq]
    omega
  have overlap (i : ℕ) : v.getVert (i + 2) = w.walk.getVert i := by
    simp only [v, SimpleGraph.Walk.getVert_append, hq, if_neg (by omega : ¬ i + 2 < 2),
      Nat.add_sub_cancel]
  let p' := p.conjugateShift (by omega) g hg hn
  have hp' : p'.walk.length = 8 := p'.length_eq_b.trans earlier.distance
  have first_eight (i : ℕ) (hi : i ≤ 8) : v.getVert i = p'.walk.getVert i := by
    have he : p'.walk = q.append (p.walk.take (p.walk.length - 2)) := rfl
    rw [he]
    change (q.append w.walk).getVert i = _
    rw [SimpleGraph.Walk.getVert_append, SimpleGraph.Walk.getVert_append, hq]
    split_ifs with h
    · rfl
    · rw [SimpleGraph.Walk.take_getVert, hl, Nat.min_eq_right (by omega),
        w.prefix_getVert earlier (by omega)]
  have hvpath : v.IsPath := by
    apply path_of_no_backtracking geometry.tree.isAcyclic
    intro i hi heq
    by_cases hi2 : i < 2
    · rw [first_eight i (by omega), first_eight (i + 2) (by omega)] at heq
      have := p'.isPath.getVert_injOn (by simp only [Set.mem_ofPred_eq, hp']; omega)
        (by simp only [Set.mem_ofPred_eq, hp']; omega) heq
      omega
    · have hsub : i - 2 + 2 = i := by omega
      rw [← hsub, overlap, hsub, overlap] at heq
      have := w.isPath.getVert_injOn (by simp only [Set.mem_ofPred_eq, w.length_eq]; omega)
        (by simp only [Set.mem_ofPred_eq, w.length_eq]; rw [hv] at hi; omega) heq
      omega
  refine ⟨{
    first := _
    last := w.last
    walk := v
    start_color := p'.start_color
    length_eq := hv
    isPath := hvpath
    critical := ?_
    turns := ?_
    separated := ?_ }⟩
  · intro i hi himax
    by_cases hi0 : i = 0
    · subst i
      rw [first_eight 0 (by omega), first_eight 8 (by omega)]
      have hend : p'.walk.getVert 8 = p.walk.getVert (p.walk.length - 2) := by
        simpa only [hp'] using p'.walk.getVert_length
      rw [SimpleGraph.Walk.getVert_zero, hend]
      exact ⟨p'.shortest.symm.trans hp', p'.critical.2⟩
    · have hi2 : 2 ≤ i := by rw [Nat.even_iff] at hi; omega
      have he : Even (i - 2) := by rw [Nat.even_iff] at hi ⊢; omega
      have h := w.critical (i - 2) he (by omega)
      rw [show i = (i - 2) + 2 by omega, overlap,
        show i - 2 + 2 + 8 = (i - 2 + 8) + 2 by omega, overlap]
      exact h
  · intro i hi hi2 himax
    by_cases hi_eq : i = 2
    · subst i
      have hreg := hasTurnConjugators_conjugateShift p hb hp g hg hn
      obtain ⟨k, hk, ht⟩ := hreg 2 (by decide) (by omega) (by rw [hp']; decide)
      exact ⟨k, by rwa [first_eight 2 (by omega)], by
        rw [first_eight 4 (by omega), first_eight 0 (by omega)]; exact ht⟩
    · have hi4 : 4 ≤ i := by rw [Nat.even_iff] at hi; omega
      have he : Even (i - 2) := by rw [Nat.even_iff] at hi ⊢; omega
      obtain ⟨k, hk, ht⟩ := w.turns (i - 2) he (by omega)
        (by rw [w.length_eq]; rw [hv] at himax; omega)
      refine ⟨k, ?_, ?_⟩
      · rw [show i = (i - 2) + 2 by omega, overlap]; exact hk
      · rw [overlap, show i - 2 = (i - 2 - 2) + 2 by omega, overlap]
        simpa only [Nat.sub_add_cancel hi2] using ht
  · intro i hi hi2 himax
    by_cases hi_eq : i = 2
    · subst i
      have h1 : v.getVert 1 = act R g (p.walk.getVert 1) := by
        simp only [v, SimpleGraph.Walk.getVert_append, hq, if_pos (by decide : 1 < 2),
          q, SimpleGraph.Walk.getVert_copy, actWalk_getVert, SimpleGraph.Walk.getVert_reverse,
          SimpleGraph.Walk.take_length, hl, SimpleGraph.Walk.take_getVert]
        rfl
      have h3 : v.getVert 3 = p.walk.getVert 1 :=
        (overlap 1).trans (w.prefix_getVert earlier (by omega)).symm
      simpa only [show 2 - 1 = 1 by rfl, show 2 + 1 = 3 by rfl, h1, h3] using hne
    · have hi4 : 4 ≤ i := by rw [Nat.even_iff] at hi; omega
      have he : Even (i - 2) := by rw [Nat.even_iff] at hi ⊢; omega
      rw [show i - 1 = (i - 2 - 1) + 2 by omega,
        show i + 1 = (i - 2 + 1) + 2 by omega, overlap, overlap]
      exact w.separated (i - 2) he (by omega) (by omega)

private theorem sourcePath_of_growing (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) (w : GrowingPath R 6) :
    Nonempty (SourcePath R (w.walk.getVert 4)) := by
  let p := w.prefix earlier
  obtain ⟨t, ht, hn⟩ := CommutatorPropagation.exists_nonnormalizing_neighbor common p
  have hne := edge_ne_of_nonnormalizing common earlier p ht hn
  have hv (i : ℕ) (hi : i ≤ 14) : (w.walk.take 14).getVert i = w.walk.getVert i := by
    rw [SimpleGraph.Walk.take_getVert, Nat.min_eq_right hi]
  refine ⟨{
    first := w.first
    last := w.walk.getVert 14
    walk := w.walk.take 14
    start_color := w.start_color
    length_eq := by rw [SimpleGraph.Walk.take_length, w.length_eq]; rfl
    isPath := w.isPath.take 14
    center_eq := hv 4 (by decide)
    critical := ?_
    turns := ?_
    edge_Z_ne := ?_
    predecessor := t
    predecessor_adjacent := ht
    first_edge_Z_ne := ?_ }⟩
  · intro i hi hi6
    rw [hv i (by omega), hv (i + 8) (by omega)]
    exact w.critical i hi (by omega)
  · intro i hi hi2 hi12
    rw [hv i (by omega), hv (i + 2) (by omega), hv (i - 2) (by omega)]
    exact w.turns i hi hi2 (by rw [w.length_eq]; omega)
  · intro i hi hi2 hi12
    rw [hv (i - 1) (by omega), hv (i + 1) (by omega)]
    exact w.separated i hi hi2 (by omega)
  · rw [hv 1 (by omega)]
    simpa only [p, w.prefix_getVert earlier (by decide : 1 ≤ 8)] using hne

omit [Finite M] in
private def sourcePath_act {a : Vertex R} (p : SourcePath R a) (g : FreeAmalgam R)
    (geometry : Geometry R) : SourcePath R (act R g a) where
  first := act R g p.first
  last := act R g p.last
  walk := actWalk R g p.walk
  start_color := (action_preserves_color R g _).trans p.start_color
  length_eq := (actWalk_length R g p.walk).trans p.length_eq
  isPath := by
    apply path_of_no_backtracking geometry.tree.isAcyclic
    intro i hi heq
    rw [actWalk_length] at hi
    rw [actWalk_getVert, actWalk_getVert] at heq
    have hh := congrArg (act R g⁻¹) heq
    simp only [← act_mul, mul_inv_cancel, act_one] at hh
    have := p.isPath.getVert_injOn (by change i ≤ p.walk.length; omega)
      (by change i + 2 ≤ p.walk.length; exact hi) hh
    omega
  center_eq := by rw [actWalk_getVert, p.center_eq]
  critical := by
    intro i hi hi6
    rw [actWalk_getVert, actWalk_getVert, dist_act, Z_act, Q_act]
    exact ⟨(p.critical i hi hi6).1, fun h => (p.critical i hi hi6).2
      ((map_le_map_iff_of_injective (MulAut.conj g⁻¹).injective).mp h)⟩
  turns := by
    intro i hi hi2 hi12
    obtain ⟨h, hh, ht⟩ := p.turns i hi hi2 hi12
    refine ⟨g⁻¹ * h * g, ?_, ?_⟩
    · rw [actWalk_getVert, stabilizer_act]
      simpa only [MulAut.conj_apply, inv_inv, MulEquiv.toMonoidHom_eq_coe,
        MonoidHom.coe_coe] using mem_map_of_mem (MulAut.conj g⁻¹).toMonoidHom hh
    · rw [actWalk_getVert, actWalk_getVert, ← act_mul]
      simp only [← mul_assoc, mul_inv_cancel, one_mul, act_mul, ht]
  edge_Z_ne := by
    intro i hi hi2 hi12
    rw [actWalk_getVert, actWalk_getVert, Z_act, Z_act]
    exact fun he => p.edge_Z_ne i hi hi2 hi12
      ((Subgroup.map_injective (MulAut.conj g⁻¹).injective) he)
  predecessor := act R g p.predecessor
  predecessor_adjacent := (adjacent_act_iff R g _ _).mpr p.predecessor_adjacent
  first_edge_Z_ne := by
    rw [actWalk_getVert, Z_act, Z_act]
    exact fun he => p.first_edge_Z_ne
      ((Subgroup.map_injective (MulAut.conj g⁻¹).injective) he)

/-- The complete path chosen for (4.5), including the turn at twelve and the
outside predecessor. Only the genuine preceding-source input remains explicit. -/
public theorem sourcePath_nonempty (source : LocalSource L R)
    (common : CommonFacts R source geometry) (earlier : Earlier R geometry)
    (a : Vertex R) (ha : color R a = false) : Nonempty (SourcePath R a) := by
  obtain ⟨e⟩ := earlier.extended a ha
  have grow : ∀ n, Nonempty (GrowingPath R n) := by
    intro n
    induction n with
    | zero =>
      exact growing_zero earlier (e.window 0 (by decide) (by omega))
        (e.window_regular 0 (by decide) (by omega))
    | succ n ih =>
      obtain ⟨w⟩ := ih
      exact growing_step common earlier w
  obtain ⟨w⟩ := grow 6
  obtain ⟨p⟩ := sourcePath_of_growing common earlier w
  have hc : color R (w.walk.getVert 4) = false := by
    simpa only [p.center_eq] using p.even_color (i := 4) (by decide) (by omega)
  obtain ⟨x, hx⟩ := exists_mVertex_of_color R hc
  obtain ⟨y, hy⟩ := exists_mVertex_of_color R ha
  have hact : act R (x⁻¹ * y) (w.walk.getVert 4) = a := by
    rw [hx, hy, act_mVertex]
    simp only [← mul_assoc, mul_inv_cancel, one_mul]
  exact hact ▸ ⟨sourcePath_act p (x⁻¹ * y) geometry⟩

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Early
