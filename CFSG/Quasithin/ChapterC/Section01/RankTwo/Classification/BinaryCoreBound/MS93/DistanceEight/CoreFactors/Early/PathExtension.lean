module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Early.First.Path

/-!
# Extending a prescribed regular critical window

A separated regular critical eight-edge window is extended by one replacement
on the left and two on the right. Each replacement preserves the overlapping
walk, all critical windows, and every interior turn. The tree property prevents
backtracking. Reversal uses the actual reverse-critical-pair theorem.

The resulting source path contains the original window at positions two through
ten. Thus later applications of (4.5.1) can retain a prescribed vertex and kernel,
instead of substituting an unrelated path. The geometric extension itself uses
only distance eight and the stated replacement choices. Its source adapter derives
those choices and an external predecessor from the preceding (4.4) inputs.

Source: Meierfrankenfeld--Stellmacher (1993), (4.4.4) and (4.5.3)(i),
printed pp.894--897, specifically the rechoice in claim (1).
-/

@[expose] public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Early.PathExtension
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

theorem exists_replacement (common : CommonFacts R source geometry)
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

-- Every interior even position is separated. All critical windows and turns
-- are retained when the segment is extended.
structure RegularSegment (R : Subgroup M) (n : ℕ) where
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
  separated : ∀ i, Even i → 2 ≤ i → i + 2 ≤ walk.length →
    Z R (walk.getVert (i - 1)) ≠ Z R (walk.getVert (i + 1))

def RegularSegment.prefix (hb : geometry.b R = 8) {n : ℕ} (w : RegularSegment R n) :
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
    exact ⟨h.1.trans (hb.symm.trans
      (geometry.distance_constant _ w.start_color).symm), h.2⟩

omit [Finite M] in
theorem RegularSegment.prefix_getVert (hb : geometry.b R = 8) {n : ℕ}
    (w : RegularSegment R n) {i : ℕ} (hi : i ≤ 8) :
    (w.prefix hb).walk.getVert i = w.walk.getVert i := by
  exact (SimpleGraph.Walk.take_getVert _ _ _).trans (congrArg w.walk.getVert (Nat.min_eq_right hi))

omit [Finite M] in
theorem RegularSegment.prefix_regular (hb : geometry.b R = 8) {n : ℕ}
    (w : RegularSegment R n) : HasTurnConjugators R (w.prefix hb) := by
  intro i hi hi2 hil
  have hl : (w.prefix hb).walk.length = 8 :=
    (w.prefix hb).length_eq_b.trans hb
  obtain ⟨g, hg, ht⟩ := w.turns i hi hi2 (by rw [w.length_eq]; omega)
  exact ⟨g, by rwa [w.prefix_getVert hb (by omega)], by
    rw [w.prefix_getVert hb (by omega), w.prefix_getVert hb (by omega)]
    exact ht⟩

omit [Finite M] in
private theorem regular_zero (hb : geometry.b R = 8) {a a' : Vertex R}
    (p : CriticalPath R geometry a a') (hp : HasTurnConjugators R p)
    (hs : ∀ i, Even i → 2 ≤ i → i + 2 ≤ p.walk.length →
      Z R (p.walk.getVert (i - 1)) ≠ Z R (p.walk.getVert (i + 1))) :
    Nonempty (Σ' w : RegularSegment R 0, ∀ i, w.walk.getVert i = p.walk.getVert i) := by
  refine ⟨⟨{
    first := a
    last := a'
    walk := p.walk
    start_color := p.start_color
    length_eq := by simpa using p.length_eq_b.trans hb
    isPath := p.isPath
    turns := hp
    critical := ?_
    separated := hs }, fun _ => rfl⟩⟩
  · intro i _ hi
    have hi0 : i = 0 := by omega
    subst i
    have hl : p.walk.length = 8 := p.length_eq_b.trans hb
    rw [Nat.zero_add, SimpleGraph.Walk.getVert_zero, ← hl, SimpleGraph.Walk.getVert_length]
    exact ⟨p.shortest.symm, p.critical.2⟩

-- Prepend the same conjugated two-edge segment used by conjugateShift.
omit [Finite M] in
theorem prepend (hb : geometry.b R = 8)
    (replace : ∀ a a' (p : CriticalPath R geometry a a'), HasTurnConjugators R p →
      ∃ g ∈ stabilizer R a,
        ¬ (Z R (p.walk.getVert 2)).map (MulAut.conj g⁻¹).toMonoidHom ≤
          Q R (p.walk.getVert (p.walk.length - 2)) ∧
        Z R (act R g (p.walk.getVert 1)) ≠ Z R (p.walk.getVert 1))
    {n : ℕ} (w : RegularSegment R n) :
    Nonempty (Σ' v : RegularSegment R (n + 1),
      ∀ i, v.walk.getVert (i + 2) = w.walk.getVert i) := by
  let p := w.prefix hb
  have hp := w.prefix_regular hb
  have hl : p.walk.length = 8 := p.length_eq_b.trans hb
  have hb4 : 4 ≤ geometry.b R := by rw [hb]; decide
  obtain ⟨g, hg, hn, hne⟩ := replace _ _ p hp
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
  have hp' : p'.walk.length = 8 := p'.length_eq_b.trans hb
  have first_eight (i : ℕ) (hi : i ≤ 8) : v.getVert i = p'.walk.getVert i := by
    have he : p'.walk = q.append (p.walk.take (p.walk.length - 2)) := rfl
    rw [he]
    change (q.append w.walk).getVert i = _
    rw [SimpleGraph.Walk.getVert_append, SimpleGraph.Walk.getVert_append, hq]
    split_ifs with h
    · rfl
    · rw [SimpleGraph.Walk.take_getVert, hl, Nat.min_eq_right (by omega),
        w.prefix_getVert hb (by omega)]
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
  refine ⟨⟨{
    first := _
    last := w.last
    walk := v
    start_color := p'.start_color
    length_eq := hv
    isPath := hvpath
    critical := ?_
    turns := ?_
    separated := ?_ }, overlap⟩⟩
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
      have hreg := hasTurnConjugators_conjugateShift p hb4 hp g hg hn
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
        (overlap 1).trans (w.prefix_getVert hb (by omega)).symm
      simpa only [show 2 - 1 = 1 by rfl, show 2 + 1 = 3 by rfl, h1, h3] using hne
    · have hi4 : 4 ≤ i := by rw [Nat.even_iff] at hi; omega
      have he : Even (i - 2) := by rw [Nat.even_iff] at hi ⊢; omega
      rw [show i - 1 = (i - 2 - 1) + 2 by omega,
        show i + 1 = (i - 2 + 1) + 2 by omega, overlap, overlap]
      exact w.separated (i - 2) he (by omega) (by rw [w.length_eq]; rw [hv] at himax; omega)



omit [Finite M] in
/-- Reversal preserves every critical window and every separated interior turn. -/
def RegularSegment.reverse (common : CommonFacts R source geometry)
    (hb : geometry.b R = 8) {n : ℕ} (w : RegularSegment R n) : RegularSegment R n where
  first := w.last
  last := w.first
  walk := w.walk.reverse
  start_color := by
    have h := (walk_vertex_color w.start_color w.walk (i := w.walk.length) le_rfl).mpr
      (by rw [w.length_eq]; exact (by decide : Even 8).add (even_two_mul n))
    simpa only [SimpleGraph.Walk.getVert_length] using h
  length_eq := (SimpleGraph.Walk.length_reverse _).trans w.length_eq
  isPath := w.isPath.reverse
  critical := by
    intro i hi himax
    let j := 8 + 2 * n - (i + 8)
    have hj : Even j := by dsimp [j]; rw [Nat.even_iff] at hi ⊢; omega
    have hjmax : j ≤ 2 * n := by dsimp [j]; omega
    have ha : color R (w.walk.getVert j) = false :=
      (walk_vertex_color w.start_color w.walk (by rw [w.length_eq]; omega)).mpr hj
    have hf : color R (w.walk.getVert (j + 8)) = false :=
      (walk_vertex_color w.start_color w.walk (by rw [w.length_eq]; omega)).mpr
        (hj.add (by decide))
    have hc := w.critical j hj hjmax
    have hcrit : CriticalPair R (w.walk.getVert j) (w.walk.getVert (j + 8))
        (geometry.exists_critical _ ha) :=
      ⟨hc.1.trans (hb.symm.trans (geometry.distance_constant _ ha).symm), hc.2⟩
    have hr := common.critical_reverse _ ha _ hf hcrit
    simp only [SimpleGraph.Walk.getVert_reverse, w.length_eq]
    have he : 8 + 2 * n - i = j + 8 := by dsimp [j]; omega
    rw [he]
    exact ⟨by rw [SimpleGraph.dist_comm]; exact hc.1, hr.2⟩
  turns := by
    intro i hi hi2 himax
    rw [SimpleGraph.Walk.length_reverse, w.length_eq] at himax
    let j := 8 + 2 * n - i
    have hj : Even j := by dsimp [j]; rw [Nat.even_iff] at hi ⊢; omega
    obtain ⟨g, hg, ht⟩ := w.turns j hj (by dsimp [j]; omega)
      (by rw [w.length_eq]; dsimp [j]; omega)
    have hp : 8 + 2 * n - (i + 2) = j - 2 := by dsimp [j]; omega
    have hm : 8 + 2 * n - (i - 2) = j + 2 := by dsimp [j]; omega
    refine ⟨g⁻¹, ?_, ?_⟩
    · simpa only [SimpleGraph.Walk.getVert_reverse, w.length_eq] using
        (stabilizer R _).inv_mem hg
    · simp only [SimpleGraph.Walk.getVert_reverse, w.length_eq, hp, hm]
      rw [← ht, ← act_mul, mul_inv_cancel, act_one]
  separated := by
    intro i hi hi2 himax
    rw [SimpleGraph.Walk.length_reverse, w.length_eq] at himax
    let j := 8 + 2 * n - i
    have hj : Even j := by dsimp [j]; rw [Nat.even_iff] at hi ⊢; omega
    have h := w.separated j hj (by dsimp [j]; omega)
      (by rw [w.length_eq]; dsimp [j]; omega)
    have hp : 8 + 2 * n - (i + 1) = j - 1 := by dsimp [j]; omega
    have hm : 8 + 2 * n - (i - 1) = j + 1 := by dsimp [j]; omega
    simpa only [SimpleGraph.Walk.getVert_reverse, w.length_eq, hp, hm] using h.symm

omit [Finite M] in
theorem RegularSegment.reverse_getVert (common : CommonFacts R source geometry)
    (hb : geometry.b R = 8) {n : ℕ} (w : RegularSegment R n) (i : ℕ) :
    (w.reverse common hb).walk.getVert i = w.walk.getVert (8 + 2 * n - i) := by
  change w.walk.reverse.getVert i = _
  rw [SimpleGraph.Walk.getVert_reverse, w.length_eq]

omit [Finite M] in
/-- Complete a separated regular critical window without changing any of its
vertices. It occurs at positions two through ten in the resulting length-fourteen segment. -/
theorem complete_segment (common : CommonFacts R source geometry)
    (hb : geometry.b R = 8)
    (replace : ∀ a a' (p : CriticalPath R geometry a a'), HasTurnConjugators R p →
      ∃ g ∈ stabilizer R a,
        ¬ (Z R (p.walk.getVert 2)).map (MulAut.conj g⁻¹).toMonoidHom ≤
          Q R (p.walk.getVert (p.walk.length - 2)) ∧
        Z R (act R g (p.walk.getVert 1)) ≠ Z R (p.walk.getVert 1))
    {a a' : Vertex R} (p : CriticalPath R geometry a a')
    (hp : HasTurnConjugators R p)
    (hs : ∀ i, Even i → 2 ≤ i → i + 2 ≤ p.walk.length →
      Z R (p.walk.getVert (i - 1)) ≠ Z R (p.walk.getVert (i + 1))) :
    Nonempty (Σ' w : RegularSegment R 3,
      ∀ i, i ≤ 8 → w.walk.getVert (i + 2) = p.walk.getVert i) := by
  obtain ⟨⟨w₀, h₀⟩⟩ := regular_zero hb p hp hs
  obtain ⟨⟨w₁, h₁⟩⟩ := prepend hb replace w₀
  obtain ⟨⟨w₂, h₂⟩⟩ := prepend hb replace (w₁.reverse common hb)
  obtain ⟨⟨w₃, h₃⟩⟩ := prepend hb replace w₂
  refine ⟨⟨w₃.reverse common hb, ?_⟩⟩
  intro i hi
  rw [RegularSegment.reverse_getVert]
  have h₃i := h₃ (10 - i)
  have h₂i := h₂ (8 - i)
  have h₁i := h₁ i
  rw [show 8 + 2 * 3 - (i + 2) = (10 - i) + 2 by omega, h₃i,
    show 10 - i = (8 - i) + 2 by omega, h₂i, RegularSegment.reverse_getVert,
    show 8 + 2 * 1 - (8 - i) = i + 2 by omega, h₁i, h₀]

/-- Supply the external predecessor using an actual nonnormalizing edge. -/
theorem sourcePath_of_segment (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) (w : RegularSegment R 3) :
    Nonempty (Σ' p : SourcePath R (w.walk.getVert 4),
      ∀ i, p.walk.getVert i = w.walk.getVert i) := by
  let q := w.prefix earlier.distance
  obtain ⟨t, ht, hn⟩ := CommutatorPropagation.exists_nonnormalizing_neighbor common q
  have hne := edge_ne_of_nonnormalizing common earlier q ht hn
  refine ⟨⟨{
    first := w.first
    last := w.last
    walk := w.walk
    start_color := w.start_color
    length_eq := by simpa using w.length_eq
    isPath := w.isPath
    center_eq := rfl
    critical := by intro i hi hi6; exact w.critical i hi hi6
    turns := by intro i hi hi2 hi12; exact w.turns i hi hi2 (by rw [w.length_eq]; omega)
    edge_Z_ne := by intro i hi hi2 hi12; exact w.separated i hi hi2 (by rw [w.length_eq]; omega)
    predecessor := t
    predecessor_adjacent := ht
    first_edge_Z_ne := ?_ }, fun _ => rfl⟩⟩
  simpa only [q, w.prefix_getVert earlier.distance (by decide : 1 ≤ 8)] using hne

/-- The exact separated critical window embeds into a complete source path,
with its starting vertex at index two and all eight edges unchanged. -/
theorem sourcePath_preserving_window (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) {a a' : Vertex R}
    (p : CriticalPath R geometry a a') (hp : HasTurnConjugators R p)
    (hs : ∀ i, Even i → 2 ≤ i → i + 2 ≤ p.walk.length →
      Z R (p.walk.getVert (i - 1)) ≠ Z R (p.walk.getVert (i + 1))) :
    ∃ c, Nonempty (Σ' q : SourcePath R c,
      ∀ i, i ≤ 8 → q.walk.getVert (i + 2) = p.walk.getVert i) := by
  obtain ⟨⟨w, hw⟩⟩ := complete_segment common earlier.distance
    (fun _ _ p hp => exists_replacement common earlier p hp) p hp hs
  obtain ⟨⟨q, hq⟩⟩ := sourcePath_of_segment common earlier w
  exact ⟨_, ⟨⟨q, fun i hi => (hq _).trans (hw i hi)⟩⟩⟩


omit [Finite M] in
/-- The literal critical eight-edge window in a source path. -/
def sourceWindow (hb : geometry.b R = 8) {a : Vertex R}
    (p : SourcePath R a) (i : ℕ) (hi : Even i) (hi6 : i ≤ 6) :
    CriticalPath R geometry (p.walk.getVert i) (p.walk.getVert (i + 8)) := by
  let w : (cosetGraph R).Walk (p.walk.getVert i) (p.walk.getVert (i + 8)) :=
    ((p.walk.drop i).take 8).copy rfl (SimpleGraph.Walk.drop_getVert _ _ _)
  have hw : w.length = 8 := by
    simp only [w, SimpleGraph.Walk.length_copy, SimpleGraph.Walk.take_length,
      SimpleGraph.Walk.drop_length, p.length_eq]
    omega
  have hc := p.even_color hi (by omega)
  exact ⟨hc, w, hw.trans (p.critical i hi hi6).1.symm,
    ⟨(p.critical i hi hi6).1.trans (hb.symm.trans
      (geometry.distance_constant _ hc).symm), (p.critical i hi hi6).2⟩⟩

omit [Finite M] in
theorem sourceWindow_getVert (hb : geometry.b R = 8) {a : Vertex R}
    (p : SourcePath R a) (i : ℕ) (hi : Even i) (hi6 : i ≤ 6)
    (j : ℕ) (hj : j ≤ 8) :
    (sourceWindow hb p i hi hi6).walk.getVert j = p.walk.getVert (i + j) := by
  simp only [sourceWindow, SimpleGraph.Walk.getVert_copy, SimpleGraph.Walk.take_getVert,
    inf_eq_right.mpr hj, SimpleGraph.Walk.drop_getVert]

omit [Finite M] in
theorem sourceWindow_regular (hb : geometry.b R = 8) {a : Vertex R}
    (p : SourcePath R a) (i : ℕ) (hi : Even i) (hi6 : i ≤ 6) :
    HasTurnConjugators R (sourceWindow hb p i hi hi6) := by
  intro j hj hj2 hjend
  have hl : (sourceWindow hb p i hi hi6).walk.length = 8 :=
    (sourceWindow hb p i hi hi6).length_eq_b.trans hb
  obtain ⟨g, hg, ht⟩ := p.turns (i + j) (hi.add hj) (by omega) (by omega)
  refine ⟨g, ?_, ?_⟩
  · rwa [sourceWindow_getVert hb p i hi hi6 j (by omega)]
  · rw [sourceWindow_getVert hb p i hi hi6 (j + 2) (by omega),
      sourceWindow_getVert hb p i hi hi6 (j - 2) (by omega)]
    simpa only [Nat.add_assoc, show i + (j - 2) = i + j - 2 by omega] using ht

omit [Finite M] in
def segmentOfSourcePath {a : Vertex R} (p : SourcePath R a) : RegularSegment R 3 where
  first := p.first
  last := p.last
  walk := p.walk
  start_color := p.start_color
  length_eq := by simpa using p.length_eq
  isPath := p.isPath
  critical := p.critical
  turns := by intro i hi hi2 hiend; exact p.turns i hi hi2 (by rw [p.length_eq] at hiend; omega)
  separated := by intro i hi hi2 hiend; exact p.edge_Z_ne i hi hi2 (by rw [p.length_eq] at hiend; omega)

/-- Reverse a source path and choose its exterior predecessor independently.
Every vertex on the fourteen-edge walk remains the literal reversed vertex. -/
theorem reverse_sourcePath (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) {a : Vertex R} (p : SourcePath R a) :
    ∃ c, Nonempty (Σ' q : SourcePath R c,
      ∀ i, q.walk.getVert i = p.walk.getVert (14 - i)) := by
  obtain ⟨⟨q, hq⟩⟩ := sourcePath_of_segment common earlier
    ((segmentOfSourcePath p).reverse common earlier.distance)
  refine ⟨_, ⟨⟨q, ?_⟩⟩⟩
  intro i
  rw [hq, RegularSegment.reverse_getVert]
  rfl


end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Early.PathExtension
