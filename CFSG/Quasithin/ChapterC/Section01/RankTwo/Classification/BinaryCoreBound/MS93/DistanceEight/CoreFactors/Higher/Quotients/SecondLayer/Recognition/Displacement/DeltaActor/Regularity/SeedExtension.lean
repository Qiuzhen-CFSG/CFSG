module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Higher.Path
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Higher.OrbitGeometry.Replacement.Unequal
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.RegularPaths.Construction
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.RegularPaths.CommutatorPropagation.Neighbor

/-!
# Extending a prescribed regular critical window

One critical eight-window with turns and unequal edge Z-layers extends to
all fourteen edges of the standing MS93 (4.5) path, preserving the whole
seed at indices four through twelve. Reverse the window, apply the actual
prescribed replacement, and reverse back to append two edges; then prepend
two pairs of edges. Each replacement retains the existing vertices and
critical windows. Criticality prevents backtracking, and the amalgam tree
makes the resulting walk geodesic.

The local chain construction adapts `Early/First/Path.lean`, retaining its
mathematics while adding the overlap equations needed to preserve a supplied
segment. Equal incident Z-layers have equal edge kernels by the binary
centralizer theorem; thus the nonnormalizing replacement also preserves
Z-separation without a second natural-module calculation.

`sourcePath_iff_regular_critical_seed` gives the exact remaining obligation
for any prescribed middle four-segment, including the actual delta--c--a
segment. The converse extracts indices four through twelve. This does not
assert that the supplied segment has such a critical extension.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), (4.4.4) and the standing choice for (4.5), printed pp.894--896.
-/

@[expose] public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Higher.Quotients.SecondLayer.Recognition.Displacement.Regularity
open PathCentrality PathCentrality.RegularPaths
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}

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
  intro he
  have hQ : Q R (act R g (p.walk.getVert 1)) = Q R (p.walk.getVert 1) := by
    rw [← Higher.OrbitGeometry.Replacement.Unequal.edge_Z_centralizer common earlier p.start_color hnew,
      ← Higher.OrbitGeometry.Replacement.Unequal.edge_Z_centralizer common earlier p.start_color hfirst, he]
  rw [← edgeCommutator_act, hga] at hE
  have hec : edgeCommutator R a (p.walk.getVert 1) = edgeCommutator R a t := by
    simpa only [edgeCommutator, hQ] using hE
  apply hn
  rw [← hec]
  exact endpoint_normalizes_first common p

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

-- A chain retains every critical window and all its interior separations.
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
  separated : ∀ i, Even i → 2 ≤ i → i + 2 ≤ walk.length →
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

-- Prepend the same conjugated two-edge segment used by conjugateShift.
private theorem growing_step (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) {n : ℕ} (w : GrowingPath R n) :
    ∃ v : GrowingPath R (n + 1), ∀ i, v.walk.getVert (i + 2) = w.walk.getVert i := by
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
    separated := ?_ }, overlap⟩
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
      exact w.separated (i - 2) he (by omega)
        (by rw [hv] at himax; rw [w.length_eq]; omega)


private def GrowingPath.reverse (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) {n : ℕ} (w : GrowingPath R n) : GrowingPath R n where
  first := w.last
  last := w.first
  walk := w.walk.reverse
  start_color := by
    have h := (walk_vertex_color w.start_color w.walk (i := w.walk.length) le_rfl).mpr
      (by rw [w.length_eq]; exact Even.add (by decide) (even_two_mul n))
    simpa only [SimpleGraph.Walk.getVert_length] using h
  length_eq := by rw [SimpleGraph.Walk.length_reverse, w.length_eq]
  isPath := w.isPath.reverse
  critical := by
    intro i hi himax
    have hn : Even (2 * n - i) := by rw [Nat.even_iff] at hi ⊢; omega
    have h := w.critical (2 * n - i) hn (by omega)
    have hcolor (j : ℕ) (hj : Even j) (hle : j ≤ 8 + 2 * n) :
        color R (w.walk.getVert j) = false :=
      (walk_vertex_color w.start_color w.walk (by rw [w.length_eq]; exact hle)).mpr hj
    have ha := hcolor (2 * n - i) hn (by omega)
    have hb := hcolor (2 * n - i + 8) (hn.add (by decide)) (by omega)
    have hc : CriticalPair R (w.walk.getVert (2 * n - i))
        (w.walk.getVert (2 * n - i + 8)) (geometry.exists_critical _ ha) := by
      refine ⟨?_, h.2⟩
      exact h.1.trans (earlier.distance.symm.trans (geometry.distance_constant _ ha).symm)
    have hr := common.critical_reverse _ ha _ hb hc
    simp only [SimpleGraph.Walk.getVert_reverse, w.length_eq]
    have h₁ : 8 + 2 * n - i = 2 * n - i + 8 := by omega
    have h₂ : 8 + 2 * n - (i + 8) = 2 * n - i := by omega
    rw [h₁, h₂, SimpleGraph.dist_comm]
    exact ⟨h.1, hr.2⟩
  turns := by
    intro i hi hi2 hiend
    change i + 2 ≤ w.walk.reverse.length at hiend
    rw [SimpleGraph.Walk.length_reverse, w.length_eq] at hiend
    have he : Even (8 + 2 * n - i) := by rw [Nat.even_iff] at hi ⊢; omega
    obtain ⟨g, hg, ht⟩ := w.turns (8 + 2 * n - i) he (by omega)
      (by rw [w.length_eq]; omega)
    refine ⟨g⁻¹, ?_, ?_⟩
    · rw [SimpleGraph.Walk.getVert_reverse, w.length_eq]
      exact (stabilizer R _).inv_mem hg
    · simp only [SimpleGraph.Walk.getVert_reverse, w.length_eq]
      have hh := congrArg (act R g⁻¹) ht
      rw [← act_mul, mul_inv_cancel, act_one] at hh
      rw [show 8 + 2 * n - (i + 2) = 8 + 2 * n - i - 2 by omega,
        show 8 + 2 * n - (i - 2) = 8 + 2 * n - i + 2 by omega]
      exact hh.symm
  separated := by
    intro i hi hi2 hiend
    change i + 2 ≤ w.walk.reverse.length at hiend
    rw [SimpleGraph.Walk.length_reverse, w.length_eq] at hiend
    have he : Even (8 + 2 * n - i) := by rw [Nat.even_iff] at hi ⊢; omega
    have h := w.separated (8 + 2 * n - i) he (by omega) (by rw [w.length_eq]; omega)
    change Z R (w.walk.reverse.getVert (i - 1)) ≠ Z R (w.walk.reverse.getVert (i + 1))
    simp only [SimpleGraph.Walk.getVert_reverse, w.length_eq]
    rw [show 8 + 2 * n - (i - 1) = 8 + 2 * n - i + 1 by omega,
      show 8 + 2 * n - (i + 1) = 8 + 2 * n - i - 1 by omega]
    exact h.symm

private theorem growing_append (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) {n : ℕ} (w : GrowingPath R n) :
    ∃ v : GrowingPath R (n + 1), ∀ i, i ≤ w.walk.length →
      v.walk.getVert i = w.walk.getVert i := by
  obtain ⟨v, hv⟩ := growing_step common earlier (w.reverse common earlier)
  refine ⟨v.reverse common earlier, ?_⟩
  intro i hi
  change v.walk.reverse.getVert i = _
  rw [SimpleGraph.Walk.getVert_reverse, v.length_eq]
  have hidx : 8 + 2 * (n + 1) - i = (8 + 2 * n - i) + 2 := by
    rw [w.length_eq] at hi
    omega
  rw [hidx, hv]
  change w.walk.reverse.getVert (8 + 2 * n - i) = _
  rw [SimpleGraph.Walk.getVert_reverse, w.length_eq]
  congr 1
  rw [w.length_eq] at hi
  omega

/-- Extend a regular critical eight-window to the complete source path,
keeping the whole original window at indices four through twelve. In
particular, every prescribed vertex of its first four-segment is retained.
The seed's existence is an additional premise, not a conclusion here. -/
public theorem sourcePath_of_regular_critical_seed
    (common : CommonFacts R source geometry) (earlier : Earlier R geometry)
    {a e : Vertex R} (p : CriticalPath R geometry a e)
    (hp : HasTurnConjugators R p)
    (hsep : ∀ i, Even i → 2 ≤ i → i + 2 ≤ p.walk.length →
      Z R (p.walk.getVert (i - 1)) ≠ Z R (p.walk.getVert (i + 1))) :
    ∃ q : Higher.SourcePath a, ∀ i, i ≤ 8 → q.walk.getVert (i + 4) = p.walk.getVert i := by
  let w : GrowingPath R 0 := {
    first := a
    last := e
    walk := p.walk
    start_color := p.start_color
    length_eq := by simpa using p.length_eq_b.trans earlier.distance
    isPath := p.isPath
    critical := by
      intro i _ hi
      have hi0 : i = 0 := by omega
      subst i
      have hl : p.walk.length = 8 := p.length_eq_b.trans earlier.distance
      rw [Nat.zero_add, SimpleGraph.Walk.getVert_zero, ← hl, SimpleGraph.Walk.getVert_length]
      exact ⟨p.shortest.symm, p.critical.2⟩
    turns := hp
    separated := hsep }
  obtain ⟨v, hv⟩ := growing_append common earlier w
  obtain ⟨v₁, hv₁⟩ := growing_step common earlier v
  obtain ⟨v₂, hv₂⟩ := growing_step common earlier v₁
  have overlap (i : ℕ) (hi : i ≤ 8) : v₂.walk.getVert (i + 4) = p.walk.getVert i := by
    rw [show i + 4 = (i + 2) + 2 by omega, hv₂, hv₁, hv i (by rw [w.length_eq]; omega)]
  have hshort : v₂.walk.length = (cosetGraph R).dist v₂.first v₂.last := by
    obtain ⟨u, hu⟩ := (cosetGraph_connected R).exists_walk_length_eq_dist v₂.first v₂.last
    have heq : v₂.walk = u := Subtype.mk.inj
      (geometry.tree.isAcyclic.subsingleton_path _ _ |>.elim
        ⟨v₂.walk, v₂.isPath⟩ ⟨u, u.isPath_of_length_eq_dist hu⟩)
    rwa [heq]
  refine ⟨{
    first := v₂.first
    last := v₂.last
    walk := v₂.walk
    start_color := v₂.start_color
    length_eq := v₂.length_eq
    shortest := hshort
    center_eq := by simpa using overlap 0 (by decide)
    turns := fun i hi hi2 hi12 => v₂.turns i hi hi2 (by rw [v₂.length_eq]; omega)
    critical := fun i hi hi6 => v₂.critical i hi hi6
    distinct_Z := fun i hi hi2 hi12 => v₂.separated i hi hi2 (by rw [v₂.length_eq]; omega) },
    overlap⟩

/-- The prescribed fourteen-edge path exists exactly when its fixed four-segment
extends to one separated regular critical eight-window. The forward direction
takes indices four through twelve. The reverse direction keeps those eight edges
while performing the three preceding-source replacements. -/
public theorem sourcePath_iff_regular_critical_seed
    (common : CommonFacts R source geometry) (earlier : Earlier R geometry)
    (a c d t : Vertex R) :
    (∃ q : Higher.SourcePath a,
      q.walk.getVert 6 = c ∧ q.walk.getVert 8 = d ∧ q.walk.getVert 7 = t) ↔
    (∃ e, ∃ p : CriticalPath R geometry a e,
      HasTurnConjugators R p ∧
      (∀ i, Even i → 2 ≤ i → i + 2 ≤ p.walk.length →
        Z R (p.walk.getVert (i - 1)) ≠ Z R (p.walk.getVert (i + 1))) ∧
      p.walk.getVert 2 = c ∧ p.walk.getVert 4 = d ∧ p.walk.getVert 3 = t) := by
  constructor
  · rintro ⟨q, hc, hd, ht⟩
    have hend : ((q.walk.drop 4).getVert 8) = q.walk.getVert 12 := by
      rw [SimpleGraph.Walk.drop_getVert]
    let w := ((q.walk.drop 4).take 8).copy q.center_eq hend
    have hlen : w.length = 8 := by
      simp only [w, SimpleGraph.Walk.length_copy, SimpleGraph.Walk.take_length,
        SimpleGraph.Walk.drop_length, q.length_eq]
      rfl
    have hv (i : ℕ) (hi : i ≤ 8) : w.getVert i = q.walk.getVert (i + 4) := by
      simp only [w, SimpleGraph.Walk.getVert_copy, SimpleGraph.Walk.take_getVert,
        Nat.min_eq_right hi, SimpleGraph.Walk.drop_getVert, Nat.add_comm]
    have ha : color R a = false := by
      rw [← q.center_eq]
      exact (walk_vertex_color q.start_color q.walk (by rw [q.length_eq]; decide)).mpr
        (by decide : Even 4)
    let p : CriticalPath R geometry a (q.walk.getVert 12) := {
      start_color := ha
      walk := w
      shortest := by
        rw [hlen]
        simpa only [q.center_eq] using (q.dist (i := 4) (j := 12) (by decide) (by decide)).symm
      critical := by
        have h := q.critical 4 (by decide) (by decide)
        rw [q.center_eq] at h
        refine ⟨?_, h.2⟩
        exact h.1.trans (earlier.distance.symm.trans (geometry.distance_constant _ ha).symm) }
    have hp : HasTurnConjugators R p := by
      intro i hi hi2 hiend
      change i + 2 ≤ w.length at hiend
      rw [hlen] at hiend
      obtain ⟨g, hg, hgturn⟩ := q.turns (i + 4) (hi.add (by decide)) (by omega) (by omega)
      refine ⟨g, ?_, ?_⟩
      · change g ∈ stabilizer R (w.getVert i)
        rwa [hv i (by omega)]
      · change act R g (w.getVert (i + 2)) = w.getVert (i - 2)
        rw [hv (i + 2) hiend, hv (i - 2) (by omega)]
        convert hgturn using 1
        congr 1
        omega
    refine ⟨_, p, hp, ?_, ?_, ?_, ?_⟩
    · intro i hi hi2 hiend
      change i + 2 ≤ w.length at hiend
      rw [hlen] at hiend
      change Z R (w.getVert (i - 1)) ≠ Z R (w.getVert (i + 1))
      rw [hv (i - 1) (by omega), hv (i + 1) (by omega)]
      have h := q.distinct_Z (i + 4) (hi.add (by decide)) (by omega) (by omega)
      convert h using 1
      congr 2
      omega
    · exact (hv 2 (by decide)).trans hc
    · exact (hv 4 (by decide)).trans hd
    · exact (hv 3 (by decide)).trans ht
  · rintro ⟨e, p, hp, hsep, hc, hd, ht⟩
    obtain ⟨q, hq⟩ := sourcePath_of_regular_critical_seed common earlier p hp hsep
    exact ⟨q, (hq 2 (by decide)).trans hc,
      (hq 4 (by decide)).trans hd, (hq 3 (by decide)).trans ht⟩

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Higher.Quotients.SecondLayer.Recognition.Displacement.Regularity
