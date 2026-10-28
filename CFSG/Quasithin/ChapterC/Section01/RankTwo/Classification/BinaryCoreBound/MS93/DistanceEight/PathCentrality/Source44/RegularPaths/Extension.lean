module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.RegularPaths.Construction
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.RegularPaths.Extension
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.RegularPaths.CommutatorPropagation.Neighbor

/-!
# Extending regular critical paths before determining the distance

Starting with a regular critical path, a prescribed replacement prepends two
edges. The resulting segment retains every critical window, all interior
turns, and the original endpoint nonnormalization at the new join. Four such
steps produce the literal length-b+8 path; an actual amalgam action places its
index-four center at any prescribed vertex of the correct color.

Only the prescribed-replacement theorem is used here. No distance-eight
conclusion, edge centrality, or natural-section conclusion is assumed. The
replacement source proof is a separate obligation in this family.

Source: Meierfrankenfeld--Stellmacher (1993), (4.4.4) and the opening of
(4.4.5), printed p.894. The finite-segment argument adapts the later fixed-eight
construction while preserving the earlier variable critical distance.
-/

@[expose] public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.Source44.RegularPaths
open PathCentrality.RegularPaths
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}

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

structure Segment (geometry : Geometry R) (n : ℕ) where
  first : Vertex R
  last : Vertex R
  walk : (cosetGraph R).Walk first last
  start_color : color R first = false
  length_eq : walk.length = geometry.b R + 2 * n
  isPath : walk.IsPath
  critical : ∀ i, Even i → i ≤ 2 * n →
    (cosetGraph R).dist (walk.getVert i) (walk.getVert (i + geometry.b R)) = geometry.b R ∧
      ¬ Z R (walk.getVert i) ≤ Q R (walk.getVert (i + geometry.b R))
  turns : ∀ i, Even i → 2 ≤ i → i + 2 ≤ walk.length →
    ∃ g ∈ stabilizer R (walk.getVert i),
      act R g (walk.getVert (i + 2)) = walk.getVert (i - 2)
  nonnormalization : ∀ i, Even i → 2 ≤ i → i ≤ 2 * n →
    ¬ Z R (walk.getVert (i + geometry.b R)) ≤ stabilizer R (walk.getVert i) ⊓
      normalizer (edgeCommutator R (walk.getVert i) (walk.getVert (i - 1)) : Set (FreeAmalgam R))

noncomputable def Segment.prefix {n : ℕ} (w : Segment geometry n) :
    CriticalPath R geometry w.first (w.walk.getVert (geometry.b R)) where
  start_color := w.start_color
  walk := w.walk.take (geometry.b R)
  shortest := by
    have h := w.critical 0 (by decide) (by omega)
    simpa only [SimpleGraph.Walk.take_length, w.length_eq,
      Nat.min_eq_left (show geometry.b R ≤ geometry.b R + 2 * n by omega),
      SimpleGraph.Walk.getVert_zero, Nat.zero_add] using h.1.symm
  critical := by
    have h := w.critical 0 (by decide) (by omega)
    simp only [SimpleGraph.Walk.getVert_zero, Nat.zero_add] at h
    exact ⟨h.1.trans (geometry.distance_constant _ w.start_color).symm, h.2⟩

omit [Finite M] in
theorem Segment.prefix_getVert {n : ℕ} (w : Segment geometry n) {i : ℕ}
    (hi : i ≤ geometry.b R) : w.prefix.walk.getVert i = w.walk.getVert i := by
  exact (SimpleGraph.Walk.take_getVert _ _ _).trans (congrArg w.walk.getVert (Nat.min_eq_right hi))

omit [Finite M] in
theorem Segment.prefix_regular {n : ℕ} (w : Segment geometry n) :
    HasTurnConjugators R w.prefix := by
  intro i hi hi2 hil
  have hl := w.prefix.length_eq_b
  obtain ⟨g, hg, ht⟩ := w.turns i hi hi2 (by rw [w.length_eq]; omega)
  exact ⟨g, by rwa [w.prefix_getVert (by omega)], by
    rw [w.prefix_getVert (by omega), w.prefix_getVert (by omega)]; exact ht⟩

private def initial {a a' : Vertex R} (p : CriticalPath R geometry a a')
    (hp : HasTurnConjugators R p) : Segment geometry 0 where
  first := a
  last := a'
  walk := p.walk
  start_color := p.start_color
  length_eq := by simpa using p.length_eq_b
  isPath := p.isPath
  critical := by
    intro i _ hi
    have hi0 : i = 0 := by omega
    subst i
    rw [Nat.zero_add, SimpleGraph.Walk.getVert_zero, ← p.length_eq_b,
      SimpleGraph.Walk.getVert_length]
    exact ⟨p.shortest.symm, p.critical.2⟩
  turns := hp
  nonnormalization := by intro i _ hi hi0; omega

theorem prepend (common : CommonFacts R source geometry) (hb : 4 ≤ geometry.b R)
    (replacement : ∀ {a a'} (p : CriticalPath R geometry a a'),
      HasTurnConjugators R p → PrescribedReplacement R p)
    {n : ℕ} (w : Segment geometry n) :
    Nonempty (Σ' v : Segment geometry (n + 1),
      ∀ i, v.walk.getVert (i + 2) = w.walk.getVert i) := by
  let p := w.prefix
  have hp := w.prefix_regular
  have hl : p.walk.length = geometry.b R := p.length_eq_b
  obtain ⟨t, ht, hnon⟩ := CommutatorPropagation.exists_nonnormalizing_neighbor common p
  obtain ⟨g, hg, hedge, hn⟩ := replacement p hp t ht hnon
  have hga : act R g w.first = w.first := hg
  let q : (cosetGraph R).Walk (act R g (p.walk.getVert 2)) w.first :=
    (actWalk R g (p.walk.take 2).reverse).copy rfl hga
  have hq : q.length = 2 := by
    simp only [q, SimpleGraph.Walk.length_copy, actWalk_length,
      SimpleGraph.Walk.length_reverse, SimpleGraph.Walk.take_length, hl]
    omega
  let v := q.append w.walk
  have hv : v.length = geometry.b R + 2 * (n + 1) := by
    simp only [v, SimpleGraph.Walk.length_append, hq, w.length_eq]
    omega
  have overlap (i : ℕ) : v.getVert (i + 2) = w.walk.getVert i := by
    simp only [v, SimpleGraph.Walk.getVert_append, hq, if_neg (by omega : ¬ i + 2 < 2),
      Nat.add_sub_cancel]
  let p' := p.conjugateShift (by omega) g hg hn
  have hp' : p'.walk.length = geometry.b R := p'.length_eq_b
  have first_window (i : ℕ) (hi : i ≤ geometry.b R) : v.getVert i = p'.walk.getVert i := by
    have he : p'.walk = q.append (p.walk.take (p.walk.length - 2)) := rfl
    rw [he]
    change (q.append w.walk).getVert i = _
    rw [SimpleGraph.Walk.getVert_append, SimpleGraph.Walk.getVert_append, hq]
    split_ifs with h
    · rfl
    · rw [SimpleGraph.Walk.take_getVert, hl, Nat.min_eq_right (by omega),
        w.prefix_getVert (by omega)]
  have hvpath : v.IsPath := by
    apply path_of_no_backtracking geometry.tree.isAcyclic
    intro i hi heq
    by_cases hi2 : i < 2
    · rw [first_window i (by omega), first_window (i + 2) (by omega)] at heq
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
    nonnormalization := ?_ }, overlap⟩⟩
  · intro i hi himax
    by_cases hi0 : i = 0
    · subst i
      rw [Nat.zero_add, first_window 0 (by omega), first_window (geometry.b R) le_rfl]
      have hend : p'.walk.getVert (geometry.b R) = p.walk.getVert (p.walk.length - 2) := by
        simpa only [hp'] using p'.walk.getVert_length
      rw [SimpleGraph.Walk.getVert_zero, hend]
      exact ⟨p'.shortest.symm.trans hp', p'.critical.2⟩
    · have hi2 : 2 ≤ i := by rw [Nat.even_iff] at hi; omega
      have he : Even (i - 2) := by rw [Nat.even_iff] at hi ⊢; omega
      have h := w.critical (i - 2) he (by omega)
      rw [show i = (i - 2) + 2 by omega, overlap,
        show i - 2 + 2 + geometry.b R = (i - 2 + geometry.b R) + 2 by omega, overlap]
      exact h
  · intro i hi hi2 himax
    by_cases hi_eq : i = 2
    · subst i
      have hreg := hasTurnConjugators_conjugateShift p hb hp g hg hn
      obtain ⟨k, hk, hkturn⟩ := hreg 2 (by decide) (by omega) (by rw [hp']; omega)
      exact ⟨k, by rwa [first_window 2 (by omega)], by
        rw [first_window 4 hb, first_window 0 (by omega)]; exact hkturn⟩
    · have hi4 : 4 ≤ i := by rw [Nat.even_iff] at hi; omega
      have he : Even (i - 2) := by rw [Nat.even_iff] at hi ⊢; omega
      obtain ⟨k, hk, hkturn⟩ := w.turns (i - 2) he (by omega)
        (by rw [w.length_eq]; rw [hv] at himax; omega)
      refine ⟨k, ?_, ?_⟩
      · rw [show i = (i - 2) + 2 by omega, overlap]; exact hk
      · rw [overlap, show i - 2 = (i - 2 - 2) + 2 by omega, overlap]
        simpa only [Nat.sub_add_cancel hi2] using hkturn
  · intro i hi hi2 himax
    by_cases hi_eq : i = 2
    · subst i
      have h1 : v.getVert 1 = act R g (p.walk.getVert 1) := by
        simp only [v, SimpleGraph.Walk.getVert_append, hq, if_pos (by decide : 1 < 2),
          q, SimpleGraph.Walk.getVert_copy, actWalk_getVert, SimpleGraph.Walk.getVert_reverse,
          SimpleGraph.Walk.take_length, hl, Nat.min_eq_left (show 2 ≤ geometry.b R by omega),
          Nat.reduceSub, SimpleGraph.Walk.take_getVert, Nat.min_eq_right (by decide : 1 ≤ 2)]
      have hstart : v.getVert 2 = w.first := by simpa using overlap 0
      have hend : v.getVert (2 + geometry.b R) = p.walk.getVert (geometry.b R) := by
        rw [Nat.add_comm, overlap, w.prefix_getVert le_rfl]
      rw [hstart, hend, h1]
      have hge : edgeCommutator R w.first (act R g (p.walk.getVert 1)) =
          edgeCommutator R w.first t := by
        rw [← hedge, ← edgeCommutator_act, hga]
      rw [hge]
      simpa only [← hl, SimpleGraph.Walk.getVert_length] using hnon
    · have hi4 : 4 ≤ i := by rw [Nat.even_iff] at hi; omega
      have he : Even (i - 2) := by rw [Nat.even_iff] at hi ⊢; omega
      rw [show i = (i - 2) + 2 by omega, overlap,
        show i - 2 + 2 + geometry.b R = (i - 2 + geometry.b R) + 2 by omega, overlap,
        show i - 2 + 2 - 1 = (i - 2 - 1) + 2 by omega, overlap]
      exact w.nonnormalization (i - 2) he (by omega) (by omega)


theorem exists_segment (common : CommonFacts R source geometry) (hb : 4 ≤ geometry.b R)
    (replacement : ∀ {a a'} (p : CriticalPath R geometry a a'),
      HasTurnConjugators R p → PrescribedReplacement R p)
    {a a' : Vertex R} (p : CriticalPath R geometry a a') (hp : HasTurnConjugators R p)
    (n : ℕ) : Nonempty (Segment geometry n) := by
  induction n with
  | zero => exact ⟨initial p hp⟩
  | succ n ih =>
    obtain ⟨w⟩ := ih
    obtain ⟨⟨v, _⟩⟩ := prepend common hb replacement w
    exact ⟨v⟩

noncomputable def Segment.toExtended (w : Segment geometry 4) :
    ExtendedPath geometry (w.walk.getVert 4) where
  first := w.first
  last := w.last
  walk := w.walk
  start_color := w.start_color
  length_eq := by simpa using w.length_eq
  isPath := w.isPath
  center_eq := rfl
  critical := by intro i hi hib; exact w.critical i hi hib
  nonnormalization := by intro i hi hi2 hib; exact w.nonnormalization i hi hi2 hib
  turns := by intro i hi hi2 hib; exact w.turns i hi hi2 (by rw [w.length_eq]; omega)

noncomputable def extendedAct {a : Vertex R} (e : ExtendedPath geometry a)
    (g : FreeAmalgam R) : ExtendedPath geometry (act R g a) where
  first := act R g e.first
  last := act R g e.last
  walk := actWalk R g e.walk
  start_color := (action_preserves_color R g _).trans e.start_color
  length_eq := (actWalk_length R g _).trans e.length_eq
  isPath := by
    apply path_of_no_backtracking geometry.tree.isAcyclic
    intro i hi heq
    rw [actWalk_length] at hi
    rw [actWalk_getVert, actWalk_getVert] at heq
    have he := congrArg (act R g⁻¹) heq
    simp only [← act_mul, mul_inv_cancel, act_one] at he
    have := e.isPath.getVert_injOn (by simpa using (show i ≤ e.walk.length by omega))
      (by simpa using hi) he
    omega
  center_eq := by rw [actWalk_getVert, e.center_eq]
  critical := by
    intro i hi hib
    rw [actWalk_getVert, actWalk_getVert, dist_act, Z_act, Q_act]
    refine ⟨(e.critical i hi hib).1, ?_⟩
    intro h
    exact (e.critical i hi hib).2
      ((map_le_map_iff_of_injective (MulAut.conj g⁻¹).injective).mp h)
  nonnormalization := by
    intro i hi hi2 hib h
    simp only [actWalk_getVert, Z_act, stabilizer_act, edgeCommutator_act] at h
    rw [← map_normalizer_eq_of_bijective
      (edgeCommutator R (e.walk.getVert i) (e.walk.getVert (i - 1)))
      (f := (MulAut.conj g⁻¹).toMonoidHom) (MulAut.conj g⁻¹).bijective,
      ← map_inf _ _ (MulAut.conj g⁻¹).toMonoidHom (MulAut.conj g⁻¹).injective] at h
    exact e.nonnormalization i hi hi2 hib
      ((map_le_map_iff_of_injective (MulAut.conj g⁻¹).injective).mp h)
  turns := by
    intro i hi hi2 hib
    obtain ⟨k, hk, ht⟩ := e.turns i hi hi2 hib
    refine ⟨g⁻¹ * k * g, ?_, ?_⟩
    · rw [actWalk_getVert, stabilizer_act]
      simpa only [MulAut.conj_apply, inv_inv, MulEquiv.toMonoidHom_eq_coe,
        MonoidHom.coe_coe] using mem_map_of_mem (MulAut.conj g⁻¹).toMonoidHom hk
    · rw [actWalk_getVert, actWalk_getVert, ← act_mul]
      simp only [← mul_assoc, mul_inv_cancel, one_mul, act_mul, ht]

theorem extended_of_regular_and_replacement (common : CommonFacts R source geometry)
    (hb : 4 ≤ geometry.b R)
    (replacement : ∀ {a a'} (p : CriticalPath R geometry a a'),
      HasTurnConjugators R p → PrescribedReplacement R p)
    {d d' : Vertex R} (p : CriticalPath R geometry d d') (hp : HasTurnConjugators R p)
    (a : Vertex R) (ha : color R a = false) : Nonempty (ExtendedPath geometry a) := by
  obtain ⟨w⟩ := exists_segment common hb replacement p hp 4
  let e := w.toExtended
  have hc : color R (w.walk.getVert 4) = false :=
    (walk_vertex_color w.start_color w.walk (by rw [w.length_eq]; omega)).mpr (by decide)
  obtain ⟨x, hx⟩ := exists_mVertex_of_color R hc
  obtain ⟨y, hy⟩ := exists_mVertex_of_color R ha
  have hact : act R (x⁻¹ * y) (w.walk.getVert 4) = a := by
    rw [hx, hy, act_mVertex]
    simp only [← mul_assoc, mul_inv_cancel, one_mul]
  exact hact ▸ ⟨extendedAct e (x⁻¹ * y)⟩

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.Source44.RegularPaths
