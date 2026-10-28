module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Propagation.Backward.Products.Selection.Pencil.Choices.Assembly
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Propagation.Backward.Products.Selection.Predecessor
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Propagation.Backward.Products.SelectionGeometry

/-!
# Source-corrected selection contracts

MS93 writes the generating group at an incident pair as the relative
normalizer `N_(G_a)(Q_t)`.  The old edge-stabilizer contracts remain exported
from the preceding modules for compatibility, while this file carries the
source-facing pencil, commutator and two-choice assembly.  The reverse-span
bound is supplied through `RelativeBoundFacts`; its producer is the corrected
form of (4.3.6).
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped Pointwise
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.Propagation.Backward.Products.Selection
open Choices
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M} {geometry : Geometry R}

theorem relativePencilFacts_of_two_lines (source : LocalSource L R)
    (p : Counterexample geometry) (hb : 2 < geometry.b R)
    (modules : ModuleFacts source geometry)
    (initial : ∀ q : Counterexample geometry, Nonempty (InitialFacts q))
    (control : ∀ q : Counterexample geometry, LocalControl q) (edge : EdgeTransfer geometry)
    (β : Vertex R) (hβ : Before p.a' p.a β 1)
    (htwo : ∃ t u, Adjacent R p.a t ∧ relativeGenerating p t ∧
      Adjacent R p.a u ∧ relativeGenerating p u ∧ edgeLine p β t ≠ edgeLine p β u) :
    RelativePencilFacts p β where
  fixed_plane := endpoint_fixed_plane source p hb modules initial control edge β hβ
  line_card := fun t ht hgen => edgeLine_card_of_relativeNormalizer source p hb modules
    initial control edge β t hβ ht hgen
  line_join := fun t ht hgen => edgeLine_join_critical_of_relativeNormalizer source p hb
    modules initial control edge β t hβ ht hgen
  two_lines := htwo

private theorem eq_of_le_order_two_relative {G : Type*} [Group G]
    (A B : Subgroup G) (hAB : A ≤ B) (hB : Nat.card B = 2) (hA : A ≠ ⊥) : A = B := by
  let : Finite B := Nat.finite_of_card_ne_zero (by rw [hB]; decide)
  let : Finite A := Finite.of_injective (inclusion hAB) (inclusion_injective _)
  have hcard : 1 < Nat.card A := (one_lt_card_iff_ne_bot A).mpr hA
  exact eq_of_le_of_card_ge hAB (by rw [hB]; omega)

/-- The commutator-to-line comparison with the source relative normalizer. -/
theorem relative_commutator_eq_edgeLine (source : LocalSource L R)
    (p : Counterexample geometry) (hb : 2 < geometry.b R)
    (modules : ModuleFacts source geometry)
    (control : ∀ q : Counterexample geometry, LocalControl q) (edge : EdgeTransfer geometry)
    (β : Vertex R) (hβ : Before p.a' p.a β 1) (pencil : RelativePencilFacts p β)
    (v t : Vertex R) (hvc : color R v = false)
    (hnear : (cosetGraph R).dist v p.a' < geometry.b R)
    (hat : Adjacent R p.a t) (hgen : relativeGenerating p t)
    (W : Subgroup (FreeAmalgam R)) (hlocal : W ≤ stabilizer R v)
    (hcomm : ⁅W, Z R v⁆ ≤ edgeDisplacement p.a t) (hbad : ¬ W ≤ Q R v) :
    ⁅W, Z R v⁆ = edgeLine p β t := by
  have hnatural := local_commutator_le_natural source v hvc W hlocal
  have hQ : Z R v ≤ Q R p.a' := by
    apply Z_le_Q_of_dist_lt R v (geometry.exists_critical v hvc)
    rw [geometry.distance_constant v hvc]
    exact hnear
  have hcentral : ⁅W, Z R v⁆ ≤ centralizer (Z R p.a' : Set (FreeAmalgam R)) :=
    ((hnatural.trans (U_le_Z v)).trans hQ).trans
      (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
        (geometry.centralizes p.a' p.end_color)))
  have hfixed : ⁅W, Z R v⁆ ≤ edgeDisplacement p.a β := by
    rw [← pencil.fixed_plane]
    exact le_inf (hcomm.trans (Initial.edge_le_natural source p.a t p.color_a hat)) hcentral
  have hline : ⁅W, Z R v⁆ ≤ edgeLine p β t :=
    le_inf hcomm (hfixed.trans (edge_le_Z p hb control edge p.a β p.color_a hβ.endpoint_adjacent))
  apply eq_of_le_order_two_relative _ _ hline (pencil.line_card t hat hgen)
  intro hzero
  apply hbad
  apply (le_Q_iff_commutator_le_center source modules v hvc W hlocal).mpr
  rw [hzero]
  exact bot_le

private theorem relative_failed_bound_line_eq_intersection (source : LocalSource L R)
    (p : Counterexample geometry) (hb : 2 < geometry.b R)
    (modules : ModuleFacts source geometry)
    (control : ∀ q : Counterexample geometry, LocalControl q) (edge : EdgeTransfer geometry)
    (rigidity : RigidityFacts geometry)
    (β d t : Vertex R) (hβ : Before p.a' p.a β 1) (pencil : RelativePencilFacts p β)
    (hd : Before p.a p.a' d 4) (hat : Adjacent R p.a t) (hgen : relativeGenerating p t)
    (hbad : ¬ backwardSpan geometry p.a t ≤ Q R d)
    (hcenter : criticalCommutator p.a p.a' ≤ localCenter d) :
    edgeLine p β t = edgeDisplacement p.a β ⊓ U R d := by
  have hdc : color R d = false := (hd.color (by decide)).trans p.end_color
  have hlocal := backwardSpan_le_before_stabilizer p d t hd
  have hcomm := relative_commutator_eq_edgeLine source p hb modules control edge β hβ pencil
    d t hdc (by rw [hd.1]; have := rigidity.six_lt p; omega) hat hgen _ hlocal
    (backwardSpan_commutator_le_edge source p (by have := rigidity.six_lt p; omega)
      control d t hd hat) hbad
  have hnatural : edgeLine p β t ≤ U R d := by
    rw [← hcomm]
    exact local_commutator_le_natural source d hdc _ hlocal
  rw [← pencil.line_join t hat hgen]
  exact (join_inf_natural_eq source modules d hdc _ _ hnatural hcenter).symm

private theorem relative_critical_le_center_of_failed_bound
    (relativeBound : RelativeBoundFacts geometry)
    (p : Counterexample geometry) (d t : Vertex R) (hd : Before p.a p.a' d 4)
    (hat : Adjacent R p.a t) (hgen : relativeGenerating p t)
    (hbad : ¬ backwardSpan geometry p.a t ≤ Q R d) :
    criticalCommutator p.a p.a' ≤ localCenter d := by
  by_contra hn
  have hnr : ¬ radiusCommutator p.a p.a' ≤ localCenter d := by
    intro hr
    exact hn ((p.critical_le_radius_inf_start.trans inf_le_left).trans hr)
  exact hbad ((relativeBound.bound p d hd hnr).2 t hat hgen)

private theorem relative_favorable_edge_of_pencil (source : LocalSource L R)
    (p : Counterexample geometry) (hb : 2 < geometry.b R)
    (modules : ModuleFacts source geometry)
    (control : ∀ q : Counterexample geometry, LocalControl q) (edge : EdgeTransfer geometry)
    (rigidity : RigidityFacts geometry)
    (relativeBound : RelativeBoundFacts geometry)
    (β d : Vertex R) (hβ : Before p.a' p.a β 1) (pencil : RelativePencilFacts p β)
    (hd : Before p.a p.a' d 4) :
    ∃ t, Adjacent R p.a t ∧ relativeGenerating p t ∧
      backwardSpan geometry p.a t ≤ Q R d := by
  classical
  by_contra hn
  have hbad (t : Vertex R) (ht : Adjacent R p.a t) (hgen : relativeGenerating p t) :
      ¬ backwardSpan geometry p.a t ≤ Q R d := fun h => hn ⟨t, ht, hgen, h⟩
  obtain ⟨t, u, ht, hgt, hu, hgu, hne⟩ := pencil.two_lines
  have hcenter_t := relative_critical_le_center_of_failed_bound relativeBound p d t hd ht hgt
    (hbad t ht hgt)
  have hline_t := relative_failed_bound_line_eq_intersection source p hb modules control edge rigidity
    β d t hβ pencil hd ht hgt (hbad t ht hgt) hcenter_t
  have hcenter_u := relative_critical_le_center_of_failed_bound relativeBound p d u hd hu hgu
    (hbad u hu hgu)
  have hline_u := relative_failed_bound_line_eq_intersection source p hb modules control edge rigidity
    β d u hβ pencil hd hu hgu (hbad u hu hgu) hcenter_u
  exact hne (hline_t.trans hline_u.symm)

private theorem relative_favorable_predecessor_line (source : LocalSource L R)
    (p : Counterexample geometry) (hb : 2 < geometry.b R)
    (modules : ModuleFacts source geometry)
    (control : ∀ q : Counterexample geometry, LocalControl q) (edge : EdgeTransfer geometry)
    (comparison : RelativePredecessorComparison geometry)
    (β d t : Vertex R) (hβ : Before p.a' p.a β 1) (pencil : RelativePencilFacts p β)
    (hd : Before p.a p.a' d 4) (hat : Adjacent R p.a t) (hgen : relativeGenerating p t)
    (hgood : backwardSpan geometry p.a t ≤ Q R d)
    (hbad : ¬ backwardSpan geometry p.a t ≤ Q R p.c) :
    ⁅backwardSpan geometry p.a t, Z R p.c⁆ = edgeLine p β t ∧
      edgeLine p β t ≤ U R p.c := by
  have hdc : color R d = false := (hd.color (by decide)).trans p.end_color
  have hdist : (cosetGraph R).dist d p.c = 2 :=
    before_dist (geometry := geometry) hd p.before (by decide)
  have hlocal := hgood.trans (Q_le_stabilizer_of_dist_two R d p.c hdc hdist)
  have heq := relative_commutator_eq_edgeLine source p hb modules control edge β hβ pencil
    p.c t p.before_color (by rw [p.before.1]; exact hb) hat hgen _ hlocal
    (comparison p d t hd hat hgen hgood) hbad
  refine ⟨heq, ?_⟩
  rw [← heq]
  exact local_commutator_le_natural source p.c p.before_color _ hlocal

private theorem relative_predecessor_edge_of_comparisons (source : LocalSource L R)
    (p : Counterexample geometry) (hb : 2 < geometry.b R)
    (modules : ModuleFacts source geometry) (initial : InitialFacts p)
    (control : ∀ q : Counterexample geometry, LocalControl q) (edge : EdgeTransfer geometry)
    (rigidity : RigidityFacts geometry) (relativeBound : RelativeBoundFacts geometry)
    (comparison : RelativePredecessorComparison geometry)
    (β d : Vertex R) (hβ : Before p.a' p.a β 1) (pencil : RelativePencilFacts p β)
    (hd : Before p.a p.a' d 4) :
    ∃ t, Adjacent R p.a t ∧ relativeGenerating p t ∧
      backwardSpan geometry p.a t ≤ Q R p.c := by
  classical
  by_contra hn
  have hbad (t : Vertex R) (ht : Adjacent R p.a t) (hgen : relativeGenerating p t) :
      ¬ backwardSpan geometry p.a t ≤ Q R p.c := fun h => hn ⟨t, ht, hgen, h⟩
  obtain ⟨t, ht, hgt, hgood⟩ := relative_favorable_edge_of_pencil source p hb modules control edge
    rigidity relativeBound β d hβ pencil hd
  obtain ⟨hNt, hnatural_t⟩ := relative_favorable_predecessor_line source p hb modules control edge
    comparison β d t hβ pencil hd ht hgt hgood (hbad t ht hgt)
  have hRc : criticalCommutator p.a p.a' ≤ localCenter p.c :=
    (p.critical_le_radius_inf_start.trans inf_le_left).trans
      (radius_le_before_center source p hb initial control edge)
  have hline_t : edgeDisplacement p.a β ⊓ U R p.c = edgeLine p β t := by
    rw [← pencil.line_join t ht hgt]
    exact join_inf_natural_eq source modules p.c p.before_color _ _ hnatural_t hRc
  obtain ⟨u, v, hu, hgu, hv, hgv, hne⟩ := pencil.two_lines
  have hdiff : ∃ u, Adjacent R p.a u ∧ relativeGenerating p u ∧
      edgeLine p β u ≠ edgeLine p β t := by
    by_cases h : edgeLine p β u = edgeLine p β t
    · exact ⟨v, hv, hgv, fun heq => hne (h.trans heq.symm)⟩
    · exact ⟨u, hu, hgu, h⟩
  obtain ⟨u, hu, hgu, hne⟩ := hdiff
  have hbad_ud : ¬ backwardSpan geometry p.a u ≤ Q R d := by
    intro hgood_u
    obtain ⟨_, hnatural_u⟩ := relative_favorable_predecessor_line source p hb modules control edge
      comparison β d u hβ pencil hd hu hgu hgood_u (hbad u hu hgu)
    have hline_u : edgeDisplacement p.a β ⊓ U R p.c = edgeLine p β u := by
      rw [← pencil.line_join u hu hgu]
      exact join_inf_natural_eq source modules p.c p.before_color _ _ hnatural_u hRc
    exact hne (hline_u.symm.trans hline_t)
  have hdc : color R d = false := (hd.color (by decide)).trans p.end_color
  have hRd := relative_critical_le_center_of_failed_bound relativeBound p d u hd hu hgu hbad_ud
  have hZc : Z R p.c ≤ V R d := by
    apply le_iSup_of_le p.c
    apply le_iSup_of_le (show (cosetGraph R).dist p.c d ≤ 2 from ?_)
    · exact le_rfl
    · rw [SimpleGraph.dist_comm, before_dist (geometry := geometry) hd p.before (by decide)]
  have hNcentral : edgeLine p β t ≤ localCenter d := by
    rw [← hNt]
    apply (commutator_mono hgood hZc).trans
    rw [commutator_comm]
    exact radius_kernel_commutator_le_center source p hb control edge d hdc
  have hplane : edgeDisplacement p.a β ≤ localCenter d := by
    rw [← pencil.line_join t ht hgt]
    exact sup_le hNcentral hRd
  have hlocal := backwardSpan_le_before_stabilizer p d u hd
  have hNu := relative_commutator_eq_edgeLine source p hb modules control edge β hβ pencil d u hdc
    (by rw [hd.1]; have := rigidity.six_lt p; omega) hu hgu _ hlocal
    (backwardSpan_commutator_le_edge source p (by have := rigidity.six_lt p; omega)
      control d u hd hu) hbad_ud
  apply backwardSpan_commutator_not_le_center source modules p d u hd hbad_ud
  rw [hNu]
  exact (le_sup_left.trans (pencil.line_join u hu hgu).le).trans hplane

/-- The completed predecessor comparison under the corrected source premise.
The generating equality is unused by the stronger locality theorem, but is
retained in the public contract to match the source's implication. -/
theorem relativePredecessorComparison (source : LocalSource L R)
    (control : ∀ p : Counterexample geometry, LocalControl p)
    (rigidity : RigidityFacts geometry) : RelativePredecessorComparison geometry := by
  intro p d t hd hat _hgen hgood
  have hdc : color R d = false := (hd.color (by decide)).trans p.end_color
  have hdist : (cosetGraph R).dist d p.c = 2 :=
    before_dist (geometry := geometry) hd p.before (by decide)
  exact backwardSpan_predecessor_commutator_le_edge source p
    (by have := rigidity.six_lt p; omega) control t hat
    (hgood.trans (Q_le_stabilizer_of_dist_two R d p.c hdc hdist))

/-- Source-corrected version of the two edge choices.  Its generating
premises use the literal relative normalizer from MS93 p.881. -/
theorem relative_edge_choices_of_local_comparisons (source : LocalSource L R)
    (hb : 2 < geometry.b R) (modules : ModuleFacts source geometry)
    (initial : ∀ p : Counterexample geometry, Nonempty (InitialFacts p))
    (control : ∀ p : Counterexample geometry, LocalControl p) (edge : EdgeTransfer geometry)
    (rigidity : RigidityFacts geometry) (relativeBound : RelativeBoundFacts geometry)
    (comparison : RelativePredecessorComparison geometry) :
    (∀ p : Counterexample geometry, ∀ d, Before p.a p.a' d 4 →
      ∃ t, Adjacent R p.a t ∧ relativeGenerating p t ∧
        backwardSpan geometry p.a t ≤ Q R d) ∧
    (∀ p : Counterexample geometry, ∃ t, Adjacent R p.a t ∧ relativeGenerating p t ∧
      backwardSpan geometry p.a t ≤ Q R p.c) := by
  have hpencil (p : Counterexample geometry) :
      ∃ β, Before p.a' p.a β 1 ∧ RelativePencilFacts p β := by
    obtain ⟨β, hβ, hdist⟩ := exists_adjacent_dist_sub_one R p.a p.a'
      (p.distance_eq_b.symm ▸ (show 0 < geometry.b R by omega))
    have hpath : Before p.a' p.a β 1 := by
      constructor
      · rw [SimpleGraph.dist_comm]
        exact SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj R _ _).mpr hβ)
      · simpa only [SimpleGraph.dist_comm] using hdist
    exact ⟨β, hpath, relativePencilFacts_of_two_lines source p hb modules initial control edge β hpath
      (exists_distinct_generating_relativeNormalizer_lines source p hb modules initial control edge β hpath)⟩
  constructor
  · intro p d hd
    obtain ⟨β, hβ, pencil⟩ := hpencil p
    exact relative_favorable_edge_of_pencil source p hb modules control edge rigidity relativeBound β d hβ pencil hd
  · intro p
    obtain ⟨β, hβ, pencil⟩ := hpencil p
    obtain ⟨d, hd⟩ := p.exists_before (show 4 ≤ geometry.b R by have := rigidity.six_lt p; omega)
    obtain ⟨hi⟩ := initial p
    exact relative_predecessor_edge_of_comparisons source p hb modules hi control edge rigidity relativeBound
      comparison β d hβ pencil hd

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.Propagation.Backward.Products.Selection
