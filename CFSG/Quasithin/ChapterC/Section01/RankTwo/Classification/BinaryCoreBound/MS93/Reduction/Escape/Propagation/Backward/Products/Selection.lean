module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Propagation.Backward.Products.Selection.Pencil
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Propagation.Backward.Products.Selection.Assembly
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Propagation.Backward.Products.Selection.SourceRelative
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Propagation.Backward.Bound.RelativeNormalizer

/-!
# The two backward-span edge choices in MS93 (4.3.7)(i)

The source generating group is the relative normalizer `G_a ∩ N(Q_t)`,
as defined on printed p.881. `SourceRelative` proves both changing-edge
arguments using the actual natural fixed plane and distinct intersection
lines, including the central-commutator contradiction on p.888.

This module discharges the corrected (4.3.6) bound and the predecessor
comparison from the preceding stages. Thus `relative_edge_choices` gives
both favorable neighbors with no additional choice, pencil, or comparison
premise. The old edge-stabilizer conditional assembly remains unchanged.
Normalization under the relative normalizer and the final product assertions
belong to the parent Products development.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), (4.3.7)(i), printed pp.887--888.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.Propagation.Backward.Products.Selection
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M} {geometry : Geometry R}

/-- Conditional final assembly of both choices. The two local premises
contain neither favorable-span witnesses nor product-normality conclusions. -/
theorem edge_choices_of_local_comparisons (source : LocalSource L R)
    (hb : 2 < geometry.b R) (modules : ModuleFacts source geometry)
    (initial : ∀ p : Counterexample geometry, Nonempty (InitialFacts p))
    (control : ∀ p : Counterexample geometry, LocalControl p) (edge : EdgeTransfer geometry)
    (rigidity : RigidityFacts geometry) (bound : BoundFacts geometry)
    (choices : ∀ p : Counterexample geometry, ∀ β, Before p.a' p.a β 1 →
      ∃ t u, Adjacent R p.a t ∧
        (stabilizer R p.a ⊓ stabilizer R t) ⊔ Z R p.a' = stabilizer R p.a ∧
        Adjacent R p.a u ∧
        (stabilizer R p.a ⊓ stabilizer R u) ⊔ Z R p.a' = stabilizer R p.a ∧
        edgeLine p β t ≠ edgeLine p β u)
    (comparison : PredecessorComparison geometry) :
    (∀ p : Counterexample geometry, ∀ d, Before p.a p.a' d 4 →
      ∃ t, Adjacent R p.a t ∧
        (stabilizer R p.a ⊓ stabilizer R t) ⊔ Z R p.a' = stabilizer R p.a ∧
        backwardSpan geometry p.a t ≤ Q R d) ∧
    (∀ p : Counterexample geometry, ∃ t, Adjacent R p.a t ∧
      (stabilizer R p.a ⊓ stabilizer R t) ⊔ Z R p.a' = stabilizer R p.a ∧
      backwardSpan geometry p.a t ≤ Q R p.c) := by
  have hpencil (p : Counterexample geometry) :
      ∃ β, Before p.a' p.a β 1 ∧ PencilFacts p β := by
    obtain ⟨β, hβ, hdist⟩ := exists_adjacent_dist_sub_one R p.a p.a'
      (p.distance_eq_b.symm ▸ (show 0 < geometry.b R by omega))
    have hpath : Before p.a' p.a β 1 := by
      constructor
      · rw [SimpleGraph.dist_comm]
        exact SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj R _ _).mpr hβ)
      · simpa only [SimpleGraph.dist_comm] using hdist
    exact ⟨β, hpath, pencilFacts_of_two_lines source p hb modules initial control edge β hpath
      (choices p β hpath)⟩
  constructor
  · intro p d hd
    obtain ⟨β, hβ, pencil⟩ := hpencil p
    exact favorable_edge_of_pencil source p hb modules control edge rigidity bound β d hβ pencil hd
  · intro p
    obtain ⟨β, hβ, pencil⟩ := hpencil p
    obtain ⟨d, hd⟩ := p.exists_before (show 4 ≤ geometry.b R by have := rigidity.six_lt p; omega)
    obtain ⟨hi⟩ := initial p
    exact predecessor_edge_of_comparisons source p hb modules hi control edge rigidity bound
      comparison β d hβ pencil hd

/-- Both source edge choices in (4.3.7)(i), with the generating relative
normalizer written literally. The corrected reverse-span bound, distinct
lines, and predecessor comparison are all supplied by their proved producers. -/
theorem relative_edge_choices (source : LocalSource L R)
    (hb : 2 < geometry.b R) (modules : ModuleFacts source geometry)
    (initial : ∀ p : Counterexample geometry, Nonempty (InitialFacts p))
    (control : ∀ p : Counterexample geometry, LocalControl p) (edge : EdgeTransfer geometry)
    (rigidity : RigidityFacts geometry) :
    (∀ p : Counterexample geometry, ∀ d, Before p.a p.a' d 4 →
      ∃ t, Adjacent R p.a t ∧
        (stabilizer R p.a ⊓ normalizer (Q R t : Set (FreeAmalgam R))) ⊔ Z R p.a' =
          stabilizer R p.a ∧
        backwardSpan geometry p.a t ≤ Q R d) ∧
    (∀ p : Counterexample geometry, ∃ t, Adjacent R p.a t ∧
      (stabilizer R p.a ⊓ normalizer (Q R t : Set (FreeAmalgam R))) ⊔ Z R p.a' =
        stabilizer R p.a ∧
      backwardSpan geometry p.a t ≤ Q R p.c) := by
  exact relative_edge_choices_of_local_comparisons source hb modules initial control edge rigidity
    (relativeBoundFacts source hb modules initial control edge rigidity)
    (relativePredecessorComparison source control rigidity)

/-- The favorable choice (*) on p.887, at any vertex four before the endpoint. -/
theorem favorable_edge_of_relativeNormalizer (source : LocalSource L R)
    (p : Counterexample geometry) (hb : 2 < geometry.b R)
    (modules : ModuleFacts source geometry)
    (initial : ∀ q : Counterexample geometry, Nonempty (InitialFacts q))
    (control : ∀ q : Counterexample geometry, LocalControl q) (edge : EdgeTransfer geometry)
    (rigidity : RigidityFacts geometry) (d : Vertex R) (hd : Before p.a p.a' d 4) :
    ∃ t, Adjacent R p.a t ∧
      (stabilizer R p.a ⊓ normalizer (Q R t : Set (FreeAmalgam R))) ⊔ Z R p.a' =
        stabilizer R p.a ∧
      backwardSpan geometry p.a t ≤ Q R d := by
  exact (relative_edge_choices source hb modules initial control edge rigidity).1 p d hd

/-- The choice on p.888 whose reverse-moving span lies in the predecessor kernel. -/
theorem predecessor_edge_of_relativeNormalizer (source : LocalSource L R)
    (p : Counterexample geometry) (hb : 2 < geometry.b R)
    (modules : ModuleFacts source geometry)
    (initial : ∀ q : Counterexample geometry, Nonempty (InitialFacts q))
    (control : ∀ q : Counterexample geometry, LocalControl q) (edge : EdgeTransfer geometry)
    (rigidity : RigidityFacts geometry) :
    ∃ t, Adjacent R p.a t ∧
      (stabilizer R p.a ⊓ normalizer (Q R t : Set (FreeAmalgam R))) ⊔ Z R p.a' =
        stabilizer R p.a ∧
      backwardSpan geometry p.a t ≤ Q R p.c := by
  exact (relative_edge_choices source hb modules initial control edge rigidity).2 p

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.Propagation.Backward.Products.Selection
