module

public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.SylowOvergroups.Alternating.ProperComponents.PrimitiveRecognition.Inputs

/-!
# Local permutation inputs for the large-degree exclusion

A four-point Klein group and the even products of disjoint transpositions
can be placed simultaneously in a Sylow two-subgroup. In a group without
three-cycles, each translate of the Klein group's four-point set meets a
double-transposition support evenly. These two independent facts reduce
the primitive large-degree exclusion to counting intersections with pairs.

The propositions below specify these local inputs; they do not assert
that either input has been proved, or assume the desired degree bound.
Source: the alternating-overgroup step of Aschbacher–Smith B.1.13,
printed p.74 (PDF p.85).
-/

public section
open Equiv MulAction
namespace CFSG.Quasithin.ChapterB.ComponentRecognition.SylowOvergroups.LargeDegree

/-- All three double transpositions on the indicated four-set belong to `G`.
The cardinality of the set is supplied separately by consumers. -/
@[expose] def KleinFourOn {α : Type*} [DecidableEq α]
    (G : Subgroup (Perm α)) (B : Finset α) : Prop :=
  ∀ a b c d : α, [a, b, c, d].Nodup → B = {a, b, c, d} →
    swap a b * swap c d ∈ G

/-- A pairing whose even products of two pair transpositions lie in `G`. -/
structure PairedFrame {α : Type*} [DecidableEq α]
    (G : Subgroup (Perm α)) (k : ℕ) where
  point : (Fin k × Fin 2) ↪ α
  pair_mem : ∀ i j : Fin k, i ≠ j →
    swap (point (i, 0)) (point (i, 1)) *
      swap (point (j, 0)) (point (j, 1)) ∈ G

/-- The elementary local permutation calculation needed by the counting proof.
An odd intersection produces a three-cycle using the double transposition
and the four-point Klein group. The translate is the literal permutation
image, so the downstream primitive-action argument needs no convention bridge. -/
@[expose] def KleinFourOverlapEven : Prop :=
  ∀ (m : ℕ) (G : Subgroup (Perm (Fin m))),
    (∀ g : G, ¬ g.val.IsThreeCycle) →
    ∀ (B : Finset (Fin m)), B.card = 4 → KleinFourOn G B →
    ∀ (g : G) (a b c d : Fin m), [a, b, c, d].Nodup →
      swap a b * swap c d ∈ G →
      Even (((B.image g.val) ∩ {a, b, c, d}).card)

/-- Simultaneous Sylow placement of a pairing and a four-point Klein group.
Only four and five pairs are requested. No primitive-action or component
hypothesis occurs in this finite two-subgroup construction. -/
@[expose] def SylowPairedFrames : Prop :=
  ∀ (m k : ℕ), (k = 4 ∨ k = 5) → 2 * k ≤ m →
    ∀ (S : Sylow 2 (alternatingGroup (Fin m)))
      (X : Subgroup (alternatingGroup (Fin m))), (S : Subgroup _) ≤ X →
      ∃ (_F : PairedFrame (X.map (alternatingGroup (Fin m)).subtype) k)
        (B : Finset (Fin m)), B.card = 4 ∧
          KleinFourOn (X.map (alternatingGroup (Fin m)).subtype) B

end CFSG.Quasithin.ChapterB.ComponentRecognition.SylowOvergroups.LargeDegree
