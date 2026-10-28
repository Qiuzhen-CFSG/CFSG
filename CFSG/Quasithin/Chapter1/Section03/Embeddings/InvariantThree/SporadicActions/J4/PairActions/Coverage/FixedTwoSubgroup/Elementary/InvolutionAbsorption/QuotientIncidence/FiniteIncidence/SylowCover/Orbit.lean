module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.J4.PairActions.Coverage.FixedTwoSubgroup.Elementary.InvolutionAbsorption.QuotientIncidence.FiniteIncidence.SylowCover.OrbitChecks

/-!
# Certified separation of the 10395 right cosets

The finite check validates distinct sorted pairs using a left inverse and
validates every edge using the four certified generator matrices. Every root is the image of a published representative; following edges multiplies on the right by subgroup generators.
The soundness lemmas in Core transfer these checks to actual group elements.
See source/README.md and source/generate.py for witness provenance.
-/

@[expose] public section
open Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData
open LowerBound LowerBound.QuotientOrderCertificate

namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions.J4Reduction.FiniteIncidence.SylowCover.Orbit
open CoverData
attribute [local irreducible] Janko4.modelGroup quotientSubgroup baseSubgroup

private theorem checked : ∀ i : Fin 10395,
    (codes i).1.toNat ≤ (codes i).2.toNat ∧
    index (key (codes i)) = i ∧
    (if parent i < i then Step (codes (parent i)) (codes i) (sylowRows (letter i))
      else codes i = rootCodes (root i)) := OrbitChecks.checked

theorem distinct : Function.Injective (fun i => point (codes i)) :=
  points_injective codes (fun i => (checked i).1)
    (Function.LeftInverse.injective (fun i => (checked i).2.1))

theorem reachable : ∀ i : Fin 10395, ∃ j b, b ∈ baseSubgroup ∧
    pairRight seed (representative j * b) = point (codes i) := by
  apply forest_reachable (fun i => point (codes i)) parent letter root
  · intro i hi
    have h := (checked i).2.2
    rw [if_neg hi] at h
    rw [h]
    exact representative_pair _
  · intro i hi
    have h := (checked i).2.2
    rw [if_pos hi] at h
    exact step_sound (codes (parent i)) (codes i) (sylowGenerator (letter i))
      (sylowRows (letter i)) (sylowGenerator_val _) h

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions.J4Reduction.FiniteIncidence.SylowCover.Orbit
