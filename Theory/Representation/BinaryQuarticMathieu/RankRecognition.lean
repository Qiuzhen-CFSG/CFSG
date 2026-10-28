module

public import Theory.Representation.BinaryQuarticMathieu.Basic
public import Theory.Representation.BinaryQuarticMathieu.RankRecognition.Reduction
public import Theory.Representation.BinaryQuarticMathieu.RankRecognition.Orbits
public import Theory.Representation.BinaryQuarticMathieu.RankRecognition.Representatives

/-!
# Intrinsic recognition and complete contraction-rank classification

For the determinant-sum quartic on ten binary coordinates, the contraction
histograms have the following multiplicities. Every unlisted rank has count zero.

| Number of vectors | rank 0 | rank 2 | rank 4 | rank 6 | rank 8 |
| ---: | ---: | ---: | ---: | ---: | ---: |
| 1 (the zero vector) | 1024 | 0 | 0 | 0 | 0 |
| 22 | 2 | 0 | 42 | 420 | 560 |
| 231 | 2 | 30 | 32 | 960 | 0 |
| 770 | 2 | 0 | 18 | 540 | 464 |

The class of size 22 is exactly the marked point configuration from `Basic`.
The representative calculations concern the image dimension of the genuine
contraction into the dual. The certified preserving linear equivalences carry
each vector from its representative, so invariance supplies every histogram.
The checked enumeration supplies exhaustiveness and the displayed multiplicities.

This completes the finite rank calculation described in the source repository's
`Scratch/J4FleetGuidance/SeedCentralizer/README.md`, under "Image bound from22
intrinsic points". The local `source/generate_orbits.py` and
`source/orbit-witnesses.json` provide only witnesses for the kernel-checked
certificates in the imported modules. No group identification is needed.
-/

public section

namespace BinaryQuarticMathieu

open RankRecognition

attribute [local irreducible] quartic

namespace RankRecognition

/-- The complete wordwise histogram, obtained from genuine preserving transports
and genuine representative contraction ranks. -/
theorem word_distributions (n : Word) :
    rankDistribution quartic (decode n) = profile (wordClass n) :=
  word_distributions_of_transports representative_histograms orbit_transport n

/-- Every vector has exactly one of the four displayed histograms. -/
theorem distributions_exhaustive (v : U) :
    ∃! c : Fin 4, rankDistribution quartic v = profile c := by
  obtain ⟨c, hc⟩ := distributions_exhaustive_of_words word_distributions v
  exact ⟨c, hc, fun d hd => profile_injective (hd.symm.trans hc)⟩

/-- The four histogram classes have sizes 1, 770, 231 and 22, respectively. -/
theorem distribution_card (c : Fin 4) :
    Nat.card {v : U // rankDistribution quartic v = profile c} = classSize c :=
  distribution_card_of_words word_distributions c

/-- Only the zero vector has all 1024 contractions of rank zero. -/
theorem zero_distribution_iff (v : U) :
    rankDistribution quartic v = zeroDistribution ↔ v = 0 :=
  zero_distribution_iff_of_words word_distributions v

private theorem nonzero_of_distribution {v : U} {c : Fin 4} (hc : c ≠ 0)
    (hv : rankDistribution quartic v = profile c) : v ≠ 0 := by
  intro hz
  have hzero : rankDistribution quartic v = profile 0 :=
    (zero_distribution_iff v).mpr hz
  exact hc (profile_injective (hv.symm.trans hzero))

/-- The three nonzero histogram classes have their stated sizes even when
nonzeroness is included explicitly in the counted predicate. -/
theorem nonzero_distribution_card (c : Fin 4) (hc : c ≠ 0) :
    Nat.card {v : U // v ≠ 0 ∧ rankDistribution quartic v = profile c} =
      classSize c := by
  calc
    Nat.card {v : U // v ≠ 0 ∧ rankDistribution quartic v = profile c} =
        Nat.card {v : U // rankDistribution quartic v = profile c} :=
      Nat.card_congr (Equiv.subtypeEquivRight (fun _ =>
        ⟨And.right, fun h => ⟨nonzero_of_distribution hc h, h⟩⟩))
    _ = classSize c := distribution_card c

end RankRecognition

/-- The specified histogram intrinsically recognizes precisely the 22 marked
points, with no auxiliary recognition or group-theoretic hypothesis. -/
theorem rankDistribution_recognition : ∀ v : U,
    rankDistribution quartic v = pointDistribution ↔ v ∈ Set.range point :=
  recognition_of_words word_distributions

/-- Each marked point has the stated histogram on all natural ranks. -/
theorem rankDistribution_point (i : Fin 22) :
    rankDistribution quartic (point i) = pointDistribution :=
  (rankDistribution_recognition (point i)).mpr ⟨i, rfl⟩

/-- Complete classification: zero has its unique histogram, and each nonzero
vector has one of the three displayed nonzero histograms. The equalities are
of functions on all natural ranks, so also specify every omitted entry. -/
theorem rankDistribution_classification (v : U) :
    (v = 0 ∧ rankDistribution quartic v = zeroDistribution) ∨
      (v ≠ 0 ∧ (rankDistribution quartic v = pointDistribution ∨
        rankDistribution quartic v = pairDistribution ∨
        rankDistribution quartic v = largeDistribution)) := by
  by_cases hv : v = 0
  · exact Or.inl ⟨hv, (zero_distribution_iff v).mpr hv⟩
  · refine Or.inr ⟨hv, ?_⟩
    obtain ⟨c, hc, _⟩ := distributions_exhaustive v
    fin_cases c
    · exact False.elim (hv ((zero_distribution_iff v).mp hc))
    · exact Or.inr (Or.inr hc)
    · exact Or.inr (Or.inl hc)
    · exact Or.inl hc

/-- Exactly one vector has the histogram `(0 : 1024)`. -/
theorem rankDistribution_zero_card :
    Nat.card {v : U // rankDistribution quartic v = zeroDistribution} = 1 :=
  distribution_card 0

/-- Exactly 22 nonzero vectors have histogram `(0 : 2, 4 : 42, 6 : 420, 8 : 560)`.
All other ranks have count zero. -/
theorem rankDistribution_point_card :
    Nat.card {v : U // v ≠ 0 ∧ rankDistribution quartic v = pointDistribution} = 22 :=
  nonzero_distribution_card 3 (by decide)

/-- Exactly 231 nonzero vectors have histogram `(0 : 2, 2 : 30, 4 : 32, 6 : 960)`.
All other ranks have count zero. -/
theorem rankDistribution_pair_card :
    Nat.card {v : U // v ≠ 0 ∧ rankDistribution quartic v = pairDistribution} = 231 :=
  nonzero_distribution_card 2 (by decide)

/-- Exactly 770 nonzero vectors have histogram `(0 : 2, 4 : 18, 6 : 540, 8 : 464)`.
All other ranks have count zero. -/
theorem rankDistribution_large_card :
    Nat.card {v : U // v ≠ 0 ∧ rankDistribution quartic v = largeDistribution} = 770 :=
  nonzero_distribution_card 1 (by decide)

end BinaryQuarticMathieu
