module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.Centralizers.Counting.UniformCases.Numerics.Inputs
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.Centralizers.Counting.UniformCases.Numerics.LocalGeometry
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.Centralizers.Counting.UniformCases.Numerics.Fibers
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.Centralizers.Counting.UniformCases.Numerics.Thompson
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.Centralizers.Counting.UniformCases.Numerics.Sizes

/-!
# Pointwise centralizer numerics from local geometry and mixed fibers

The proved half-order support gives Thompson's two-term order formula without
assuming that the ambient group has only two involution classes. The full
centralizer index and the local field-action square convert the two actual
fiber counts into the centralizing and moving coset-degree formulas. All
cancellations take place in the natural numbers; in particular the moving
formula retains the source's integrality assertion.

The local orbit/model calculation and the two fiber cardinalities remain
explicit inputs to this assembly. They must be constructed before asserting
unconditional `ResidualCentralizerNumerics`. Neither centralizer collapse nor
centralization of the actor is assumed. The same local exponent is retained
in the actual model and the ambient degree.

Source: GLS4, Chapter 2, Lemma 12.8, `refs/KGroup/GLS4/Chapter2.tex`.
-/

noncomputable section
namespace BenderSuzuki.ZD
open Subgroup Theory.GroupTheory.TwoInvolutionClassOrder
variable {G : Type*} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}

/-- Evaluate both Thompson degree formulas from the local geometric witness
and the actual mixed-fiber cardinalities. This is the assembly step; the two
input producers are independent remaining earlier-source obligations. -/
public theorem proper_residualGenerated_numericalWitness_of_geometry_and_fibers
    (h : MinimalCounterexample Z M) (r : SimpleReduction Z M)
    (ha : ResidualAction Z M) {z t v : G}
    (hz : z ∈ Z) (hzM : z ∈ M) (ht : t ∈ Z) (htM : t ∉ M)
    (hL : residualGenerated M z t ≠ ⊤)
    (heven : Even (Nat.card (residualPairStabilizer M t)))
    (hlocal : ResidualCentralizerLocalData Z M z t)
    (hvD : v ∈ residualPairStabilizer M t) (hv : PFAppendixIII.IsInvolution v)
    {k i : ℕ} (d : ResidualCentralizerPointGeometry Z M z t v k i)
    (hfibers : ResidualCentralizerFiberCounts Z M z v) :
    ResidualCentralizerNumericalWitness Z M z t v k i := by
  let q := 2 ^ k
  let f := q ^ i + 1
  have horder := proper_residualGenerated_thompson_order
    h r ha hz hzM ht htM hL heven hlocal hvD hv
  have hindex := proper_residualGenerated_distinguished_centralizer_card
    h r ha hz hzM ht htM hL heven
  have hactor : kappa z v v = (q - 1) * f * (q ^ i * (q - 1) + 1) := by
    simpa only [d.fixed_distinguished, d.fixed_cosets, Nat.add_sub_cancel, q, f]
      using hfibers.at_actor
  have hquot := M.card_eq_card_quotient_mul_card_subgroup
  refine ⟨d.exponent_ge, d.kind, d.suzuki_odd, d.fixed_distinguished, d.fixed_cosets,
    ?_, ?_, d.central_model⟩
  · intro hc
    have hA : Nat.card (closure (Z ∩ (M : Set G))) = q := by
      simpa only [ResidualNumerics.fixed_distinguished_eq hc] using d.fixed_distinguished
    have hzero := proper_residualGenerated_central_kappa_zero
      h r ha hz hzM ht htM hL heven hlocal hvD hv hc
    rw [hA] at hindex
    apply Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α := M))
    calc
      Nat.card (G ⧸ M) * Nat.card M = Nat.card G := hquot.symm
      _ = kappa z v v * Nat.card (centralizer ({z} : Set G)) := by
        simpa only [hzero, zero_mul, zero_add] using horder
      _ = (f * (q ^ i * (q - 1) + 1)) * Nat.card M := by
        rw [hactor, hindex]
        ring
  · intro hc
    have hA := proper_residualGenerated_moving_distinguished_card
      h r ha hz hzM ht htM hL heven hlocal hvD hv d.fixed_distinguished hc
    refine ⟨hA, ?_⟩
    have hdistinguished :
        (q + 1) * kappa z v z * Nat.card (centralizer ({v} : Set G)) = Nat.card M * f * q := by
      simpa only [d.fixed_distinguished, d.fixed_cosets, q, f] using hfibers.at_distinguished hc
    have hqpos : q ≠ 0 := by dsimp [q]; positivity
    have hfactor : q ^ 2 - 1 = (q + 1) * (q - 1) := by
      obtain ⟨s, hs⟩ := Nat.exists_eq_succ_of_ne_zero hqpos
      rw [hs]
      simp only [Nat.succ_eq_add_one, Nat.add_sub_cancel]
      rw [show (s + 1) ^ 2 = s * (s + 2) + 1 by ring, Nat.add_sub_cancel]
      ring
    rw [hA, hfactor] at hindex
    apply Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α := M))
    calc
      ((q + 1) * Nat.card (G ⧸ M)) * Nat.card M = (q + 1) * Nat.card G := by
        rw [mul_assoc, ← hquot]
      _ = (q + 1) * kappa z v z * Nat.card (centralizer ({v} : Set G)) +
          (q + 1) * kappa z v v * Nat.card (centralizer ({z} : Set G)) := by
        rw [horder]
        ring
      _ = Nat.card M * f * q + Nat.card M * f * (q ^ i * (q - 1) + 1) := by
        rw [hdistinguished, hactor]
        congr 1
        rw [hindex]
        ring
      _ = (f * (q ^ i * (q - 1) + q + 1)) * Nat.card M := by ring

/-- Assemble pointwise numerics once both earlier-source producers have been
supplied. Their existence is not asserted by this conditional theorem. -/
public theorem proper_residualGenerated_numerics_of_geometry_and_fibers
    (h : MinimalCounterexample Z M) (r : SimpleReduction Z M)
    (ha : ResidualAction Z M) {z t : G}
    (hz : z ∈ Z) (hzM : z ∈ M) (ht : t ∈ Z) (htM : t ∉ M)
    (hL : residualGenerated M z t ≠ ⊤)
    (heven : Even (Nat.card (residualPairStabilizer M t)))
    (hlocal : ResidualCentralizerLocalData Z M z t)
    (hgeometry : ∀ v ∈ residualPairStabilizer M t, PFAppendixIII.IsInvolution v →
      ∃ k i, ResidualCentralizerPointGeometry Z M z t v k i)
    (hfibers : ∀ v ∈ residualPairStabilizer M t, PFAppendixIII.IsInvolution v →
      ResidualCentralizerFiberCounts Z M z v) :
    ResidualCentralizerNumerics Z M z t := by
  intro v hvD hv
  obtain ⟨k, i, d⟩ := hgeometry v hvD hv
  exact ⟨k, i, proper_residualGenerated_numericalWitness_of_geometry_and_fibers
    h r ha hz hzM ht htM hL heven hlocal hvD hv d (hfibers v hvD hv)⟩

/-- The pointwise numerical input of GLS4, Chapter 2, Lemma 12.8.

The local fixed-coset/model calculation and the two mixed-fiber counts are
independent source branches.  This theorem discharges both from the same
`ResidualCentralizerLocalData`, retaining the literal quotient action and
centralizer conventions in `ResidualCentralizerNumerics`.
-/
public theorem proper_residualGenerated_numerics_of_local
    (h : MinimalCounterexample Z M) (r : SimpleReduction Z M)
    (ha : ResidualAction Z M) {z t : G}
    (hz : z ∈ Z) (hzM : z ∈ M) (ht : t ∈ Z) (htM : t ∉ M)
    (hL : residualGenerated M z t ≠ ⊤)
    (heven : Even (Nat.card (residualPairStabilizer M t)))
    (hlocal : ResidualCentralizerLocalData Z M z t) :
    ResidualCentralizerNumerics Z M z t := by
  exact proper_residualGenerated_numerics_of_geometry_and_fibers
    h r ha hz hzM ht htM hL heven hlocal
    (proper_residualGenerated_point_geometry_of_local
      h r ha hz hzM ht htM hL heven hlocal)
    (proper_residualGenerated_fiber_counts_of_local
      h r ha hz hzM ht htM hL heven hlocal)

end BenderSuzuki.ZD
