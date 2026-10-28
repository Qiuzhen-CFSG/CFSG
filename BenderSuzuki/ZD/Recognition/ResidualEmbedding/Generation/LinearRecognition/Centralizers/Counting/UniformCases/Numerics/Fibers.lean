module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.Centralizers.Counting.UniformCases.Numerics.Fibers.Correspondence
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.Centralizers.Counting.UniformCases.Numerics.Fibers.Displacement
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.Centralizers.Counting.UniformCases.Numerics.Fibers.DisplacementCount
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.Centralizers.Counting.UniformCases.Numerics.Fibers.FixedCoset
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.Centralizers.Counting.UniformCases.Numerics.Fibers.OddIncidence

/-!
# The two actual fiber counts from local centralizer data

The dihedral correspondence counts the actor fiber by odd-product pairs in
its distinguished centralizer closure. The distinguished fiber is counted
by elementary-group displacement pairs. The fixed-point ratio replaces the
ambient actor class inside M by the literal fixed-coset cardinality times
|M| divided by the actor centralizer order, using a multiplied identity.

Fixed-coset incidence counts the odd-product pairs, including equal factors.
Fusion in M and the moving square |A| = q² count the displacement pairs.
The final theorem discharges both cardinalities from the local centralizer
data, retaining the literal fixed-coset size without choosing a model exponent.
Source: GLS4, Chapter 2, proof of Lemma 12.8, `refs/KGroup/GLS4/Chapter2.tex`.
-/

namespace BenderSuzuki.ZD
open Subgroup Theory.GroupTheory.TwoInvolutionClassOrder
variable {G : Type*} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}

/-- The two independent local pair counts supply the literal Thompson counts.
The assembly owner must discharge both cardinality premises. -/
public theorem proper_residualGenerated_fiber_counts_of_pair_counts
    (h : MinimalCounterexample Z M) (r : SimpleReduction Z M)
    (ha : ResidualAction Z M) {z t v : G}
    (hz : z ∈ Z) (hzM : z ∈ M) (ht : t ∈ Z) (htM : t ∉ M)
    (hL : residualGenerated M z t ≠ ⊤)
    (heven : Even (Nat.card (residualPairStabilizer M t)))
    (hlocal : ResidualCentralizerLocalData Z M z t)
    (hvD : v ∈ residualPairStabilizer M t) (hv : PFAppendixIII.IsInvolution v)
    (hodd :
      let q := Nat.card (closure (Z ∩ (M : Set G)) ⊓ centralizer ({v} : Set G) : Subgroup G)
      let f := Nat.card {beta : G ⧸ M // v • beta = beta}
      Nat.card (ResidualCentralizerOddPairs Z v) =
        (q - 1) * f * ((f - 1) * (q - 1) + 1))
    (hdisplacement : v ∉ centralizer (closure (Z ∩ (M : Set G)) : Set G) →
      let q := Nat.card (closure (Z ∩ (M : Set G)) ⊓ centralizer ({v} : Set G) : Subgroup G)
      (q + 1) * Nat.card (ResidualDistinguishedDisplacementPairs Z M z v) =
        Nat.card {b : M // IsConj v (b : G)} * q) :
    ResidualCentralizerFiberCounts Z M z v := by
  constructor
  · rw [proper_residualGenerated_kappa_actor_eq_local_odd_pairs
      h r ha hz hzM ht htM hL heven hlocal hvD hv]
    exact hodd
  · intro hc
    dsimp only
    rw [proper_residualGenerated_kappa_distinguished_eq_displacement_pairs
      h r ha hz hzM ht htM hL heven hvD hv]
    rw [hdisplacement hc]
    calc
      _ = (Nat.card {b : M // IsConj v (b : G)} * Nat.card (centralizer ({v} : Set G))) *
          Nat.card (closure (Z ∩ (M : Set G)) ⊓ centralizer ({v} : Set G) : Subgroup G) := by
        ac_rfl
      _ = _ := by rw [residual_conjugates_card_mul_centralizer v]

/-- The actual mixed-involution fiber counts in GLS4, Chapter 2, Lemma 12.8,
for every involution in the two-point stabilizer. Both local pair-cardinality
premises are discharged. The distinguished element `z` need not commute with
the actor, and no fixed-coset degree or centralizer collapse is assumed. -/
public theorem proper_residualGenerated_fiber_counts_of_local
    (h : MinimalCounterexample Z M) (r : SimpleReduction Z M)
    (ha : ResidualAction Z M) {z t : G}
    (hz : z ∈ Z) (hzM : z ∈ M) (ht : t ∈ Z) (htM : t ∉ M)
    (hL : residualGenerated M z t ≠ ⊤)
    (heven : Even (Nat.card (residualPairStabilizer M t)))
    (hlocal : ResidualCentralizerLocalData Z M z t) :
    ∀ v ∈ residualPairStabilizer M t, PFAppendixIII.IsInvolution v →
      ResidualCentralizerFiberCounts Z M z v := by
  intro v hvD hv
  exact proper_residualGenerated_fiber_counts_of_pair_counts
    h r ha hz hzM ht htM hL heven hlocal hvD hv
    (proper_residualGenerated_local_odd_pairs_card
      h r ha hz hzM ht htM hL heven hlocal hvD hv)
    (proper_residualGenerated_displacement_pairs_card
      h r ha hz hzM ht htM hL heven hlocal hvD hv)

end BenderSuzuki.ZD
