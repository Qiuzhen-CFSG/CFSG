module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.ActionConstruction.LocalSubgroups.XCensus.Action
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.ActionConstruction.LocalSubgroups.XCensus.Counting

/-!
# The full census of Janko's derived F-normalizer

The literal subgroup X = (N(F))' is a split extension of its actual elementary
sixteen F by A5. Its complement acts faithfully on F. The established
order-three fixed-point theorem and the order-five action theorem handle the
odd fibers. Each involution of A5 inverts a five-element, forcing its fixed
subgroup on F to have order four; its fiber therefore contains four
involutions and twelve elements of order four.

The resulting census is one identity, 75 involutions, 320 elements of order
three, 180 of order four and 384 of order five. All other orders have count
zero. The original local analysis already supplies every premise; the
additional ambient order and Sylow-three hypotheses are unnecessary here.

Source: Z. Janko, *A characterization of the Mathieu simple groups, I*,
J. Algebra 9 (1968), Section 8, Lemma 17, pp.16--17;
DOI 10.1016/0021-8693(68)90002-1.
-/

namespace Theory.GroupTheory.HeldM22A10.M22Identification.ActionConstruction.LocalSubgroups
open LocalModelDichotomy
universe u
variable {G : Type u} [Group G] [Finite G] (D : LocalData G)
  (k : TwistedModel ≃* D.centralizer)

/-- The complete source census of the literal derived F-normalizer. -/
public theorem X_count (L : LocalAnalysisData D k) (n : ℕ) :
    Nat.card {x : X D k // orderOf x = n} = localOrderCount 75 320 180 384 n := by
  obtain ⟨π, s, hs, hpow, hcard, hfixed, hfree⟩ := XCensus.exists_census_data D k L
  exact XCensus.split_census π s hs hpow hcard hfixed hfree n

end Theory.GroupTheory.HeldM22A10.M22Identification.ActionConstruction.LocalSubgroups
