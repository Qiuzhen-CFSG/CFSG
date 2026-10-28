module
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.Ambient.Max4.GraphBound.GraphTable

/-!
# Separating graph signatures for the orbit kernel

Fixing five of the actual orbit letters restricts vertex zero to three
images. The other signatures force a four-point base once zero is fixed.
These are finite checks in the unchanged ATLAS Held graph, used for
GLS3 Table 5.3p; they assume no fixed-subgroup order bound.
-/

namespace Held.OuterInvolution.FixedStructure.OrbitCoverCertificate
open Held.NormalizerGraph Held.NormalizerGraph.CardBound
open Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.Ambient.Max4.GraphBound
set_option Elab.async false

set_option maxRecDepth 16384 in
public theorem separate0 : ∀ x : Fin 2058,
    baseSignature [129, 392, 1767, 1167, 389] x = baseSignature [129, 392, 1767, 1167, 389] 0 →
    x = 0 ∨ x = 815 ∨ x = 1356 := by
  simp only [baseSignature, adj_iff_fast]
  apply checked_forall
  decide +kernel

set_option maxRecDepth 16384 in
public theorem separate1 : ∀ x : Fin 2058,
    baseSignature [389, 1191, 0, 1767, 30] x = baseSignature [389, 1191, 0, 1767, 30] 1 →
    x = 1 := by
  simp only [baseSignature, adj_iff_fast]
  apply checked_forall
  decide +kernel

set_option maxRecDepth 16384 in
public theorem separate491 : ∀ x : Fin 2058,
    baseSignature [129, 389, 392, 1424, 0, 411] x = baseSignature [129, 389, 392, 1424, 0, 411] 491 →
    x = 491 := by
  simp only [baseSignature, adj_iff_fast]
  apply checked_forall
  decide +kernel

set_option maxRecDepth 16384 in
public theorem separate1185 : ∀ x : Fin 2058,
    baseSignature [65, 389, 1167, 1480, 0, 288] x = baseSignature [65, 389, 1167, 1480, 0, 288] 1185 →
    x = 1185 := by
  simp only [baseSignature, adj_iff_fast]
  apply checked_forall
  decide +kernel

set_option maxRecDepth 16384 in
public theorem separate1126 : ∀ x : Fin 2058,
    baseSignature [30, 65, 0, 946, 690] x = baseSignature [30, 65, 0, 946, 690] 1126 →
    x = 1126 := by
  simp only [baseSignature, adj_iff_fast]
  apply checked_forall
  decide +kernel

set_option maxRecDepth 16384 in
public theorem separate34 : ∀ x : Fin 2058,
    baseSignature [65, 1167, 690, 1191, 129] x = baseSignature [65, 1167, 690, 1191, 129] 34 →
    x = 34 := by
  simp only [baseSignature, adj_iff_fast]
  apply checked_forall
  decide +kernel

set_option maxRecDepth 16384 in
public theorem separate2 : ∀ x : Fin 2058,
    baseSignature [1671, 0, 491, 129, 392, 2042] x = baseSignature [1671, 0, 491, 129, 392, 2042] 2 →
    x = 2 := by
  simp only [baseSignature, adj_iff_fast]
  apply checked_forall
  decide +kernel

set_option maxRecDepth 16384 in
public theorem separate3 : ∀ x : Fin 2058,
    baseSignature [2, 1126, 34, 1767, 1185, 1469] x = baseSignature [2, 1126, 34, 1767, 1185, 1469] 3 →
    x = 3 := by
  simp only [baseSignature, adj_iff_fast]
  apply checked_forall
  decide +kernel

end Held.OuterInvolution.FixedStructure.OrbitCoverCertificate
