module

public import Theory.SpecificGroups.Held.LocalPairs.SylowGeometry.ThreePrimeOvergroups.Data

/-!+# Eliminating the two exceptional regular orbit unions

The exploratory degree test on unions of the 24 specified fibers leaves the
pair and two sets of size 22. Here the two larger sets are identified with
their actual fibers, and kernel checks show that their common-neighbor
profiles are not constant: the basepoint has profile zero, whereas vertex
107 has profile eight. Thus neither set can be a transitive orbit of a
relation-preserving group.

The exhaustive degree test is still an explicit premise. This module only
certifies its exceptional cases, and passes the resulting orbit test to the
overgroup reduction. The constants refer to the original ATLAS HeG1-p2058B0
action and the relation in `Held.NormalizerGraph.GraphData`. Source context:
GLS3 Table 5.3p and the Held-case application on Aschbacher–Smith p.725.
-/

namespace Held.LocalPairs.SylowGeometry.ThreePrimeOvergroups

/-- The union of the fibers numbered 0, 1, and 6 (bit mask 67). -/
@[expose] public def candidate67 : Finset (Fin 2058) :=
  {11, 89, 107, 447, 508, 600, 615, 691, 909, 972, 1080, 1144, 1290, 1307,
    1313, 1335, 1337, 1477, 1523, 1714, 1953, 1967}

/-- The union of the fibers numbered 0, 2, and 6 (bit mask 69). -/
@[expose] public def candidate69 : Finset (Fin 2058) :=
  {107, 447, 508, 600, 615, 691, 754, 880, 972, 1080, 1144, 1290, 1292,
    1313, 1335, 1337, 1477, 1523, 1696, 1714, 1953, 1967}

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
/-- The published labeling has only 24 possible values. -/
public theorem orbitLabel_lt (x : Fin 2058) : orbitLabel x < 24 := by
  have h : ∀ y : Fin 2058, orbitLabel y < 24 := by decide +kernel
  exact h x

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
/-- Fiber zero is exactly the specified pair. -/
public theorem orbitLabel_eq_zero_iff (x : Fin 2058) :
    orbitLabel x = 0 ↔ x ∈ basePair := by
  have h : ∀ y : Fin 2058, orbitLabel y = 0 ↔ y ∈ basePair := by decide +kernel
  exact h x

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
/-- The first exceptional set really is the indicated union of fibers. -/
public theorem mem_candidate67 (x : Fin 2058) :
    x ∈ candidate67 ↔ orbitLabel x = 0 ∨ orbitLabel x = 1 ∨ orbitLabel x = 6 := by
  have h : ∀ y : Fin 2058,
      y ∈ candidate67 ↔ orbitLabel y = 0 ∨ orbitLabel y = 1 ∨ orbitLabel y = 6 := by
    decide +kernel
  exact h x

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
/-- The second exceptional set really is the indicated union of fibers. -/
public theorem mem_candidate69 (x : Fin 2058) :
    x ∈ candidate69 ↔ orbitLabel x = 0 ∨ orbitLabel x = 2 ∨ orbitLabel x = 6 := by
  have h : ∀ y : Fin 2058,
      y ∈ candidate69 ↔ orbitLabel y = 0 ∨ orbitLabel y = 2 ∨ orbitLabel y = 6 := by
    decide +kernel
  exact h x

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
private theorem candidate67_profile :
    profileCount candidate67 basepoint = 0 ∧ profileCount candidate67 107 = 8 := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
private theorem candidate69_profile :
    profileCount candidate69 basepoint = 0 ∧ profileCount candidate69 107 = 8 := by
  decide +kernel

/-- Constant common-neighbor profiles eliminate the two certified exceptions.
Only the exhaustive degree test remains a premise of this finite orbit test. -/
public theorem orbit_test_of_regular_candidates
    (hdegrees : ∀ U : Finset (Fin 2058), basepoint ∈ U →
      (∀ x ∈ U, ∀ y, orbitLabel x = orbitLabel y → y ∈ U) →
      ¬ 3 ∣ U.card →
      (∀ x ∈ U, neighborCount U x = neighborCount U basepoint) →
      U = basePair ∨ U = candidate67 ∨ U = candidate69)
    (U : Finset (Fin 2058)) (hbase : basepoint ∈ U)
    (hsat : ∀ x ∈ U, ∀ y, orbitLabel x = orbitLabel y → y ∈ U)
    (hthree : ¬ 3 ∣ U.card)
    (hregular : ∀ x ∈ U, neighborCount U x = neighborCount U basepoint)
    (hprofile : ∀ x ∈ U, profileCount U x = profileCount U basepoint) :
    U = basePair := by
  rcases hdegrees U hbase hsat hthree hregular with h | h | h
  · exact h
  · subst U
    have hp := hprofile 107 (by decide +kernel)
    have hc := candidate67_profile
    omega
  · subst U
    have hp := hprofile 107 (by decide +kernel)
    have hc := candidate69_profile
    omega

end Held.LocalPairs.SylowGeometry.ThreePrimeOvergroups
