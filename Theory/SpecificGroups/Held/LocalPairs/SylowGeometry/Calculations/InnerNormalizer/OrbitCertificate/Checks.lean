module

public import Theory.SpecificGroups.Held.LocalPairs.SylowGeometry.Calculations.InnerNormalizer.OrbitCertificate.Tables

/-!
# Finite checks for the Held representative orbit forest

Both coordinate round trips certify every component's cardinality without a
quadratic membership count. Generator invariance prevents components from
joining, and each nonroot has a depth-decreasing edge with the same component
number. `Actions` identifies these edge functions with the four actual words;
the parent certificate derives reachability by induction on depth.

Every assertion here is checked by kernel reduction against the candidate data.
Source: ATLAS HeG1-p2058B0, `Calculations/Source/words.json`, and
`InnerNormalizer/Source/orbits.json`; see `OrbitCertificate/Source/generate.py`.
-/

namespace Held.LocalPairs.SylowGeometry.Calculations.InnerNormalizer.OrbitCertificate

set_option maxRecDepth 16384 in
public theorem coordinates_valid : ∀ x : Fin 2058,
    position x < size (color x) ∧ vertex (color x) (position x) = x := by
  decide +kernel

set_option maxRecDepth 16384 in
public theorem enumeration_valid : ∀ c : Fin 24, ∀ i : Fin (size c),
    color (vertex c i.val) = c ∧ position (vertex c i.val) = i.val := by
  decide +kernel

set_option maxRecDepth 16384 in
public theorem size_eq_label : ∀ x : Fin 2058, size (color x) = orbitSizeLabel x := by
  decide +kernel

set_option maxRecDepth 16384 in
public theorem action_preserves_color : ∀ i : Fin 4, ∀ x : Fin 2058,
    color (action i x) = color x := by
  decide +kernel

set_option maxRecDepth 16384 in
public theorem tree_valid : ∀ x : Fin 2058, x = root (color x) ∨
    (depth (parent x) < depth x ∧ color (parent x) = color x ∧
      action (step x) (parent x) = x) := by
  decide +kernel

end Held.LocalPairs.SylowGeometry.Calculations.InnerNormalizer.OrbitCertificate
