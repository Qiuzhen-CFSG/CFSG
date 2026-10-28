module

public import Theory.Mathieu.M24.LocalGeometry.SylowNormalizer.Generators
public import Theory.Mathieu.M24.LocalGeometry.SylowNormalizer.Automorphisms.Profiles

/-!
# Automorphisms of the marked M₂₄ two-subgroup

Assuming the marked subgroup has order 1024, its Frattini quotient is the
binary group of rank four. Counts of elements killed by the second and fourth
powers distinguish five classes of cosets. A finite certificate proves that
every automorphism preserving these classes squares to the identity. The
Burnside Frattini-kernel theorem then makes the full automorphism group a
two-group.

The cardinality premise is intentional and is discharged separately by the
Sylow-normalizer assembly. Source context: Aschbacher–Smith, printed p.511;
GLS3, Table 5.3e.
-/

namespace Sporadic.Mathieu.M24LocalGeometry.SylowNormalizer
open AutomorphismData

public theorem candidate_automorphisms_isPGroup
    (hcard : Nat.card candidate = 1024) : IsPGroup 2 (MulAut candidate) := by
  exact Subgroup.isPGroup_mulAut_of_frattini_word_profile
    (k := 1) (IsPGroup.of_card (n := 10) hcard) (quotientEquiv hcard)
    powerTag powerTag_map binaryGen binaryWord binaryColor binaryWord_eval
    (profile_color hcard) binary_certificate

end Sporadic.Mathieu.M24LocalGeometry.SylowNormalizer
