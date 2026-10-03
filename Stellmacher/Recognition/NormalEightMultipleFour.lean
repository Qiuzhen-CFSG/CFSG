module

public import Stellmacher.Recognition.NormalEightMultipleFourDihedral
public import Stellmacher.Recognition.NormalEightMultipleFourSemidihedral

/-!
# Excluding distinct normal fours without a normal elementary eight

In a Sylow two-subgroup of a finite nonsolvable simple group, an elementary
subgroup of order at least eight and two distinct normal elementary fours
force a normal elementary subgroup of order at least eight.

Under the contrary assumption, the two fours generate a dihedral central
factor of order eight. Its centralizer has no normal elementary four, so the
binary Hall classification leaves cyclic, quaternion, dihedral and
semidihedral alternatives. Transfer excludes the cyclic case; in the other
cases a weakly closed involution contradicts simple-group involution fusion.
The reduction module and the two centralizer exclusion modules provide these
steps without a bound on arbitrary elementary subgroups.

Source: Janko–Thompson, Math. Z. 113 (1970), result 1.2, printed pp.385–386,
and its application on p.394.
-/

namespace Stellmacher.Recognition.NormalEightMultipleFour

open Subgroup

variable {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]

/-- Distinct normal elementary fours contradict the absence of a normal
elementary eight when the Sylow contains an elementary subgroup of order at
least eight. No N₂, noncommutativity, or center-cardinality hypothesis is needed. -/
public theorem false_of_distinct_normal_fours
    (hns : ¬ Group.IsSolvable G) (S : Sylow 2 G)
    (A : Subgroup S) [IsElementaryAbelian 2 A] (hA : 8 ≤ Nat.card A)
    (hno : ¬ ∃ U : Subgroup S, U.Normal ∧ IsElementaryAbelian 2 U ∧ 8 ≤ Nat.card U)
    (W F : Subgroup S) [W.Normal] [F.Normal]
    [IsElementaryAbelian 2 W] [IsElementaryAbelian 2 F]
    (hW : Nat.card W = 4) (hF : Nat.card F = 4) (hne : F ≠ W) : False := by
  rcases dihedral_or_semidihedral_centralizer_of_distinct_normal_fours
      hns S A hA hno W F hW hF hne with hdih | hsemi
  · obtain ⟨e⟩ := sup_dihedral_of_distinct_normal_fours_of_no_normal_eight
      hno W F hW hF hne.symm
    have hgen := sup_centralizer_eq_top_of_distinct_normal_fours_of_no_normal_eight
      S.isPGroup' hno W F hW hF hne.symm
    obtain ⟨m, ⟨f⟩⟩ := hdih
    exact false_of_dihedral_centralizer hns S A hA hno W F hW hF hne e hgen m f
  · exact false_of_semidihedral_centralizer_of_distinct_normal_fours
      hns S hno W F hW hF hne hsemi

end Stellmacher.Recognition.NormalEightMultipleFour
