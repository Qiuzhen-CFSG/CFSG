module

public import Theory.SpecificGroups.Held.TwoLocalCandidates.SylowContainment
public import Theory.SpecificGroups.Held.LocalPairs.SylowGeometry.Calculations
public import Theory.GroupTheory.SelfNormalizingSylowOvergroups

/-!
# Held candidate normalizers from the fixed Sylow calculation

Each literal max3/max4/max5 subgroup contains a certified conjugate of the
published four-word representative. If that representative is a two-group
and is self-normalizing in Held, the normalizer condition makes it Sylow.
The Frattini argument then makes each candidate self-normalizing.

The containments are unconditional permutation calculations. The two inputs
about the representative remain explicit here; this module does not yet
claim an unconditional candidate-normalizer theorem. No ambient order,
maximal-subgroup label, or abstract model identification is used.

Source: GLS3 Table 5.3p, the literal ATLAS max3/max4/max5 programs, and the
Frattini argument inside each candidate's ambient normalizer.
-/

namespace Held.TwoLocalCandidates
open Subgroup LocalPairs.SylowGeometry.Calculations

/-- The two remaining facts about the fixed representative imply the actual
ambient normalizer identities for all three unchanged candidates. -/
public theorem normalizer_eq_of_representative
    (hp : IsPGroup 2 representative)
    (hn : normalizer (representative : Set He) = representative)
    (i : Fin 3) : normalizer (subgroup i : Set He) = subgroup i := by
  obtain ⟨P, hP⟩ := exists_representative_sylow hp hn
  obtain ⟨g, hg⟩ := SylowContainment.exists_conjugate_representative_le i
  let T : Sylow 2 He := P.mapSurjective
    (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).surjective
  have hT : (T : Subgroup He) ≤ subgroup i := by
    change (P : Subgroup He).map (MulAut.conj g).toMonoidHom ≤ subgroup i
    rwa [hP]
  exact normalizer_eq_of_self_normalizing_sylow T
    (inner_self_normalizing_of_representative hp hn T) _ hT

end Held.TwoLocalCandidates
